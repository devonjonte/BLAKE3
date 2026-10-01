"""The one reader of bench-hashes' samples files (`bench-hashes.samples.tsv`)
for every Python tool: perf_regress, ab.py, losses.py, bench-hashes'
compare-runs.py and check-report.py, and every scratch analysis. Import
it; write no parser of your own.

It reads what the benchmark concluded, and recomputes nothing: whether
other programs kept the machine busy is the Rust `clocks::load` rule's
verdict, which the file carries on its `# load:` line.

    run = samples.read(path)
    run.cells[(contender, scenario, use_case, point)]  # [Fraction ns per unit], in the order taken
    run.starts[key]   # when each sample started, ms
    run.measured[key] # [(raw ns, raw units)], before Fraction reduces them
    run.load_observed # clocks recorded at least one load window
    run.busy          # other programs kept a CPU busy in some window
    run.load, run.power, run.meta["rounds"], run.order (contenders in order)
    run.samples_in_busy_windows(key)  # how many of the cell's samples started in a busy window

It reads the current format alone, `samples v4` (each sample as
measured, `ns/units`, its start in ms, the load windows), and stops on
any other: a file in an older format is read with the tools of its own
commit (AGENTS.md, "Contracts change everywhere at once").
"""
from fractions import Fraction
from pathlib import Path

BUSY = 1000  # milli-CPUs; the file's windows are judged by clocks::load's BUSY_MILLI_CPUS


class Run:
    def __init__(self):
        self.version = None
        self.meta = {}
        self.cells = {}
        self.measured = {}
        self.units = {}
        self.starts = {}
        self.order = []
        # (start ms, end ms, other milli-CPUs, steal milli-CPUs).
        self.windows = []

    @property
    def power(self):
        return self.meta["power"]

    @property
    def load(self):
        """The benchmark's own line: "quiet: ...", "busy: ...", or "not
        measured on this platform"."""
        return self.meta["load"]

    @property
    def load_observed(self):
        """Whether clocks recorded any load window; empty includes short runs
        on supported platforms as well as unavailable counters."""
        return bool(self.windows)

    @property
    def busy(self):
        return self.load.startswith("busy")

    def samples_in_busy_windows(self, key):
        """How many of the cell's samples started in a busy window."""
        busy = [(a, b) for a, b, other, steal in self.windows if max(other, steal) >= BUSY]
        return sum(any(a <= t < b for a, b in busy) for t in self.starts[key])


def read(source):
    """A Run from a samples file's path or its text."""
    text = source if isinstance(source, str) and "\n" in source else Path(source).read_text()
    run, header = Run(), None
    for line in text.splitlines():
        if run.version is None:
            assert line == "# bench-hashes samples v4", f"a samples v4 file begins with its version line, not {line!r}"
            run.version = 4
            continue
        if line.startswith("# load windows ("):
            listed = line.split("): ", 1)[1]
            for window in filter(None, listed.split(",")):
                span, other, steal = window.split(":")
                start, end = span.split("-")
                run.windows.append((int(start), int(end), int(other), int(steal)))
            continue
        if line.startswith("# "):
            key, sep, value = line[2:].partition(": ")
            if sep and key not in run.meta:
                run.meta[key] = value
            continue
        if not line:
            continue
        fields = line.split("\t")
        if header is None:
            header = fields
            assert header == ["contender", "scenario", "use_case", "point", "unit", "ns/units", "start ms"], header
            continue
        contender, scenario, use_case, point, unit, values, starts = fields
        key = (contender, scenario, use_case, point)
        assert key not in run.cells, f"one row per sampled cell; duplicate {key}"
        measured = [tuple(map(int, v.split("/"))) for v in values.split(",")]
        assert all(len(v) == 2 and v[0] >= 0 and v[1] > 0 for v in measured), f"nonnegative ns over positive units for {key}"
        run.measured[key] = measured
        run.cells[key] = [Fraction(ns, units) for ns, units in measured]
        run.units[key] = unit
        run.starts[key] = [int(t) for t in starts.split(",")]
        assert len(run.starts[key]) == len(run.cells[key]), f"a start for every sample of {key}"
        if contender not in run.order:
            run.order.append(contender)
    assert header is not None and "load" in run.meta and "power" in run.meta, "a samples file has its load and power lines and a header row"
    return run


if __name__ == "__main__":
    # Self-check against a small file, and an older one refused.
    run = read("# bench-hashes samples v4\n# power: mains power\n"
               "# load: busy: other programs kept 0.80 CPUs busy on average\n"
               "# load windows (start ms-end ms:other milli-CPUs:steal milli-CPUs): 0-1000:1200:0,1000-2000:10:0\n"
               "contender\tscenario\tuse_case\tpoint\tunit\tns/units\tstart ms\n"
               "a\tsolo\tOneMessage\t64 B\tB\t3/2,5/1\t999,1000\n")
    key = ("a", "solo", "OneMessage", "64 B")
    assert run.cells[key] == [Fraction(3, 2), Fraction(5)] and run.busy and run.power == "mains power"
    assert run.samples_in_busy_windows(key) == 1 and run.order == ["a"]
    try:
        read("# bench-hashes samples v3\ncontender\tscenario\tuse_case\tpoint\tunit\tns/units\n")
        raise SystemExit("samples.py: an older format was accepted")
    except AssertionError:
        pass
    print("samples.py: self-check passed")
