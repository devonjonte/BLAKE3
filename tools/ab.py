#!/usr/bin/env python3
"""An A/B of runner benchmark jobs, speed with speed (tools/speeds.py).

    pypy3 tools/ab.py OLD NEW NEW OLD [--contender blake3-servil-mt] [--use-case Continuous]

Each argument is a runner job number (runner/results/NNN-*); the jobs run
old, new, new, old. For every cell of the contender, the line gives each
side's speeds (median and share of the pooled samples) and new/old of the
fast and of the slow speed. Beside it, OLD against OLD and NEW against NEW
(the first job of a side against its second): the same code's spread, so
a change reads beside what repetition alone moves. A cell whose share of
the slow speed swings between repetitions of one side cannot be judged
by its median: read the shares.
"""
import argparse
import glob
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import speeds  # noqa: E402
import samples  # noqa: E402


def load(job):
    found = glob.glob(f"runner/results/{job}-*/benchmark-results/*/bench-hashes.samples.tsv")
    assert len(found) == 1, f"job {job}: expected one samples file, found {found}"
    run = samples.read(found[0])
    if run.busy:
        print(f"ab: job {job} ran while other programs kept the machine busy: {run.load}")
    return run.cells


def main():
    p = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    p.add_argument("jobs", nargs=4)
    p.add_argument("--contender", default="blake3-servil-mt")
    p.add_argument("--use-case", default="", help="only use cases starting with this")
    args = p.parse_args()
    o1, n1, n2, o2 = (load(j) for j in args.jobs)
    for key in o1:
        contender, scenario, use_case, point = key
        if contender != args.contender or not use_case.startswith(args.use_case) or key not in n1:
            continue
        c = speeds.compare(o1[key] + o2[key], n1[key] + n2[key])
        same_old = speeds.compare(o1[key], o2[key])
        same_new = speeds.compare(n1[key], n2[key])
        print(f"{scenario:6} {use_case:20} {point:>8}: {speeds.describe_comparison(c)}")
        if c["two_speeds"] or same_old["two_speeds"] or same_new["two_speeds"]:
            print(f"{'':39} old vs old {speeds.describe_comparison(same_old)}")
            print(f"{'':39} new vs new {speeds.describe_comparison(same_new)}")


if __name__ == "__main__":
    main()
