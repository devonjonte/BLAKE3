"""Mutation testing against a list of the mutants known to survive.

    python3 tools/mutants/check.py [--since REV] [--write] [--map]

cargo-mutants plants likely bugs in the files tools/mutants/known-<arch>.txt
names (its `files:` line), one at a time, and runs the library's and the
integration tests on each. Every mutant that survives them must be in the
list with its reason, and every listed mutant must still survive. So the
check fails on a new survivor (a missing test, or a new equivalent mutant
to list with its reason), on a listed one now caught (the list is
stale), and on a listed one whose reason is still UNCLASSIFIED. A mutant
is named by its file, function, and change, without its line: the same
change at several places in one function counts once per place. It runs
in git worktrees of HEAD of its own (SHARDS at once), so the checkout is
never mutated. With --write, the list is rewritten from this run, each
new mutant's reason UNCLASSIFIED and the others' kept.

A mutant whose tests no test fails, but the clock stops (nextest's, or
cargo-mutants' backstop), has an outcome of its own: it timed out. That
is neither caught nor survived: the tests did not finish, which says
nothing of what they would have found (a loop that never ends, a wait
that never returns; or a test the load made slow). Time-outs have their
own list, tools/mutants/timeouts-<arch>.txt, in KNOWN's form, and are
checked against it the same way (NEW TIME-OUT, NO LONGER TIMES OUT).
Exit status: 0 both lists match; 1 a survivor differs from its list (or a
reason is missing); 2 only the time-outs differ (no verdict on those).

The tests run under cargo-nextest (.config/nextest.toml), each in its own
process, a test killed at 30 s as a hang; a mutant's tests stop at the
first that fails. Every run records each test's outcome and time on every
mutant, by its place (one change at several places is a mutant at each),
and on the unmutated tree (tmp/mutants-last/<run>/tests.tsv). With
--map, every test runs on every mutant (the `mutants-map` profile, for when
the tests change), and the run weighs the tests by cost: the cheapest set
of tests that still catches every caught mutant, the tests outside it
(each a big test whose catches cheaper ones make), and the mutants only an
expensive test catches (each a small test worth writing).

With --since REV, a change's check: the mutants in the lines the change
makes (git diff REV...HEAD, cargo-mutants --in-diff), and it fails on a new
survivor among them; a listed one now caught waits for a whole run. Either
way it fails while the list names a missing test ("OPEN: a missing test"):
that is work to do, not a survivor to keep. A change that alters a test (a
line taken away inside a #[test] function, comments aside) can lose the
catches of code it leaves alone: the mutants the latest map (a --map run of
an ancestor) records that test catching, the startup self-test's aside, run
again too. A change to other test code (a helper, a test module's or
tests/'s own items), or one with no such map, runs the whole check.
"""

import collections
import json
import os
import platform
import re
import shutil
import subprocess
import sys
import tempfile

ROOT = subprocess.run(["git", "rev-parse", "--show-toplevel"], capture_output=True, text=True, check=True).stdout.strip()
KNOWN = os.path.join(ROOT, "tools", "mutants", f"known-{platform.machine()}.txt")
# The mutants (by name, counted in places, as KNOWN) that no test catches but
# the clock stops: a loop that never ends, a wait that never returns. Their
# own outcome, never folded into caught or survived: a time-out says the
# tests did not finish, not what they would have found. Rows as KNOWN's, CPU
# conditions too.
TIMEOUTS = os.path.join(ROOT, "tools", "mutants", f"timeouts-{platform.machine()}.txt")
NAME = re.compile(r"^(\S+?):\d+:\d+: (.*)$")


def cpu_flags():
    """The CPU's feature flags as the OS names them (Linux: /proc/cpuinfo's
    flags or Features line; macOS: sysctl's hw.optional names set to 1)."""
    try:
        for line in open("/proc/cpuinfo"):
            if line.startswith(("flags", "Features")):
                return set(line.split(":", 1)[1].split())
    except OSError:
        pass
    if sys.platform == "darwin":
        out = subprocess.run(["sysctl", "hw.optional"], capture_output=True, text=True).stdout
        return {k.rsplit(".", 1)[-1] for k, _, v in (l.partition(": ") for l in out.splitlines()) if v.strip() == "1"}
    return set()


# A row whose survival depends on the CPU, not only the architecture: its
# reason begins "[cpu has FLAG ...] " or "[cpu lacks FLAG ...] " (flags as
# cpu_flags() names them), and the row applies only where that holds (an
# EPYC 9255, October 22: AVX-512's detection mutants survive where the CPU
# has it, and are caught on the i7, where it is absent, and the reverse).
CONDITION = re.compile(r"^\[cpu (has|lacks) ([^\]]+)\] ")
FLAGS = cpu_flags()


def applies(reason):
    m = CONDITION.match(reason)
    return m is None or all(f in FLAGS for f in m.group(2).split()) == (m.group(1) == "has")


def read_known(path=None, inactive=None):
    """A list's files and the rows that apply on this CPU; the rest are
    kept in `inactive` (INACTIVE for KNOWN), for --write. A list that does
    not exist yet (TIMEOUTS, on a new machine) has no rows."""
    path, inactive = (KNOWN, INACTIVE) if path is None else (path, inactive)
    files, known = [], {}
    if not os.path.exists(path):
        return files, known
    for line in open(path):
        line = line.rstrip("\n")
        if line.startswith("files:"):
            files = line.split()[1:]
        elif line and not line.startswith("#"):
            file, mutant, count, reason = line.split("\t")
            if applies(reason):
                name = f"{file}\t{mutant}"
                assert name not in known, f"{name}: two rows apply on this CPU"
                known[name] = (int(count), reason)
            else:
                inactive.append(line)
    return files, known


# The rows for other CPUs, as written (a name may have one row a CPU).
INACTIVE = []
INACTIVE_TIMEOUTS = []


MAP = "--map" in sys.argv


# Runs at once, each in its own worktree and build: on the VM (16 CPUs),
# a whole run took 47 minutes at 6 and about 60 at 3 (October 20).
SHARDS = 6
# cargo-mutants needs a limit on a mutant's tests (with --in-place it would
# otherwise take 300 s). The run's one clock is nextest's, a test's 30 s
# (.config/nextest.toml, profile mutants), which ends a hanging test first;
# this is a backstop far beyond it, and its firing stops the check as an
# error, never a verdict (it overlapped the 5 s clock, so a mutant's
# outcome hung on which ran out first: an EPYC 9255, October 22).
BACKSTOP = 3600
# Each process's memory, builds' and tests' alike: a mutant that allocates
# without end fails its test here, and leaves the machine's memory to the
# rest (one of 57 GB took the long proofs' memory). The limit is on data
# (heap and anonymous mappings, RLIMIT_DATA), which is what a runaway test
# takes; address space would count the linker's reservations too, and a
# 2.2 GiB address-space cap crashed rust-lld (i7, October 23). At most
# 8 GiB, and at most the machine's memory less 4 GiB shared among the
# shards, since SHARDS such mutants at once must fit: six at 8 GiB killed
# a 14 GiB machine twice (October 23), once the 30 s clock let a runaway
# test grow that far. A fresh build and the suite pass under 2.25 GB.
def memory_cap(shards):
    total = os.sysconf("SC_PAGE_SIZE") * os.sysconf("SC_PHYS_PAGES")
    return min(8 << 30, (total - (4 << 30)) // shards)


def cap_memory(shards=SHARDS):
    import resource
    cap = memory_cap(shards)
    resource.setrlimit(resource.RLIMIT_DATA, (cap, cap))


def scratch_dir():
    """tmp/ in the repository (git ignores it), made if absent."""
    path = os.path.join(ROOT, "tmp")
    os.makedirs(path, exist_ok=True)
    return path


def run(files, extra=(), shards=SHARDS, label="run"):
    """The mutants that survive the library's tests, by name, counted, and
    every mutant's outcome by function. Each shard's results are kept in
    tmp/mutants-last/<label>/ for a look afterwards."""
    # The public features on, so the code behind them is tested too (the
    # build variants, pure and the like, are their own builds).
    # A hang is nextest's to end (a test's 30 s); BACKSTOP only guards the run.
    args = ["cargo", "mutants", "--in-place", "--profile", "mutants", "--features", "serde,zeroize", "--timeout", str(BACKSTOP),
            "--test-tool", "nextest", *extra]
    for f in files:
        args += ["--file", f]
    runs, scratch = [], scratch_dir()
    for k in range(shards):
        # Under the repository's tmp/, on disk: /tmp is memory (tmpfs) on
        # some machines, and six worktrees' release builds there filled a
        # 14 GiB machine (i7, three times, October 22-23).
        tree = tempfile.mkdtemp(prefix="mutants-", dir=scratch)
        subprocess.run(["git", "-C", ROOT, "worktree", "add", "-q", "--detach", tree, "HEAD"], check=True)
        # The library's and the integration tests; the doc tests stay out
        # (each compiles a program of its own: minutes per mutant).
        # Its own build directory, named outright (a cargo config's
        # target-dir would otherwise give the shards one, and each would
        # test the others' builds).
        env = dict(os.environ, CARGO_TARGET_DIR=os.path.join(tree, "target"), NEXTEST_PROFILE="mutants-map" if MAP else "mutants")
        # Consecutive slices (cargo-mutants' default): a shard's mutants in one
        # file one after another rebuild less (round-robin evened the shards
        # and made each build 10% slower, the run no faster, October 21).
        shard = args + ["--shard", f"{k}/{shards}", "--output", os.path.join(tree, "mutants-result"), "--", "--lib", "--tests"]
        runs.append((tree, subprocess.Popen(shard, cwd=tree, env=env, preexec_fn=lambda: cap_memory(shards))))
    names = collections.Counter()
    timed = collections.Counter()  # the time-outs, by name: their own outcome
    functions = collections.defaultdict(list)  # (file, function) -> [(outcome, name)]
    rows = []  # (mutant name, function, test, outcome, ms); the unmutated tree's mutant name is UNMUTATED
    kept = os.path.join(ROOT, "tmp", "mutants-last", "map" if MAP and label == "run" else label)
    shutil.rmtree(kept, ignore_errors=True)
    for k, (tree, process) in enumerate(runs):
        # 0: every mutant caught; 2: some missed; 3: some timed out. Any
        # other status (a failing unmutated baseline) is no result.
        assert process.wait() in (0, 2, 3), f"cargo mutants failed ({process.returncode}) in {tree}"
        out = os.path.join(tree, "mutants-result", "mutants.out")
        # No mutants.out when there was nothing to test (a diff of no
        # mutants), so none of its files.
        missed = os.path.join(out, "missed.txt")
        for line in (open(missed).read().splitlines() if os.path.exists(missed) else []):
            m = NAME.match(line)
            assert m, f"a missed mutant cargo-mutants names unexpectedly: {line}"
            names[f"{m.group(1)}\t{m.group(2)}"] += 1
        outcomes = os.path.join(out, "outcomes.json")
        for outcome in (json.load(open(outcomes))["outcomes"] if os.path.exists(outcomes) else []):
            mutant = outcome["scenario"]
            log = os.path.join(out, outcome["log_path"]) if outcome.get("log_path") else None
            if not isinstance(mutant, dict):
                rows += [(UNMUTATED, "", *t) for t in read_tests(log)]  # the unmutated baseline
                continue
            mutant = mutant["Mutant"]
            function = (mutant.get("function") or {}).get("function_name", "")
            m = NAME.match(mutant["name"])
            name = f"{m.group(1)}\t{m.group(2)}"
            summary = outcome["summary"]
            if summary == "Timeout":
                # cargo-mutants' own limit: nextest's clock should have come
                # first. Still a time-out, never an error or a catch.
                print(f"BACKSTOP: the {BACKSTOP} s limit ended {mutant['name']}'s tests, not nextest's clock (.config/nextest.toml)")
                timed[name] += 1
            if summary in ("CaughtMutant", "MissedMutant", "Timeout"):
                # The mutant's place too: one name can be several places,
                # each caught (or not) by tests of its own.
                place = mutant["name"].split(": ", 1)[0].split(":", 1)[1]
                tests = read_tests(log)
                rows += [(f"{name}\t{place}", f"{mutant['file']} {function}", *t) for t in tests]
                failed = [o for _, o, _ in tests if o != "PASS"]
                if summary == "CaughtMutant" and failed and all(o == "TIMEOUT" for o in failed):
                    # No test failed: the clock stopped one. Timed out, not caught.
                    summary = "TimedOut"
                    timed[name] += 1
                    CLOCK_ONLY.add(f"{name}\t{place}")
            functions[(mutant["file"], function)].append((summary, name))
        if os.path.exists(out):
            shutil.copytree(out, os.path.join(kept, f"shard{k}"))
        subprocess.run(["git", "-C", ROOT, "worktree", "remove", "--force", tree], check=True)
        shutil.rmtree(tree, ignore_errors=True)
    if rows:
        os.makedirs(kept, exist_ok=True)
        with open(os.path.join(kept, "tests.tsv"), "w") as f:
            f.write(HEADER)
            f.writelines("\t".join(map(str, r)) + "\n" for r in rows)
        if MAP and label == "run":  # the confirming pass reruns a few mutants: its weights would be noise
            weigh(rows, os.path.join(kept, "tests.tsv"))
            head = subprocess.run(["git", "-C", ROOT, "rev-parse", "HEAD"], capture_output=True, text=True, check=True).stdout
            open(os.path.join(kept, "commit"), "w").write(head)
    return names, functions, timed


# The places that no test failed, but the clock stopped (listed by name in
# TIMEOUTS): a hang, or a test made slow by the mutant, or by the machine's
# load (a mutant compiled out of the build was stopped so once, at 5 s).
CLOCK_ONLY = set()

UNMUTATED = "(unmutated)\t\t"
HEADER = "# mutant (file, change, line:column)\tfunction\ttest\toutcome\tms\n"  # the record's format
SELF_TEST = "(the startup self-test)"
STATUS = re.compile(r"^\s+(PASS|FAIL|TIMEOUT|SIG[A-Z]+|ABORT)\s+\[\s*([\d.]+)s\]\s+(?:\(\s*\d+/\d+\)\s+)?(\S+)\s+(\S+)")


def read_tests(log):
    """Each test a cargo-nextest log ran: (test, outcome, ms). A failure
    whose output names the startup self-test is the self-test's catch,
    whichever test it ran in (a broken build fails it in every test)."""
    tests, last = [], None
    for line in open(log, errors="replace"):
        m = STATUS.match(line)
        if m:
            last = [f"{m.group(3)} {m.group(4)}", m.group(1), round(float(m.group(2)) * 1000)]
            tests.append(last)
        elif last and last[1] != "PASS" and "startup self-test failed" in line:
            last[0] = SELF_TEST
    return [tuple(t) for t in tests]


def weigh(rows, path):
    """The tests weighed by cost, from a run's record: the cheapest set of
    tests that catches every caught mutant (greedy, each step the test
    with the most uncaught mutants per millisecond), the tests outside it,
    and the mutants only an expensive test catches. Small tests are cheap,
    so they come first; a test outside the set is a reading (a test's
    worth goes beyond the mutants it catches: a contract, a shape no
    mutant models), and so is a mutant to give a small test."""
    cost = {}
    for name, _, test, outcome, ms in rows:
        if name == UNMUTATED and outcome == "PASS":
            cost[test] = min(cost.get(test, ms), ms)
    floor = max(1, min(cost.values(), default=1))
    cost[SELF_TEST] = floor  # it runs as every test process starts
    catches, function_of = collections.defaultdict(set), {}
    for name, function, test, outcome, _ in rows:
        if name != UNMUTATED and outcome != "PASS":
            catches[test].add(name)
            function_of[name] = function
    price = lambda t: max(floor, cost.get(t, 5000))
    uncovered, cover = set().union(*catches.values()) if catches else set(), []
    while uncovered:
        best = max(catches, key=lambda t: (len(catches[t] & uncovered) / price(t), -price(t), t))
        if not catches[best] & uncovered:
            break
        cover.append(best)
        uncovered -= catches[best]
    print(f"tests: {len(cost) - 1} take {sum(v for t, v in cost.items() if t != SELF_TEST)} ms unmutated; "
          f"{len(cover)} of them, {sum(price(t) for t in cover)} ms, catch every caught mutant "
          f"({len(function_of)} places; the startup self-test {len(catches[SELF_TEST])}) ({path})")
    for t in sorted(set(catches) - set(cover), key=lambda t: -price(t))[:10]:
        print(f"  outside the cheapest set: {price(t)} ms {t} ({len(catches[t])} catches, each made by cheaper tests)")
    cheapest = {n: min(price(t) for t in catches if n in catches[t]) for n in function_of}
    dear = collections.Counter(function_of[n] for n, ms in cheapest.items() if ms >= 100)
    for function, n in dear.most_common(10):
        print(f"  caught only by tests of 100 ms or more: {n} mutants in {function}")


def confirm(found, known, timed, tknown, differ=None):
    """`found` (survivors) and `timed` (time-outs) with every name whose
    count of either differs from its list run again, alone: a test that
    fails by chance (under load, say) neither hides a survivor nor fails
    the check, and a test the load made slow is not taken for a hang."""
    if differ is None:
        differ = sorted(k for k in set(found) | set(known) | set(timed) | set(tknown)
                        if found.get(k, 0) != known.get(k, (0, ""))[0] or timed.get(k, 0) != tknown.get(k, (0, ""))[0])
    if not differ:
        return found, timed
    patterns = [": " + re.escape(k.split("\t", 1)[1]) + "$" for k in differ]
    again, _, again_timed = run(sorted({k.split("\t", 1)[0] for k in differ}), [arg for p in patterns for arg in ("--re", p)], shards=1, label="confirm")
    confirmed, confirmed_timed = collections.Counter(found), collections.Counter(timed)
    for k in differ:
        confirmed[k], confirmed_timed[k] = again.get(k, 0), again_timed.get(k, 0)
    print(f"confirmed alone: {len(differ)} names whose count differed from a list")
    return +confirmed, +confirmed_timed


def changed_tests(since, head="HEAD"):
    """The tests a change alters, from the code before it: (names, sure).
    A line the change takes away (a changed line is one taken away and one
    added) inside a #[test] function names that test; one in other test code
    (a helper, a test module's or tests/'s own items) can weaken any test,
    so `sure` is False. Lines of the library's code are the change's own
    mutants' business."""
    diff = subprocess.run(["git", "-C", ROOT, "diff", "-U0", f"{since}...{head}", "--", "src", "tests"], capture_output=True, text=True, check=True).stdout
    names, sure, file, old = set(), True, None, []
    for line in diff.splitlines():
        if line.startswith("--- "):
            file = line[6:] if line.startswith("--- a/") else None
            old = subprocess.run(["git", "-C", ROOT, "show", f"{since}:{file}"], capture_output=True, text=True).stdout.splitlines() if file else []
        elif line.startswith("@@") and file:
            start, count = re.match(r"@@ -(\d+)(?:,(\d+))?", line).groups()
            for n in range(int(start), int(start) + int(count if count is not None else 1)):
                if not old[n - 1].strip() or old[n - 1].lstrip().startswith("//"):
                    continue  # a comment or a blank line weakens no test
                # src/test.rs is the library's test module (lib.rs: #[cfg(test)] mod test).
                kind, name = enclosing(old, n - 1, file.startswith("tests/") or file == "src/test.rs")
                if kind == "test":
                    names.add(name)
                elif kind == "helper":
                    sure = False
    return names, sure


def enclosing(lines, i, test_file):
    """What line `i` of a source file (rustfmt's layout) belongs to: ("test",
    its name) inside a #[test] function, ("helper", None) inside other test
    code (a #[cfg(test)] module, or anywhere in tests/), ("code", None)
    elsewhere."""
    depth = len(lines[i]) - len(lines[i].lstrip())
    fn = None
    for k in range(i, -1, -1):
        line = lines[k]
        indent = len(line) - len(line.lstrip())
        if not line.strip() or indent > depth or (indent == depth and k != i and not line.lstrip().startswith(("fn ", "pub fn ", "mod ", "pub(crate) mod ", "#["))):
            continue
        m = re.match(r"\s*(?:pub(?:\([a-z]+\))? )?(?:async )?fn (\w+)", line)
        if m and fn is None:
            attrs = []
            for a in range(k - 1, -1, -1):
                if lines[a].lstrip().startswith(("#[", "///", "//")):
                    attrs.append(lines[a])
                else:
                    break
            if any(re.search(r"#\[test\]", a) for a in attrs):
                return "test", m.group(1)
            fn = m.group(1)
        if re.match(r"\s*(?:pub(?:\([a-z]+\))? )?mod \w+ \{", line):
            above = lines[k - 1] if k else ""
            if "cfg(test" in above or "cfg(all(test" in above:
                return "helper", None
        depth = min(depth, indent)
    return ("helper" if test_file else "code"), None


MAP_DIR = os.path.join(ROOT, "tmp", "mutants-last", "map")


def caught_by(tests):
    """The mutants the latest map (a --map run of an ancestor of HEAD) records
    as caught by any of `tests` (by function name) at a place the startup
    self-test does not catch, by name (rerun at all its places); None when
    there is no such map."""
    record, commit = os.path.join(MAP_DIR, "tests.tsv"), os.path.join(MAP_DIR, "commit")
    if not (os.path.exists(record) and os.path.exists(commit)):
        return None
    if subprocess.run(["git", "-C", ROOT, "merge-base", "--is-ancestor", open(commit).read().strip(), "HEAD"]).returncode != 0:
        return None
    by, self_test = collections.defaultdict(set), set()
    lines = open(record)
    assert next(lines) == HEADER, f"{record} is in an older format: make a new map with --map"
    for line in lines:
        file, mutant, place, _function, test, outcome, _ms = line.rstrip("\n").split("\t")
        if file == "(unmutated)" or outcome == "PASS":
            continue
        name = (f"{file}\t{mutant}", place)
        if test == SELF_TEST:
            self_test.add(name)
        elif re.split(r"[ :]", test)[-1] in tests:
            by[name].add(test)
    return sorted({name for name, _ in set(by) - self_test})


def figure(functions, known):
    """How much of the library mutation testing covers, by function: every
    mutant caught, every survivor explained, or one still open."""
    caught = explained = 0
    open_ = []
    for (file, function), outcomes in sorted(functions.items()):
        reasons = [known.get(name, (0, "UNCLASSIFIED"))[1] for summary, name in outcomes if summary in ("MissedMutant", "TimedOut")]
        if not reasons:
            caught += 1
        elif all(not r.startswith(("OPEN", "UNCLASSIFIED")) for r in reasons):
            explained += 1
        else:
            open_.append(f"{file} {function}")
    print(f"functions: {len(functions)}: {caught} every mutant caught, {explained} every survivor explained, {len(open_)} open; "
          "the assembly kernels are the proofs'")
    return open_


def main():
    files, known = read_known()
    _, tknown = read_known(TIMEOUTS, INACTIVE_TIMEOUTS)
    # A test known to be missing is work to do now, not a survivor to keep:
    # the check fails while one is listed, whichever run this is.
    missing = sorted(k for k, (_, reason) in known.items() if reason.startswith("OPEN: a missing test"))
    for k in missing:
        print(f"MISSING TEST: {k}")
    if missing:
        sys.exit("mutants: the list names missing tests; write them first")
    since = sys.argv[sys.argv.index("--since") + 1] if "--since" in sys.argv else None
    extra = []  # the mutants the change's altered tests caught (the map's)
    if since is not None:
        diff = subprocess.run(["git", "-C", ROOT, "diff", f"{since}...HEAD", "--", *files], capture_output=True, text=True, check=True).stdout
        tests, sure = changed_tests(since)
        caught = caught_by(tests) if tests and sure else []
        if not sure:
            print(f"mutants: the change since {since} alters test code outside a test (a helper); the whole run")
            since = None
        elif caught is None:
            print(f"mutants: the change since {since} alters {len(tests)} test{'s' if len(tests) > 1 else ''} and no map of an ancestor holds their catches (check.py --map); the whole run")
            since = None
        else:
            extra = caught
            if tests:
                print(f"mutants: the change alters {len(tests)} test{'s' if len(tests) > 1 else ''}; the map's {len(extra)} mutant names they catch run again")
    if since is not None:
        if not diff and not extra:
            print(f"mutants: the change since {since} touches no mutated file and alters no test")
            return
        path = os.path.join(tempfile.mkdtemp(prefix="mutants-diff-", dir=scratch_dir()), "change.diff")
        with open(path, "w") as f:
            f.write(diff)
        # One shard: a change's mutants are few, and each shard builds anew.
        found, functions, timed = run(files, ["--in-diff", path], shards=1) if diff else (collections.Counter(), {}, collections.Counter())
        if extra:
            # The altered tests' catches, wherever they are: by name.
            again, more, again_timed = run(sorted({k.split("\t", 1)[0] for k in extra}), [arg for k in extra for arg in ("--re", ": " + re.escape(k.split("\t", 1)[1]) + "$")], label="tests")
            found, timed = found + again, timed + again_timed
            functions = {**more, **functions}
        # Only the names with more survivors than the list: the run holds
        # the change's lines alone, so a listed name's other places are
        # missing from it (a whole run sees those, and stale entries).
        found, timed = confirm(found, known, timed, tknown, sorted({k for k in found if found[k] > known.get(k, (0, ""))[0]}
                                                                   | {k for k in timed if timed[k] > tknown.get(k, (0, ""))[0]}))
        new = {k: n for k, n in found.items() if n > known.get(k, (0, ""))[0]}
        new_timed = {k: n for k, n in timed.items() if n > tknown.get(k, (0, ""))[0]}
        for k, n in sorted(new.items()):
            print(f"NEW SURVIVOR ({n - known.get(k, (0, ''))[0]}): {k}")
        for k, n in sorted(new_timed.items()):
            print(f"NEW TIME-OUT ({n - tknown.get(k, (0, ''))[0]}): {k}")
        print(f"mutants: the change since {since}: {sum(1 for f in functions.values() for _ in f)} mutants, "
              + ("no new survivor" if not new else f"{len(new)} names with a new survivor")
              + ("" if not new_timed else f", {len(new_timed)} names with a new time-out (no verdict on them)"))
        sys.exit(1 if new else 2 if new_timed else 0)
    found, functions, timed = run(files)
    found, timed = confirm(found, known, timed, tknown)
    figure(functions, {**{k: tknown.get(k, (n, "UNCLASSIFIED")) for k, n in timed.items()},
                       **{k: known.get(k, (n, "UNCLASSIFIED")) for k, n in found.items()}})
    if "--write" in sys.argv:
        header = [l.rstrip("\n") for l in open(KNOWN) if l.startswith("#") or l.startswith("files:")]
        # The rows for other CPUs stay as they were: this run cannot see them.
        rows = sorted([f"{k}\t{n}\t{known.get(k, (0, 'UNCLASSIFIED'))[1]}" for k, n in found.items()] + INACTIVE)
        open(KNOWN, "w").write("\n".join(header + rows) + "\n")
        print(f"{KNOWN}: {sum(found.values())} survivors, {sum(1 for k in found if k not in known)} names new")
        theader = [l.rstrip("\n") for l in open(TIMEOUTS) if l.startswith("#")] if os.path.exists(TIMEOUTS) else \
            [f"# The mutants that time out on {platform.machine()}: no test fails, the clock stops one (tools/mutants/check.py, TIMEOUTS).",
             "# A line: file <TAB> mutant (function and change) <TAB> places <TAB> reason."]
        trows = sorted([f"{k}\t{n}\t{tknown.get(k, (0, 'UNCLASSIFIED'))[1]}" for k, n in timed.items()] + INACTIVE_TIMEOUTS)
        open(TIMEOUTS, "w").write("\n".join(theader + trows) + "\n")
        print(f"{TIMEOUTS}: {sum(timed.values())} time-outs, {sum(1 for k in timed if k not in tknown)} names new")
        return
    unexplained = sorted(k for k, (_, reason) in {**tknown, **known}.items() if reason == "UNCLASSIFIED")
    for k in unexplained:
        print(f"NO REASON: {k}")
    new = {k: n for k, n in found.items() if n > known.get(k, (0, ""))[0]}
    # An OPEN pool entry is caught or not as the run's scheduling falls
    # (the list says why): its count is the most that survive, and a run
    # that catches more of them is no change to the list.
    stale = {k: c for k, (c, reason) in known.items() if found.get(k, 0) < c and not (k.startswith("src/lanes.rs") and reason.startswith("OPEN: the pool's scheduling"))}
    for k, n in sorted(new.items()):
        print(f"NEW SURVIVOR ({n - known.get(k, (0, ''))[0]}): {k}")
    for k, c in sorted(stale.items()):
        print(f"{'NOW TIMES OUT' if timed.get(k) else 'NOW CAUGHT'} ({c - found.get(k, 0)}): {k}")
    # The time-outs against their list, alike (an OPEN pool row's count is
    # the most that time out, as for survivors).
    new_timed = {k: n for k, n in timed.items() if n > tknown.get(k, (0, ""))[0]}
    stale_timed = {k: c for k, (c, reason) in tknown.items() if timed.get(k, 0) < c and not (k.startswith("src/lanes.rs") and reason.startswith("OPEN: the pool's scheduling"))}
    for k, n in sorted(new_timed.items()):
        print(f"NEW TIME-OUT ({n - tknown.get(k, (0, ''))[0]}): {k}")
    for k, c in sorted(stale_timed.items()):
        print(f"NO LONGER TIMES OUT ({c - timed.get(k, 0)}): {k}")
    for k in sorted(CLOCK_ONLY):
        print(f"TIMED OUT (place): {k}")
    ok = not new and not stale and not unexplained
    ok_timed = not new_timed and not stale_timed
    print(f"mutants: {sum(found.values())} survive, each known and explained" if ok else "mutants: the list and this run differ, or a listed mutant has no reason")
    print(f"mutants: {sum(timed.values())} time out, each known ({os.path.basename(TIMEOUTS)})" if ok_timed
          else f"mutants: the time-outs differ from {os.path.basename(TIMEOUTS)} (no verdict on those mutants)")
    # One status an outcome: 1 a survivor or list wrong, 2 only time-outs differ, 0 both as listed.
    sys.exit(0 if ok and ok_timed else 1 if not ok else 2)


if __name__ == "__main__":
    main()
