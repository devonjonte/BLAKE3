"""Mutation testing against a list of the mutants known to survive.

    pypy3 tools/mutants/check.py [--since REV] [--write]

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

The tests run under cargo-nextest (its `mutants` profile, .config/nextest.toml:
each test in its own process, every test on every mutant, a test killed at
5 s as a hang). Every run records each test's outcome and time on every
mutant and on the unmutated tree (tmp/mutants-last/<run>/tests.tsv), and
weighs the tests by cost: the cheapest set of tests that still catches
every caught mutant, the tests outside it (each a big test whose catches
cheaper ones make), and the mutants only an expensive test catches (each a
small test worth writing).

With --since REV, a change's check: only the mutants in the lines the
change makes (git diff REV...HEAD, cargo-mutants --in-diff), and it fails
on a new survivor among them; a listed one now caught waits for a whole
run. Either way it fails while the list names a missing test ("OPEN: a
missing test"): that is work to do, not a survivor to keep. A change that removes or alters test code (a line of src/test.rs or
tests/, or one with an assertion or a test's name) can weaken the tests of
code it leaves alone, which only a whole run sees: then the whole run
happens instead, by itself.
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
NAME = re.compile(r"^(\S+?):\d+:\d+: (.*)$")


def read_known():
    files, known = [], {}
    for line in open(KNOWN):
        line = line.rstrip("\n")
        if line.startswith("files:"):
            files = line.split()[1:]
        elif line and not line.startswith("#"):
            file, mutant, count, reason = line.split("\t")
            known[f"{file}\t{mutant}"] = (int(count), reason)
    return files, known


HANGS = os.path.join(ROOT, "tools", "mutants", "hangs.txt")


def read_hangs():
    """The mutants skipped because they hang the tests (tools/mutants/hangs.txt), by name."""
    names = set()
    for line in open(HANGS):
        line = line.rstrip("\n")
        if line and not line.startswith("#"):
            file, mutant, _test, _why = line.split("\t")
            names.add(f"{file}\t{mutant}")
    return names


# Runs at once, each in its own worktree and build: on the VM (16 CPUs),
# a whole run took 47 minutes at 6 and about 60 at 3 (October 20).
SHARDS = 6
# The seconds a mutant's tests may take: the unmutated tests take 1.5 s on
# the VM and 2 s on an i7-12700K (October 20), a caught mutant's at most
# 2.5 s on the VM, so a mutant still running at 30 s hangs (Zooko: a
# hang's cost is paid on every hang, a slow test's misclassification once).
TIMEOUT = 30
# Each process's address space, builds' and tests' alike: a mutant that
# allocates without end fails its test here, and leaves the machine's
# memory to the rest (one of 57 GB took the long proofs' memory).
MEMORY = 8 << 30


def cap_memory():
    import resource
    resource.setrlimit(resource.RLIMIT_AS, (MEMORY, MEMORY))


def run(files, extra=(), shards=SHARDS, label="run"):
    """The mutants that survive the library's tests, by name, counted, and
    every mutant's outcome by function. Each shard's results are kept in
    tmp/mutants-last/<label>/ for a look afterwards."""
    # The public features on, so the code behind them is tested too (the
    # build variants, pure and the like, are their own builds).
    # A mutant whose tests outlast TIMEOUT is a hang, which the check counts
    # as caught.
    args = ["cargo", "mutants", "--in-place", "--profile", "mutants", "--features", "serde,zeroize", "--timeout", str(TIMEOUT),
            "--test-tool", "nextest", *[arg for name in sorted(read_hangs()) for arg in ("--exclude-re", re.escape(name.split("\t", 1)[1]))], *extra]
    for f in files:
        args += ["--file", f]
    runs = []
    for k in range(shards):
        tree = tempfile.mkdtemp(prefix="mutants-", dir="/tmp")
        subprocess.run(["git", "-C", ROOT, "worktree", "add", "-q", "--detach", tree, "HEAD"], check=True)
        # The library's and the integration tests; the doc tests stay out
        # (each compiles a program of its own: minutes per mutant).
        # Its own build directory, named outright (a cargo config's
        # target-dir would otherwise give the shards one, and each would
        # test the others' builds).
        env = dict(os.environ, CARGO_TARGET_DIR=os.path.join(tree, "target"), NEXTEST_PROFILE="mutants")
        shard = args + ["--shard", f"{k}/{shards}", "--output", os.path.join(tree, "mutants-result"), "--", "--lib", "--tests"]
        runs.append((tree, subprocess.Popen(shard, cwd=tree, env=env, preexec_fn=cap_memory)))
    names = collections.Counter()
    functions = collections.defaultdict(list)  # (file, function) -> [(outcome, name)]
    rows = []  # (mutant name, function, test, outcome, ms); the unmutated tree's mutant name is UNMUTATED
    kept = os.path.join(ROOT, "tmp", "mutants-last", label)
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
            functions[(mutant["file"], function)].append((outcome["summary"], name))
            if outcome["summary"] in ("CaughtMutant", "MissedMutant", "Timeout"):
                rows += [(name, f"{mutant['file']} {function}", *t) for t in read_tests(log)]
        if os.path.exists(out):
            shutil.copytree(out, os.path.join(kept, f"shard{k}"))
        subprocess.run(["git", "-C", ROOT, "worktree", "remove", "--force", tree], check=True)
        shutil.rmtree(tree, ignore_errors=True)
    if rows:
        os.makedirs(kept, exist_ok=True)
        with open(os.path.join(kept, "tests.tsv"), "w") as f:
            f.write("# mutant (file, change)\tfunction\ttest\toutcome\tms\n")
            f.writelines("\t".join(map(str, r)) + "\n" for r in rows)
        if label == "run":  # the confirming pass reruns a few mutants: its weights would be noise
            weigh(rows, os.path.join(kept, "tests.tsv"))
    return names, functions


UNMUTATED = "(unmutated)\t"
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
          f"({len(function_of)}; the startup self-test {len(catches[SELF_TEST])}) ({path})")
    for t in sorted(set(catches) - set(cover), key=lambda t: -price(t))[:10]:
        print(f"  outside the cheapest set: {price(t)} ms {t} ({len(catches[t])} catches, each made by cheaper tests)")
    cheapest = {n: min(price(t) for t in catches if n in catches[t]) for n in function_of}
    dear = collections.Counter(function_of[n] for n, ms in cheapest.items() if ms >= 100)
    for function, n in dear.most_common(10):
        print(f"  caught only by tests of 100 ms or more: {n} mutants in {function}")


def confirm(found, known, differ=None):
    """`found` with every name whose count differs from the list's run
    again, alone: a test that fails by chance (under load, say) neither
    hides a survivor nor fails the check."""
    if differ is None:
        differ = sorted(k for k in set(found) | set(known) if found.get(k, 0) != known.get(k, (0, ""))[0])
    if not differ:
        return found
    patterns = [": " + re.escape(k.split("\t", 1)[1]) + "$" for k in differ]
    again, _ = run(sorted({k.split("\t", 1)[0] for k in differ}), [arg for p in patterns for arg in ("--re", p)], shards=1, label="confirm")
    confirmed = collections.Counter(found)
    for k in differ:
        confirmed[k] = again.get(k, 0)
    print(f"confirmed alone: {len(differ)} names whose count differed from the list")
    return +confirmed


def weakens_tests(diff):
    """Whether a diff removes or alters test code: a line it takes away (a
    changed line is one taken away and one added) in src/test.rs or
    tests/, or one holding an assertion or a test."""
    file = ""
    for line in diff.splitlines():
        if line.startswith("--- "):
            file = line[6:] if line.startswith("--- a/") else ""
        elif line.startswith("-") and not line.startswith("---"):
            if file == "src/test.rs" or file.startswith("tests/") or re.search(r"assert|#\[test\]|fn test_", line):
                return True
    return False


def figure(functions, known):
    """How much of the library mutation testing covers, by function: every
    mutant caught, every survivor explained, or one still open."""
    caught = explained = 0
    open_ = []
    for (file, function), outcomes in sorted(functions.items()):
        reasons = [known.get(name, (0, "UNCLASSIFIED"))[1] for summary, name in outcomes if summary == "MissedMutant"]
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
    # A skipped mutant cannot be seen to survive: a name on both lists would
    # read as caught, run after run.
    both = sorted(set(known) & read_hangs())
    for k in both:
        print(f"ON BOTH LISTS: {k}")
    if both:
        sys.exit(f"mutants: {len(both)} names are both skipped (hangs.txt) and listed as surviving ({os.path.basename(KNOWN)}); keep each on one")
    # A test known to be missing is work to do now, not a survivor to keep:
    # the check fails while one is listed, whichever run this is.
    missing = sorted(k for k, (_, reason) in known.items() if reason.startswith("OPEN: a missing test"))
    for k in missing:
        print(f"MISSING TEST: {k}")
    if missing:
        sys.exit("mutants: the list names missing tests; write them first")
    since = sys.argv[sys.argv.index("--since") + 1] if "--since" in sys.argv else None
    if since is not None:
        diff = subprocess.run(["git", "-C", ROOT, "diff", f"{since}...HEAD", "--", *files], capture_output=True, text=True, check=True).stdout
        if weakens_tests(diff):
            print(f"mutants: the change since {since} removes or alters test code; the whole run")
            since = None
    if since is not None:
        if not diff:
            print(f"mutants: the change since {since} touches no mutated file")
            return
        path = os.path.join(tempfile.mkdtemp(prefix="mutants-diff-", dir="/tmp"), "change.diff")
        with open(path, "w") as f:
            f.write(diff)
        # One shard: a change's mutants are few, and each shard builds anew.
        found, functions = run(files, ["--in-diff", path], shards=1)
        # Only the names with more survivors than the list: the run holds
        # the change's lines alone, so a listed name's other places are
        # missing from it (a whole run sees those, and stale entries).
        found = confirm(found, known, sorted(k for k in found if found[k] > known.get(k, (0, ""))[0]))
        new = {k: n for k, n in found.items() if n > known.get(k, (0, ""))[0]}
        for k, n in sorted(new.items()):
            print(f"NEW SURVIVOR ({n - known.get(k, (0, ''))[0]}): {k}")
        print(f"mutants: the change since {since}: {sum(1 for f in functions.values() for _ in f)} mutants, "
              + ("no new survivor" if not new else f"{len(new)} names with a new survivor"))
        sys.exit(1 if new else 0)
    found, functions = run(files)
    found = confirm(found, known)
    figure(functions, {k: known.get(k, (n, "UNCLASSIFIED")) for k, n in found.items()})
    if "--write" in sys.argv:
        header = [l.rstrip("\n") for l in open(KNOWN) if l.startswith("#") or l.startswith("files:")]
        rows = [f"{k}\t{n}\t{known.get(k, (0, 'UNCLASSIFIED'))[1]}" for k, n in sorted(found.items())]
        open(KNOWN, "w").write("\n".join(header + rows) + "\n")
        print(f"{KNOWN}: {sum(found.values())} survivors, {sum(1 for k in found if k not in known)} names new")
        return
    unexplained = sorted(k for k, (_, reason) in known.items() if reason == "UNCLASSIFIED")
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
        print(f"NOW CAUGHT ({c - found.get(k, 0)}): {k}")
    ok = not new and not stale and not unexplained
    print(f"mutants: {sum(found.values())} survive, each known and explained" if ok else "mutants: the list and this run differ, or a listed mutant has no reason")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
