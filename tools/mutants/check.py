"""Mutation testing against a list of the mutants known to survive.

    pypy3 tools/mutants/check.py [--write]

cargo-mutants plants likely bugs in the files tools/mutants/known-<arch>.txt
names (its `files:` line), one at a time, and runs the library's and the
integration tests on each. Every mutant that survives them must be in the list, with its
reason; every listed mutant must still survive. So the check fails on a
new survivor (a missing test, or a new equivalent mutant to list with its
reason) and on a listed one now caught (the list is stale). A mutant is
named by its file, function, and change, without its line: the same
change at several places in one function counts once per place. It runs
in git worktrees of HEAD of its own (SHARDS at once), so the checkout is
never mutated.
With --write, the list is rewritten from this run, each new mutant's
reason UNCLASSIFIED and the others' kept.
"""

import collections
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


SHARDS = 3  # runs at once, each in its own worktree and build
# Each process's address space, builds' and tests' alike: a mutant that
# allocates without end fails its test here, and leaves the machine's
# memory to the rest (one of 57 GB took the long proofs' memory).
MEMORY = 8 << 30


def cap_memory():
    import resource
    resource.setrlimit(resource.RLIMIT_AS, (MEMORY, MEMORY))


def survivors(files):
    """The mutants that survive the library's tests, by name, counted."""
    # The public features on, so the code behind them is tested too (the
    # build variants, pure, no_sme2, and the like, are their own builds).
    args = ["cargo", "mutants", "--in-place", "--profile", "mutants", "--features", "mmap,serde,zeroize,traits-preview", "--timeout", "30"]
    for f in files:
        args += ["--file", f]
    runs = []
    for k in range(SHARDS):
        tree = tempfile.mkdtemp(prefix="mutants-", dir="/tmp")
        subprocess.run(["git", "-C", ROOT, "worktree", "add", "-q", "--detach", tree, "HEAD"], check=True)
        # The library's and the integration tests; the doc tests stay out
        # (each compiles a program of its own: minutes per mutant).
        # Its own build directory, named outright (a cargo config's
        # target-dir would otherwise give the shards one, and each would
        # test the others' builds).
        # Temporary files on /tmp too: a full root filesystem failed the
        # tests that write them, and counted their mutants caught.
        env = dict(os.environ, CARGO_TARGET_DIR=os.path.join(tree, "target"), TMPDIR="/tmp")
        shard = args + ["--shard", f"{k}/{SHARDS}", "--output", os.path.join(tree, "mutants-result"), "--", "--lib", "--tests"]
        runs.append((tree, subprocess.Popen(shard, cwd=tree, env=env, preexec_fn=cap_memory)))
    names = collections.Counter()
    for tree, run in runs:
        # 0: every mutant caught; 2: some missed; 3: some timed out. Any
        # other status (a failing unmutated baseline) is no result.
        assert run.wait() in (0, 2, 3), f"cargo mutants failed ({run.returncode}) in {tree}"
        for line in open(os.path.join(tree, "mutants-result", "mutants.out", "missed.txt")).read().splitlines():
            m = NAME.match(line)
            assert m, f"a missed mutant cargo-mutants names unexpectedly: {line}"
            names[f"{m.group(1)}\t{m.group(2)}"] += 1
        subprocess.run(["git", "-C", ROOT, "worktree", "remove", "--force", tree], check=True)
        shutil.rmtree(tree, ignore_errors=True)
    return names


def main():
    files, known = read_known()
    found = survivors(files)
    if "--write" in sys.argv:
        header = [l.rstrip("\n") for l in open(KNOWN) if l.startswith("#") or l.startswith("files:")]
        rows = [f"{k}\t{n}\t{known.get(k, (0, 'UNCLASSIFIED'))[1]}" for k, n in sorted(found.items())]
        open(KNOWN, "w").write("\n".join(header + rows) + "\n")
        print(f"{KNOWN}: {sum(found.values())} survivors, {sum(1 for k in found if k not in known)} names new")
        return
    new = {k: n for k, n in found.items() if n > known.get(k, (0, ""))[0]}
    stale = {k: c for k, (c, _) in known.items() if found.get(k, 0) < c}
    for k, n in sorted(new.items()):
        print(f"NEW SURVIVOR ({n - known.get(k, (0, ''))[0]}): {k}")
    for k, c in sorted(stale.items()):
        print(f"NOW CAUGHT ({c - found.get(k, 0)}): {k}")
    print(f"mutants: {sum(found.values())} survive, all known" if not new and not stale else "mutants: the list and this run differ")
    sys.exit(1 if new or stale else 0)


if __name__ == "__main__":
    main()
