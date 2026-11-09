"""A short run of check.py, start to finish, for a change to it (CONTRIBUTING:
a tool that runs for hours lands after one on each kind of machine): two
shards on one small file; the next run's start-of-run cleanup, which keeps
the shards' worktrees and removes any other leftover; and a second run on
the kept worktrees, with the same outcome. About a minute and a half.

    python3 tools/mutants/smoke.py
"""
import os
import subprocess
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
os.chdir(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
import check

def trees():
    """The worktrees under check.py's directory, by name."""
    listed = subprocess.run(["git", "worktree", "list", "--porcelain"], capture_output=True, text=True, check=True).stdout
    home = os.path.realpath(check.WORKTREES) + os.sep
    return sorted(os.path.basename(t) for t in (l.removeprefix("worktree ") for l in listed.splitlines() if l.startswith("worktree "))
                  if os.path.realpath(t).startswith(home))


check.remove_leftovers()
found, functions, timed = check.run(["src/io.rs"], shards=2, label="smoke")
print("found", dict(found), "timed", dict(timed), "functions", len(functions))
assert {"smoke-0", "smoke-1"} <= set(trees()), f"the run keeps its two shards' worktrees for the next: {trees()}"
# A leftover no shard reuses (a crash's, a stop by hand's) goes at the next start; the shards' stay.
subprocess.run(["git", "worktree", "add", "-q", "--detach", os.path.join(check.WORKTREES, "leftover"), "HEAD"], check=True)
check.remove_leftovers()
assert "leftover" not in trees() and {"smoke-0", "smoke-1"} <= set(trees()), f"the next start removes the leftover alone: {trees()}"
# The next run reuses them, with the same outcome.
before = trees()
again, _, _ = check.run(["src/io.rs"], shards=2, label="smoke")
assert trees() == before, f"the second run reuses its worktrees: {before} -> {trees()}"
assert again == found, f"the second run finds the same survivors: {dict(found)} -> {dict(again)}"
print("smoke: ok")
