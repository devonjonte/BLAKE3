#!/usr/bin/env python3
"""The release checklist's mechanical steps, read from where each gate
left its result, for one commit (PROCEDURES.md, "Releases").

    pypy3 tools/release-check.py [COMMIT]        # default: servil's tip

It runs nothing heavy. For each step it reads the evidence the gate
wrote and prints one line: PASS, FAIL, or OPEN (no evidence yet, with the
command that makes it). Exit status 0 only when every step passes.

- CI: GitHub's workflow runs on the commit (every job succeeded).
- Long proofs: the commit's GitHub status "long proofs" (long-proofs.sh).
- Mac check: runner/results/*/verdict.json whose job names this commit as
  new_commit and the previous release as old_commit (a "check" job with
  "cells": "all").
- VM check: tmp/night/check-release-vm.log, written by
  `cd bench-hashes && cargo run --release -- check --against <previous tag> --cells all`.
- Full mutation run: tmp/night/mutants-release.log ending "each known and
  explained", from `pypy3 tools/mutants/check.py` on the commit.
- check-builds: tmp/night/check-builds-release.log ending "every build passes".
- Publish dry run: tmp/night/publish-dry-run.log, from
  `cargo publish --dry-run` in the root and in b3sum/.
- The pages: README.md, QUALITY.md, CHANGELOG.md changed since the
  previous release (a release rewrites them for its readers).
"""

import glob
import json
import os
import re
import subprocess
import sys
import urllib.request

ROOT = subprocess.run(["git", "rev-parse", "--show-toplevel"], capture_output=True, text=True, check=True).stdout.strip()
# The main checkout holds the token, the runner's jobs and results, and the
# night's logs, for a worktree too.
MAIN = subprocess.run(["git", "-C", ROOT, "rev-parse", "--path-format=absolute", "--git-common-dir"], capture_output=True, text=True, check=True).stdout.strip()
MAIN = os.path.dirname(MAIN) if MAIN.endswith("/.git") else MAIN


def git(*args):
    return subprocess.run(["git", "-C", ROOT, *args], capture_output=True, text=True, check=True).stdout.strip()


def github(path):
    token = open(os.path.join(MAIN, "ghtokenclassic.txt")).read().strip()
    request = urllib.request.Request("https://api.github.com" + path, headers={"Authorization": f"token {token}"})
    with urllib.request.urlopen(request, timeout=60) as response:
        return json.load(response)


def log_ends_with(path, text):
    full = os.path.join(MAIN, path)
    if not os.path.exists(full):
        return None
    return text in open(full, errors="replace").read()[-4000:]


def main():
    commit = git("rev-parse", sys.argv[1] if len(sys.argv) > 1 else "servil")
    tags = [t for t in git("tag", "--list", "v*", "--sort=-creatordate").split() if t]
    previous = tags[0] if tags else None
    results = []

    def step(name, ok, how):
        results.append(ok)
        print(f"{'PASS' if ok else 'FAIL' if ok is False else 'OPEN'}  {name}" + ("" if ok else f": {how}"))

    runs = github(f"/repos/johnservil/BLAKE3/actions/runs?head_sha={commit}&per_page=20").get("workflow_runs", [])
    ci = [r for r in runs if r["name"] == "tests"]
    step("CI, every job", (ci[0]["conclusion"] == "success") if ci and ci[0]["status"] == "completed" else None,
         "dispatch the tests workflow on the commit and wait")

    statuses = github(f"/repos/johnservil/BLAKE3/commits/{commit}/statuses")
    proofs = [s for s in statuses if s["context"] == "long proofs"]
    step("long proofs", (proofs[0]["state"] == "success") if proofs else None, "sh tools/verify/long-proofs.sh <commit> (overnight)")

    mac = None
    for verdict in sorted(glob.glob(os.path.join(MAIN, "runner/results/*/verdict.json"))):
        v = json.load(open(verdict))
        job = os.path.join(MAIN, "runner/jobs", v["job"])
        if not os.path.exists(job):
            continue
        j = json.load(open(job))
        if j.get("new_commit") == commit and (previous is None or j.get("old_commit") == git("rev-parse", previous)):
            mac = v["status"]
    step("Mac check against the previous release", (mac == "no regression") if mac else None,
         f"a check job (cells all) with old_commit {previous or '<previous tag>'} and new_commit {commit[:10]}")

    step("VM check against the previous release", log_ends_with("tmp/night/check-release-vm.log", "no cell slower"),
         f"(cd bench-hashes && cargo run --release -- check --against {previous or '<previous tag>'} --cells all) > tmp/night/check-release-vm.log")
    step("full mutation run", log_ends_with("tmp/night/mutants-release.log", "each known and explained"),
         "pypy3 tools/mutants/check.py > tmp/night/mutants-release.log (overnight)")
    step("check-builds", log_ends_with("tmp/night/check-builds-release.log", "every build passes"),
         "sh tools/check-builds.sh > tmp/night/check-builds-release.log")
    step("cargo publish --dry-run", log_ends_with("tmp/night/publish-dry-run.log", "publish-dry-run: ok"),
         "(cargo publish --dry-run --allow-dirty && cd b3sum && cargo publish --dry-run --allow-dirty) > tmp/night/publish-dry-run.log && echo publish-dry-run: ok >> tmp/night/publish-dry-run.log")

    if previous:
        changed = set(git("diff", "--name-only", previous, commit).split())
        for page in ["README.md", "QUALITY.md", "CHANGELOG.md"]:
            step(f"{page} rewritten since {previous}", page in changed, "a release rewrites it for its readers")
    else:
        step("pages rewritten since the previous release", None, "no previous release tag found")

    print("release-check:", "every step passes" if all(results) else f"{sum(1 for r in results if not r)} steps open or failing")
    sys.exit(0 if all(results) else 1)


if __name__ == "__main__":
    main()
