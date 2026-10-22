#!/usr/bin/env python3
"""Wait for a runner job to finish, then print its verdict.

    python3 tools/runner/wait_for.py JOB [LIMIT_SECONDS]

JOB is the job file's name in runner/jobs/ (with or without `.json`).
Checks every 30 s for runner/results/<JOB>.*/verdict.json and prints it;
gives up after LIMIT_SECONDS (default: the job's time limit plus ten
minutes for the clone and build), or after IDLE_SECONDS in which the job
has not started and no other job ran: the runner is stopped (the Mac
asleep, or the runner not started). The VM stays idle meanwhile, as a Mac
measurement needs. Exit 0 when the verdict's status is "ok" or
"no regression", 1 for any other status, 2 when the limit passes first.
"""
import json
import os
import sys
import time
from pathlib import Path

EXCHANGE = Path(__file__).resolve().parents[2] / "runner"
# A runner takes its next job within seconds of finishing one.
IDLE_SECONDS = 180


def main():
    assert 2 <= len(sys.argv) <= 3, __doc__
    stem = sys.argv[1].removesuffix(".json")
    job = json.loads((EXCHANGE / "jobs" / f"{stem}.json").read_text())
    limit = int(sys.argv[2]) if len(sys.argv) == 3 else job.get("time_limit_seconds", 1800) + 600
    deadline = time.monotonic() + limit
    idle_since = time.monotonic()
    results = EXCHANGE / "results"
    while time.monotonic() < deadline:
        # One listing of the folder and at most two files' status a poll:
        # the folder is on the Mac, and each operation through the mount is
        # work on the Mac while it measures (a poll that read every result
        # folder, every 10 s, kept half a CPU busy there: October 22, 2026).
        names = os.listdir(results)
        mine = sorted(n for n in names if n.startswith(stem + "."))
        if mine and (results / mine[-1] / "verdict.json").exists():
            verdict = json.loads((results / mine[-1] / "verdict.json").read_text())
            print(f"{results / mine[-1]}\n{json.dumps(verdict, indent=2)}")
            return 0 if verdict["status"] in ("ok", "no regression") else 1
        # A job running: the newest folder without a verdict yet, made
        # within the longest a job may take (older ones are jobs that crashed).
        newest = max(names, key=lambda n: n.rsplit(".", 1)[-1], default=None)
        running = newest is not None and not (results / newest / "verdict.json").exists() \
            and time.time() - (results / newest).stat().st_mtime < 7200 + 600
        if mine or running:
            idle_since = time.monotonic()
        elif time.monotonic() - idle_since > IDLE_SECONDS:
            print(f"wait_for: {stem} has not started and no job has run for {IDLE_SECONDS} s: the runner looks stopped; start it on the Mac (tools/runner/setup-mac.sh)")
            return 2
        time.sleep(30)
    print(f"wait_for: no verdict for {stem} after {limit} s; is the runner running on the Mac?")
    return 2


if __name__ == "__main__":
    sys.exit(main())
