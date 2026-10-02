#!/usr/bin/env python3
"""Wait for a runner job to finish, then print its verdict.

    pypy3 tools/runner/wait_for.py JOB [LIMIT_SECONDS]

JOB is the job file's name in runner/jobs/ (with or without `.json`).
Checks every 10 s for runner/results/<JOB>.*/verdict.json and prints it;
gives up after LIMIT_SECONDS (default: the job's time limit plus ten
minutes for the clone and build), or after IDLE_SECONDS in which the job
has not started and no other job ran: the runner is stopped (the Mac
asleep, or the runner not started). The VM stays idle meanwhile, as a Mac
measurement needs. Exit 0 when the verdict's status is "ok" or
"no regression", 1 for any other status, 2 when the limit passes first.
"""
import json
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
    while time.monotonic() < deadline:
        done = sorted((EXCHANGE / "results").glob(f"{stem}.*/verdict.json"))
        if done:
            verdict = json.loads(done[-1].read_text())
            print(f"{done[-1].parent}\n{json.dumps(verdict, indent=2)}")
            return 0 if verdict["status"] in ("ok", "no regression") else 1
        started = any((EXCHANGE / "results").glob(f"{stem}.*"))
        # A job running: its folder without a verdict yet, made within the
        # longest a job may take (older ones are jobs that crashed).
        running = any(d.is_dir() and not (d / "verdict.json").exists() and time.time() - d.stat().st_mtime < 7200 + 600
                      for d in (EXCHANGE / "results").iterdir())
        if started or running:
            idle_since = time.monotonic()
        elif time.monotonic() - idle_since > IDLE_SECONDS:
            print(f"wait_for: {stem} has not started and no job has run for {IDLE_SECONDS} s: the runner looks stopped; start it on the Mac (tools/runner/setup-mac.sh)")
            return 2
        time.sleep(10)
    print(f"wait_for: no verdict for {stem} after {limit} s; is the runner running on the Mac?")
    return 2


if __name__ == "__main__":
    sys.exit(main())
