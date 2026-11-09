"""The runner's exchange: where its jobs come from and its results go.

An exchange is a folder holding `jobs/` and `results/`. When the folder is
a Git clone, every runner on every machine shares it through the remote:
anyone with write access pushes a job file into `jobs/`; a runner pulls,
claims a job by pushing a results folder for it, runs it, and pushes the
results' text. Two runners that claim the same job at once resolve it by
the push: the second push is rejected, that runner pulls, sees the
other's claim, withdraws its own, and moves on.

A job is pending while `results/` holds no folder named after it. A
results folder is `results/<job>.<time>-<machine>/`; the machine names
the runner, since results from different machines never compare.

What is pushed: the text a reader needs (`verdict.json`, `runner.log`,
`claimed.json`, samples, reports, summaries; files of the listed kinds
up to a size), and nothing a job built or fetched (any folder holding a
`.git`, a `Cargo.toml` or a `target`). Everything stays on the machine's
disk in the same folder.
"""
import json
import subprocess
import sys
import time
from pathlib import Path

PUBLISHED_KINDS = {".json", ".log", ".txt", ".tsv", ".csv", ".md", ".err", ".html", ".svg", ".asm"}
PUBLISHED_LIMIT = 20 << 20


def publishable(out):
    """The files under `out` a reader needs, in a stable order."""
    files = []

    def walk(folder):
        entries = sorted(folder.iterdir())
        if folder != out and any(e.name in (".git", "Cargo.toml") for e in entries):
            return
        for e in entries:
            if e.is_dir():
                if not e.name.startswith("target"):
                    walk(e)
            elif e.suffix in PUBLISHED_KINDS and e.stat().st_size <= PUBLISHED_LIMIT:
                files.append(e)

    walk(out)
    return files


class Exchange:
    def __init__(self, path, machine):
        self.path = Path(path)
        self.jobs = self.path / "jobs"
        self.results = self.path / "results"
        assert self.jobs.is_dir() and self.results.is_dir(), f"{self.path} must hold jobs/ and results/"
        self.machine = machine
        assert machine and all(c.isalnum() or c in "-_" for c in machine), "a machine name is letters, digits, - and _"
        self.shared = (self.path / ".git").exists()

    def git(self, *args, check=True):
        return subprocess.run(["git", *args], cwd=self.path, capture_output=True, text=True, check=check)

    def refresh(self):
        """Take what others pushed. A pull that fails (no network) is
        reported and leaves the local copy as it was."""
        if self.shared:
            r = self.git("pull", "--ff-only", "--quiet", check=False)
            if r.returncode != 0:
                print(f"exchange: pull failed: {r.stderr.strip()}", file=sys.stderr, flush=True)

    def pending(self):
        """Job files no results folder names, oldest name first."""
        return sorted(p for p in self.jobs.glob("*.json") if not any(self.results.glob(f"{p.stem}.*")))

    def claim(self, job):
        """A results folder for `job`, pushed; None when another runner
        claimed it first."""
        out = self.results / f"{job.stem}.{time.strftime('%Y%m%d-%H%M%S')}-{self.machine}"
        out.mkdir()
        (out / "claimed.json").write_text(json.dumps({"job": job.name, "machine": self.machine, "claimed": time.strftime("%Y-%m-%dT%H:%M:%S%z")}, indent=2) + "\n")
        if not self.shared:
            return out
        self.git("add", str(out / "claimed.json"))
        self.git("commit", "--quiet", "-m", f"{self.machine} claims {job.name}")
        for _ in range(5):
            if self.git("push", "--quiet", check=False).returncode == 0:
                return out
            self.git("pull", "--rebase", "--quiet", check=False)
            others = [d for d in self.results.glob(f"{job.stem}.*") if d != out]
            if others:
                self.git("rm", "-r", "--quiet", str(out))
                self.git("commit", "--quiet", "-m", f"{self.machine} withdraws its claim on {job.name}: {others[0].name} has it")
                self.git("push", "--quiet", check=False)
                return None
        raise RuntimeError(f"could not push the claim on {job.name} in five tries")

    def publish(self, out, message):
        """Push the results' text; a conflict with others' pushes is
        resolved by rebasing (results folders never collide)."""
        if not self.shared:
            return
        files = publishable(out)
        if files:
            self.git("add", *map(str, files))
        if self.git("diff", "--cached", "--quiet", check=False).returncode == 0:
            return
        self.git("commit", "--quiet", "-m", message)
        for _ in range(5):
            if self.git("push", "--quiet", check=False).returncode == 0:
                return
            self.git("pull", "--rebase", "--quiet", check=False)
        print(f"exchange: could not push {out.name} in five tries; it stays committed locally", file=sys.stderr, flush=True)
