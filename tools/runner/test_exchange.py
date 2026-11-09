"""The shared exchange: jobs pushed by anyone, claimed once, results' text
pushed back. Two clones of one bare repository stand for two machines."""
import json
import subprocess
import tempfile
import unittest
from pathlib import Path

from exchange import Exchange, publishable


def git(cwd, *args):
    return subprocess.run(["git", *args], cwd=cwd, capture_output=True, text=True, check=True).stdout


def seed(root):
    """A bare remote with jobs/ and results/, and a clone a 'submitter' uses."""
    remote = root / "remote.git"
    git(root, "init", "--quiet", "--bare", "-b", "main", str(remote))
    submitter = root / "submitter"
    git(root, "clone", "--quiet", str(remote), str(submitter))
    configure(submitter)
    (submitter / "jobs").mkdir()
    (submitter / "results").mkdir()
    (submitter / "jobs/.keep").write_text("")
    (submitter / "results/.keep").write_text("")
    git(submitter, "add", "-A")
    git(submitter, "commit", "--quiet", "-m", "the exchange")
    git(submitter, "push", "--quiet", "-u", "origin", "main")
    return remote, submitter


def configure(clone):
    git(clone, "config", "user.name", "test")
    git(clone, "config", "user.email", "test@example.invalid")
    git(clone, "config", "commit.gpgsign", "false")


def machine(root, remote, name):
    clone = root / name
    git(root, "clone", "--quiet", str(remote), str(clone))
    configure(clone)
    return Exchange(clone, name)


class SharedExchange(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name)
        self.remote, self.submitter = seed(self.root)

    def tearDown(self):
        self.tmp.cleanup()

    def submit(self, name):
        (self.submitter / "jobs" / name).write_text(json.dumps({"type": "test", "fork_commit": "0" * 40}))
        git(self.submitter, "add", "jobs")
        git(self.submitter, "commit", "--quiet", "-m", f"queue {name}")
        git(self.submitter, "push", "--quiet")

    def test_a_pushed_job_is_pending_until_a_runner_claims_it_and_results_come_back_as_text(self):
        mini = machine(self.root, self.remote, "m6")
        self.submit("3001-a.json")
        self.assertEqual(mini.pending(), [])
        mini.refresh()
        self.assertEqual([p.name for p in mini.pending()], ["3001-a.json"])
        out = mini.claim(mini.pending()[0])
        self.assertIsNotNone(out)
        self.assertEqual(mini.pending(), [])
        # The job's results: text a reader needs, and a build tree nobody does.
        (out / "verdict.json").write_text('{"status": "passed"}\n')
        (out / "samples").mkdir()
        (out / "samples/run-1.tsv").write_text("a\tb\n")
        (out / "target-old").mkdir()
        (out / "target-old/big.json").write_text("{}")
        (out / "bench").mkdir()
        (out / "bench/Cargo.toml").write_text("[package]")
        (out / "bench/README.md").write_text("fetched")
        (out / "binary").write_bytes(b"\x00" * 10)
        mini.publish(out, "3001-a: passed")
        git(self.submitter, "pull", "--quiet")
        published = sorted(p.relative_to(self.submitter / "results" / out.name).as_posix() for p in (self.submitter / "results" / out.name).rglob("*") if p.is_file())
        self.assertEqual(published, ["claimed.json", "samples/run-1.tsv", "verdict.json"])

    def test_two_machines_claiming_one_job_leave_exactly_one_claim(self):
        mini = machine(self.root, self.remote, "m6")
        laptop = machine(self.root, self.remote, "m4max")
        self.submit("3002-b.json")
        mini.refresh()
        laptop.refresh()
        job_on_mini, job_on_laptop = mini.pending()[0], laptop.pending()[0]
        first = mini.claim(job_on_mini)
        second = laptop.claim(job_on_laptop)
        self.assertIsNotNone(first)
        self.assertIsNone(second, "the later push is rejected, the claim withdrawn")
        git(self.submitter, "pull", "--quiet")
        claims = [d.name for d in (self.submitter / "results").glob("3002-b.*")]
        self.assertEqual(len(claims), 1)
        self.assertTrue(claims[0].endswith("-m6"))
        laptop.refresh()
        self.assertEqual(laptop.pending(), [], "the laptop sees the mini's claim")

    def test_a_folder_without_git_is_a_private_exchange(self):
        private = self.root / "private"
        (private / "jobs").mkdir(parents=True)
        (private / "results").mkdir()
        ex = Exchange(private, "local")
        (private / "jobs/3003-c.json").write_text("{}")
        out = ex.claim(ex.pending()[0])
        self.assertTrue((out / "claimed.json").exists())
        ex.publish(out, "nothing to push")
        self.assertEqual(ex.pending(), [])


class Publishable(unittest.TestCase):
    def test_kinds_sizes_and_build_trees(self):
        with tempfile.TemporaryDirectory() as tmp:
            out = Path(tmp)
            (out / "runner.log").write_text("x")
            (out / "huge.txt").write_bytes(b"x" * (20 * 1024 * 1024 + 1))
            (out / "lib-old").mkdir()
            (out / "lib-old/.git").mkdir()
            (out / "lib-old/README.md").write_text("fetched library")
            (out / "mutants-last").mkdir()
            (out / "mutants-last/outcomes.json").write_text("{}")
            self.assertEqual([p.relative_to(out).as_posix() for p in publishable(out)], ["mutants-last/outcomes.json", "runner.log"])


if __name__ == "__main__":
    unittest.main()
