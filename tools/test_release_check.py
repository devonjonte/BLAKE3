"""Release-gate controls. All GitHub answers and release logs are fixtures."""
import contextlib
import importlib.util
import io
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

spec = importlib.util.spec_from_file_location("release_check", Path(__file__).with_name("release-check.py"))
check = importlib.util.module_from_spec(spec)
spec.loader.exec_module(check)

HEAD, OLD = "a" * 40, "b" * 40
RUN = {"id": 7, "name": "tests", "status": "completed", "conclusion": "success"}


def job(conclusion="success", status="completed"):
    return {"name": "test job", "status": status, "conclusion": conclusion}


class CI(unittest.TestCase):
    def result(self, jobs):
        with patch.object(check, "github", return_value={"total_count": len(jobs), "jobs": jobs}):
            return check.ci_result(RUN)

    def test_success_needs_successful_jobs(self):
        self.assertIs(self.result([job(), job()]), True)
        self.assertIsNone(self.result([]))

    def test_skipped_or_pending_is_open(self):
        for other in [job("skipped"), job(None, "in_progress")]:
            with self.subTest(other=other):
                self.assertIsNone(self.result([job(), other]))

    def test_failed_or_cancelled_does_not_pass(self):
        for conclusion in ["failure", "cancelled", "action_required"]:
            with self.subTest(conclusion=conclusion):
                self.assertIs(self.result([job(conclusion)]), False)

    def test_job_timeout_stays_distinct(self):
        self.assertEqual(self.result([job("timed_out")]), check.TIMED_OUT)

    def test_unfinished_or_failed_workflow_does_not_pass(self):
        with patch.object(check, "github") as github:
            self.assertIsNone(check.ci_result(dict(RUN, status="in_progress", conclusion=None)))
            self.assertIs(check.ci_result(dict(RUN, conclusion="failure")), False)
            self.assertEqual(check.ci_result(dict(RUN, conclusion="timed_out")), check.TIMED_OUT)
            github.assert_not_called()

    def test_all_pages_are_checked(self):
        replies = [{"total_count": 101, "jobs": [job()] * 100}, {"total_count": 101, "jobs": [job("skipped")]}]
        with patch.object(check, "github", side_effect=replies) as github:
            self.assertIsNone(check.ci_result(RUN))
            self.assertIn("page=2", github.call_args.args[0])

    def test_missing_page_stops(self):
        with patch.object(check, "github", return_value={"total_count": 1, "jobs": []}):
            with self.assertRaises(AssertionError):
                check.ci_result(RUN)


class ReleaseEvidence(unittest.TestCase):
    def run_gate(self, cells="all", kind="check", ci_jobs=None, new=HEAD, old=OLD, verdict="no regression"):
        jobs = [job(), job()] if ci_jobs is None else ci_jobs
        def git(*args):
            if args[0] == "rev-parse":
                return HEAD if args[1] == "candidate" else OLD
            if args[0] == "tag":
                return "v0.3.0+fixture"
            if args[0] == "diff":
                return "README.md\nQUALITY.md\nCHANGELOG.md"
            raise AssertionError(args)

        def github(path):
            if "/actions/runs?" in path:
                return {"workflow_runs": [RUN]}
            if "/actions/runs/7/jobs?" in path:
                return {"total_count": len(jobs), "jobs": jobs}
            if path.endswith("/statuses"):
                return [{"context": "long proofs", "state": "success"}]
            raise AssertionError(path)

        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "runner/jobs").mkdir(parents=True)
            (root / "runner/results/1").mkdir(parents=True)
            task = {"type": kind, "old_commit": old, "new_commit": new}
            if cells is not None:
                task["cells"] = cells
            (root / "runner/jobs/job.json").write_text(json.dumps(task))
            (root / "runner/results/1/verdict.json").write_text(json.dumps({"job": "job.json", "status": verdict}))
            output = io.StringIO()
            with patch.object(check, "MAIN", tmp), patch.object(check, "git", git), \
                 patch.object(check, "github", github), patch.object(check, "log_ends_with", return_value=True), \
                 patch("sys.argv", ["release-check.py", "candidate"]), contextlib.redirect_stdout(output):
                with self.assertRaises(SystemExit) as caught:
                    check.main()
            return caught.exception.code, output.getvalue()

    def test_complete_fixture_passes(self):
        self.assertEqual(self.run_gate()[0], 0)

    def test_skipped_ci_not_pass(self):
        code, output = self.run_gate(ci_jobs=[job(), job("skipped")])
        self.assertEqual(code, 1)
        self.assertIn("OPEN  CI, every job", output)

    def test_partial_mac_not_pass(self):
        code, output = self.run_gate(cells=None)
        self.assertEqual(code, 1)
        self.assertIn("OPEN  Mac check", output)

    def test_non_check_mac_not_pass(self):
        self.assertEqual(self.run_gate(kind="benchmark")[0], 1)

    def test_wrong_commits_not_pass(self):
        self.assertEqual(self.run_gate(new="c" * 40)[0], 1)
        self.assertEqual(self.run_gate(old="c" * 40)[0], 1)

    def test_mac_undecided_outcomes_remain_distinct(self):
        for verdict, label in [("timed out", "TIMED OUT"), ("no verdict", "NO VERDICT")]:
            with self.subTest(verdict=verdict):
                code, output = self.run_gate(verdict=verdict)
                self.assertEqual(code, 2)
                self.assertIn(label + "  Mac check", output)


if __name__ == "__main__":
    unittest.main()
