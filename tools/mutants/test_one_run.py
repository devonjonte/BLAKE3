"""One mutation run at a time holds the worktrees, and one each target directory."""
import os
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

import check


class OneRun(unittest.TestCase):
    def test_a_second_run_stops_and_names_the_worktrees_and_a_later_one_runs(self):
        with tempfile.TemporaryDirectory() as d, patch.object(check, "WORKTREES", d + "/trees"), patch.object(check, "TARGET_DIR", d + "/target"):
            first = check.one_run_at_a_time()
            with self.assertRaises(SystemExit) as stopped:
                check.one_run_at_a_time()
            self.assertIn("another run is using " + d + "/trees", str(stopped.exception))
            self.assertIn("TMPDIR", str(stopped.exception))
            first.close()
            check.one_run_at_a_time().close()

    def test_a_second_run_with_worktrees_of_its_own_stops_at_a_shared_target_directory(self):
        """Two linked worktrees build in the main checkout's target/ (#453): a
        TMPDIR of its own gives a second run other worktrees and the same
        builds and same-code records."""
        with tempfile.TemporaryDirectory() as d, patch.object(check, "TARGET_DIR", d + "/target"):
            with patch.object(check, "WORKTREES", d + "/one/trees"):
                os.makedirs(d + "/one")
                first = check.one_run_at_a_time()
            with patch.object(check, "WORKTREES", d + "/two/trees"):
                os.makedirs(d + "/two")
                with self.assertRaises(SystemExit) as stopped:
                    check.one_run_at_a_time()
                self.assertIn("another run is building in " + d + "/target", str(stopped.exception))
                self.assertIn(d + "/target/mutants.lock", str(stopped.exception))
                self.assertIn("CARGO_TARGET_DIR", str(stopped.exception))
                # the stopped run gave its own worktrees up again: a third run there gets as far
                with self.assertRaises(SystemExit) as again:
                    check.one_run_at_a_time()
                self.assertIn("building in", str(again.exception))
                first.close()
                check.one_run_at_a_time().close()

    def test_a_run_with_a_target_directory_of_its_own_runs_beside_another(self):
        with tempfile.TemporaryDirectory() as d:
            os.makedirs(d + "/one"), os.makedirs(d + "/two")
            with patch.object(check, "WORKTREES", d + "/one/trees"), patch.object(check, "TARGET_DIR", d + "/one/target"):
                first = check.one_run_at_a_time()
            with patch.object(check, "WORKTREES", d + "/two/trees"), patch.object(check, "TARGET_DIR", d + "/two/target"):
                second = check.one_run_at_a_time()
            first.close(), second.close()

    def test_a_run_of_every_crate_holds_each_crates_target_directory(self):
        """A run takes the locks of all its crates before its first crate
        starts: a second run that shares any one of them stops, and one that
        shares none runs."""
        with tempfile.TemporaryDirectory() as d:
            os.makedirs(d + "/one"), os.makedirs(d + "/two"), os.makedirs(d + "/root")
            os.symlink(d + "/root", d + "/link")
            with patch.object(check, "WORKTREES", d + "/one/trees"):
                first = check.one_run_at_a_time([d + "/root/target", d + "/threads/target", d + "/root/target", d + "/link/target"])
            self.assertEqual(len(first.files), 3)  # the worktrees', and one a directory, whatever names it was given by
            with patch.object(check, "WORKTREES", d + "/two/trees"):
                with self.assertRaises(SystemExit) as stopped:
                    check.one_run_at_a_time([d + "/elsewhere/target", d + "/threads/target"])
                self.assertIn("another run is building in " + d + "/threads/target", str(stopped.exception))
                check.one_run_at_a_time([d + "/elsewhere/target"]).close()
                first.close()
                check.one_run_at_a_time([d + "/root/target", d + "/threads/target"]).close()

    def test_a_crates_process_takes_no_lock_where_the_run_that_started_it_holds_them(self):
        with tempfile.TemporaryDirectory() as d, patch.object(check, "WORKTREES", d + "/trees"), patch.object(check, "TARGET_DIR", d + "/target"):
            run = check.one_run_at_a_time()
            with patch.dict(os.environ, {check.LOCKS_HELD_BY: str(os.getppid())}):
                self.assertEqual(check.one_run_at_a_time().files, [])
            # the number of another process than the one that started this: no run of this one's holds them
            with patch.dict(os.environ, {check.LOCKS_HELD_BY: str(os.getppid() + 1)}):
                with self.assertRaises(SystemExit):
                    check.one_run_at_a_time()
            run.close()

    def test_a_crates_process_keeps_the_hold_after_the_run_that_started_it(self):
        """The run's process hands its locks to each crate's process, open:
        while that one lives, the hold stands, whatever became of the run's."""
        with tempfile.TemporaryDirectory() as d, patch.object(check, "WORKTREES", d + "/trees"), patch.object(check, "TARGET_DIR", d + "/target"):
            run = check.one_run_at_a_time()
            crate = subprocess.Popen([sys.executable, "-c", "import time; print('started', flush=True); time.sleep(60)"],
                                     pass_fds=[lock.fileno() for lock in run.files], stdout=subprocess.PIPE, text=True)
            try:
                self.assertEqual(crate.stdout.readline(), "started\n")
                run.close()
                with self.assertRaises(SystemExit) as stopped:
                    check.one_run_at_a_time()
                self.assertIn("another run is", str(stopped.exception))
            finally:
                crate.kill()
                crate.wait()
                crate.stdout.close()
            check.one_run_at_a_time().close()


if __name__ == "__main__":
    unittest.main()
