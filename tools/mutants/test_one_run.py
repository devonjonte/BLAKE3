"""One mutation run at a time holds the worktrees."""
import tempfile
import unittest
from unittest.mock import patch

import check


class OneRun(unittest.TestCase):
    def test_a_second_run_stops_and_names_the_worktrees_and_a_later_one_runs(self):
        with tempfile.TemporaryDirectory() as d, patch.object(check, "WORKTREES", d + "/trees"):
            first = check.one_run_at_a_time()
            with self.assertRaises(SystemExit) as stopped:
                check.one_run_at_a_time()
            self.assertIn("another run is using " + d + "/trees", str(stopped.exception))
            self.assertIn("TMPDIR", str(stopped.exception))
            first.close()
            check.one_run_at_a_time().close()


if __name__ == "__main__":
    unittest.main()
