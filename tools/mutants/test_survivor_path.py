"""A change with new survivors: what its first run found is said at once,
and each surviving place gets one release build, in the run that confirms it."""
import collections
import io
import json
import os
import tempfile
import unittest
from contextlib import redirect_stdout
from unittest.mock import patch

import check

A = "src/a.rs\treplace a with b"
B = "src/a.rs\treplace c with d"
C = "src/a.rs\treplace e with f"


class SoFar(unittest.TestCase):
    def test_nothing_beyond_the_lists_says_nothing(self):
        self.assertEqual(check.so_far({}, {}, {}, {}), [])
        self.assertEqual(check.so_far({A: 2}, {A: (2, "speed: a reason")}, {B: 1}, {B: (1, "a hang")}), [])
        self.assertEqual(check.so_far({A: 1}, {A: (2, "speed: a reason")}, {}, {}), [], "fewer places than its row: not new")

    def test_each_name_beyond_its_row_is_named_with_its_excess(self):
        lines = check.so_far({A: 3, B: 1, C: 1}, {A: (2, "speed: a reason"), C: (1, "speed: another")}, {C: 2}, {})
        self.assertEqual(lines, [f"SURVIVES SO FAR (1): {A}", f"SURVIVES SO FAR (1): {B}", f"TIMED OUT SO FAR (2): {C}",
                                 "mutants: 3 names beyond their rows so far; each runs again alone before the verdict"])


class Looks(unittest.TestCase):
    def test_a_whole_or_confirming_run_looks_at_every_surviving_place(self):
        survivors = {"tree-0": [((A, "1:2"), "src/a.rs", "diff", 1)], "tree-1": [((B, "3:4"), "src/a.rs", "diff", 3)]}
        self.assertIs(check.second_looks(survivors, None), survivors)

    def test_a_changes_first_run_leaves_the_looks_to_the_confirming_run(self):
        survivors = {"tree-0": [((A, "1:2"), "src/a.rs", "diff", 1)]}
        self.assertEqual(check.second_looks(survivors, {}), {})
        self.assertEqual(check.second_looks(survivors, {A: (1, "speed: a reason")}), {})

    def test_the_confirming_runs_look_is_the_one_the_verdict_reads(self):
        # Why the first run's look was redundant: whatever it found for a
        # name that runs again, confirm copies the confirming run's over it.
        for first, again in [(1, 0), (0, 1), (1, 1)]:
            def rerun(files, extra, shards, label):
                self.assertEqual((files, shards, label), (["src/a.rs"], 1, "confirm"))
                check.SAME["confirm"][A] = again
                check.RELEASE_SAME["confirm"][A] = again
                return collections.Counter({A: 1}), {}, collections.Counter()
            saved = {name: collections.defaultdict(collections.Counter, getattr(check, name)) for name in ["SAME", "RELEASE_SAME"]}
            try:
                check.SAME.clear()
                check.RELEASE_SAME.clear()
                check.SAME["run"][A] = check.RELEASE_SAME["run"][A] = first
                out = io.StringIO()
                with patch.object(check, "run", rerun), patch.object(check, "LOOM_FILES", []), redirect_stdout(out):
                    found, timed = check.confirm(collections.Counter({A: 1}), {}, collections.Counter(), {}, [A])
                self.assertEqual((dict(found), dict(timed)), ({A: 1}, {}))
                self.assertEqual((check.SAME["run"][A], check.RELEASE_SAME["run"][A]), (again, again), (first, again))
            finally:
                for name, value in saved.items():
                    getattr(check, name).clear()
                    getattr(check, name).update(value)


class Budget(unittest.TestCase):
    def test_an_over_budget_run_says_what_its_release_builds_took(self):
        with tempfile.TemporaryDirectory() as d, patch.object(check, "ROOT", d), \
             patch.object(check, "LOOKS_S", collections.Counter({"confirm": 41.6})):
            shard = os.path.join(d, "tmp", "mutants-last", "run", "shard0")
            os.makedirs(shard)
            with open(os.path.join(shard, "outcomes.json"), "w") as f:
                json.dump({"outcomes": [{"phase_results": [{"phase": "Build", "duration": 42.4}, {"phase": "Test", "duration": 31.1}]}]}, f)
            out = io.StringIO()
            with redirect_stdout(out):
                check.budget(check.time.monotonic() - 175)
            self.assertEqual(out.getvalue().strip(), "mutants: took 175 s, OVER the 60 s budget "
                             "(shard time: Build 42 s, Test 31 s; survivors' release builds: 42 s)")


if __name__ == "__main__":
    unittest.main()
