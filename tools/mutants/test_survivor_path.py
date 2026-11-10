"""A change with new survivors: what its first run found is said at once,
and each surviving place is built for release once, by the first run that asks."""
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

    def test_a_changes_first_run_looks_at_its_new_survivors_alone(self):
        a1, a2, b = ((A, "1:2"), "src/a.rs", "diff", 1), ((A, "5:6"), "src/a.rs", "diff", 5), ((B, "3:4"), "src/a.rs", "diff", 3)
        survivors = {"tree-0": [a1, b], "tree-1": [a2]}
        self.assertEqual(check.second_looks(survivors, {}), survivors)
        # A has two surviving places and a row for two: listed, no look. B is new.
        self.assertEqual(check.second_looks(survivors, {A: (2, "speed: a reason")}), {"tree-0": [b]})
        # A row for one of A's two places: A is new again, both places.
        self.assertEqual(check.second_looks(survivors, {A: (1, "speed: a reason"), B: (1, "speed: another")}), {"tree-0": [a1], "tree-1": [a2]})

    def test_a_place_is_built_for_release_once(self):
        a1, a2, b = ((A, "1:2"), "src/a.rs", "diff", 1), ((A, "5:6"), "src/a.rs", "diff", 5), ((B, "3:4"), "src/a.rs", "diff", 3)
        # Nothing built yet: everything is to make.
        self.assertEqual(check.looks_to_make({"tree-0": [a1, b], "tree-1": [a2]}, {}), ({"tree-0": [a1, b], "tree-1": [a2]}, []))
        # The confirming run asks about the same places from its one tree:
        # the two the first run built are remembered, with their answers kept
        # apart (one the same code, one not), and the place it did not build
        # (it was caught the first time) is still to make.
        looked = {(A, "1:2"): True, (B, "3:4"): False}
        to_make, remembered = check.looks_to_make({"confirm-0": [a1, a2, b]}, looked)
        self.assertEqual(to_make, {"confirm-0": [a2]})
        self.assertEqual(remembered, [(A, "1:2"), (B, "3:4")])
        self.assertEqual([key for key in remembered if looked[key]], [(A, "1:2")])
        # All remembered: no tree is left to build in.
        self.assertEqual(check.looks_to_make({"confirm-0": [a1, b]}, looked), ({}, [(A, "1:2"), (B, "3:4")]))

    def test_the_confirming_runs_look_is_the_one_the_verdict_reads(self):
        # The verdict's "same code" counts are the confirming run's, copied
        # over the first run's: so the confirming run must have an answer for
        # every place it finds surviving, remembered or built.
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
