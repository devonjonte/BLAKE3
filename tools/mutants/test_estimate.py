"""The check's opening estimate comes from this machine's last check, or is not given."""
import json
import os
import tempfile
import unittest

import check


def outcome(scenario, *durations):
    return {"scenario": scenario, "phase_results": [{"phase": p, "duration": d} for p, d in zip(("Build", "Test"), durations)]}


class Estimate(unittest.TestCase):
    def test_a_rate_is_a_shards_unmutated_run_and_a_mutants_mean(self):
        shards = [[outcome("Baseline", 4.0, 2.0), outcome({"Mutant": {}}, 1.5, 0.5), outcome({"Mutant": {}}, 2.5, 1.5)],
                  [outcome("Baseline", 5.0, 3.0), outcome({"Mutant": {}}, 1.0, 0.0)]]
        self.assertEqual(check.rate_of(shards), (7.0, 7.0 / 3))
        # No mutant ran, or no shard: nothing to go by.
        self.assertIsNone(check.rate_of([[outcome("Baseline", 4.0, 2.0)]]))
        self.assertIsNone(check.rate_of([]))

    def test_the_estimate_is_the_longest_shard(self):
        # 102 mutants on 12 shards: nine on the fullest, after its unmutated run.
        self.assertEqual(check.estimate(102, 12, (6.0, 2.7)), 30)
        self.assertEqual(check.estimate(1, 1, (6.0, 2.7)), 9)
        self.assertIsNone(check.estimate(102, 12, None))

    def test_the_rate_is_kept_and_read_back(self):
        with tempfile.TemporaryDirectory() as d:
            path = os.path.join(d, "kept", "rate.json")
            self.assertIsNone(check.read_rate(path))
            check.keep_rate(path, (6.5, 2.25))
            self.assertEqual(check.read_rate(path), (6.5, 2.25))
            with open(path) as f:
                self.assertEqual(json.load(f), {"unmutated_s": 6.5, "mutant_s": 2.25})
            check.keep_rate(path, None)   # a run with nothing to go by keeps the last rate
            self.assertEqual(check.read_rate(path), (6.5, 2.25))
            with open(path, "w") as f:
                f.write("not json")
            self.assertIsNone(check.read_rate(path))

    def test_the_plan_line_says_where_the_estimate_is_from_or_gives_none(self):
        self.assertEqual(check.plan_line(102, 12, (6.0, 2.7)), "mutants: the change's 102 mutants on 12 shards (about 30 s, by this machine's last check)")
        self.assertEqual(check.plan_line(400, 6, (6.0, 2.7)), "mutants: the change's 400 mutants on 6 shards (about 187 s, by this machine's last check: over the 60 s budget)")
        self.assertEqual(check.plan_line(1, 1, None), "mutants: the change's 1 mutants on 1 shard")


if __name__ == "__main__":
    unittest.main()
