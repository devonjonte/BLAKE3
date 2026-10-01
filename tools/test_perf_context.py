"""Actual pair/confirmation code preserves context and requires load.

BENCH_GATE_TOOLS selects an archived gate's tools for before/after controls.
Only build/process execution is replaced; samples and decision rules are shared.
"""
import contextlib
import io
import os
import sys
import unittest
from unittest.mock import patch

if 'BENCH_GATE_TOOLS' in os.environ:
    sys.path.insert(0, os.environ['BENCH_GATE_TOOLS'])
import perf_regress as gate


class FixedContext(unittest.TestCase):
    def setUp(self):
        gate.BUSY_RUNS.clear()
        gate.POWER_SEEN.clear()
        if hasattr(gate, 'UNOBSERVED_RUNS'):
            gate.UNOBSERVED_RUNS.clear()
        self.requests = []
        self.points = ['continuous batch 16', 'lent 1 MiB']

    def compare(self, positive=False, neighbor_moves=False, unknown_stage=None, busy=False):
        def run(side, points):
            stage = 'confirmation' if len(self.requests) >= 8 else 'initial'
            unknown = stage == unknown_stage
            self.requests.append((side, list(points), stage))
            text = '# bench-hashes samples v4\n# power: mains power\n'
            text += '# load: ' + ('not measured on this platform' if unknown else 'busy' if busy else 'quiet') + '\n'
            if not unknown:
                text += '# load windows (start ms-end ms:other milli-CPUs:steal milli-CPUs): 0-1000:0:0\n'
            text += 'contender\tscenario\tuse_case\tpoint\tunit\tns/units\tstart ms\n'
            for point in points:
                case, label = ('ContinuousBatches', '16') if point == self.points[0] else ('LentMessages', '1 MiB')
                for contender in [gate.CONTROL, gate.SUBJECTS[0]]:
                    value = 100
                    if side == 'new' and contender != gate.CONTROL:
                        if positive and point == self.points[0] and self.points[1] in points:
                            value = 120  # a real cost only in the declared full context
                        if neighbor_moves and point == self.points[1]:
                            value = 80  # retains the neighbor in the original adaptive initial stage
                    text += (f'{contender}\tsolo\t{case}\t{label}\tB\t' +
                             ','.join([f'{value}/1'] * 24) + '\t' + ','.join(['0'] * 24) + '\n')
            return gate.parse(text)
        stdout, stderr = io.StringIO(), io.StringIO()
        with patch.object(gate, 'side_bench', side_effect=lambda side, rev: (side, set())), \
             patch.object(gate, 'points_of', return_value=self.points), \
             patch.object(gate, 'run', side_effect=run), \
             contextlib.redirect_stdout(stdout), contextlib.redirect_stderr(stderr):
            code = gate.compare('old', 'new')
        self.output = stdout.getvalue() + stderr.getvalue()
        return code

    def assert_fixed(self):
        self.assertTrue(all(points == self.points for _, points, _ in self.requests), self.requests)

    def test_null_stops_with_same_context(self):
        self.assertEqual(self.compare(), 0)
        self.assertEqual(len(self.requests), 2)
        self.assert_fixed()

    def test_closed_neighbor_stays_in_initial_pairs(self):
        self.assertEqual(self.compare(positive=True), 1)
        self.assertEqual(len(self.requests), 16)
        self.assert_fixed()

    def test_open_neighbor_stays_in_confirmation(self):
        self.assertEqual(self.compare(positive=True, neighbor_moves=True), 1)
        self.assertEqual(len(self.requests), 16)
        self.assert_fixed()

    def test_unknown_initial_abstains(self):
        self.assertEqual(self.compare(unknown_stage='initial'), 2)

    def test_unknown_confirmation_abstains(self):
        self.assertEqual(self.compare(positive=True, neighbor_moves=True, unknown_stage='confirmation'), 2)

    def test_busy_abstains(self):
        self.assertEqual(self.compare(busy=True), 2)


if __name__ == '__main__':
    unittest.main()
