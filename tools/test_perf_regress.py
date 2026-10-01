"""The gate requires load observation in initial and confirmation stages."""
import contextlib
import io
import unittest
from unittest.mock import patch
import perf_regress as gate


def readings(value, observed=True, busy=False, outside=False):
    text = '# bench-hashes samples v4\n# power: mains power\n'
    text += '# load: ' + ('busy' if busy else 'quiet' if observed else 'not measured on this platform') + '\n'
    if observed:
        text += '# load windows (start ms-end ms:other milli-CPUs:steal milli-CPUs): 0-1000:0:0\n'
    text += 'contender\tscenario\tuse_case\tpoint\tunit\tns/units\tstart ms\n'
    for contender, ns in [(gate.CONTROL, 100), (gate.SUBJECTS[0], value)]:
        text += (f'{contender}\tsolo\tContinuousBatches\t16\tmsg\t' +
                 ','.join([f'{ns}/1'] * 24) + '\t' + ','.join(['1000' if outside else '0'] * 24) + '\n')
    return gate.parse(text)


class LoadPolicy(unittest.TestCase):
    def setUp(self):
        gate.BUSY_RUNS.clear()
        gate.UNOBSERVED_RUNS.clear()
        gate.POWER_SEEN.clear()

    def compare(self, initial_value=100, initial_observed=True, confirmation_observed=True, busy=False, outside=False, confirmation_outside=False):
        def pairs(old, new, start, points, use_cases):
            observed = initial_observed if start == 0 else confirmation_observed
            uncovered = outside or (start > 0 and confirmation_outside)
            return [(readings(100, observed, busy, uncovered), readings(initial_value, observed, busy, uncovered))
                    for _ in range(gate.PAIRS)]
        with patch.object(gate, 'side_bench', return_value=('exe', set())), \
             patch.object(gate, 'pairs', side_effect=pairs), \
             contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
            return gate.compare('old', 'new')

    def test_observed_null_passes(self):
        self.assertEqual(self.compare(), 0)

    def test_observed_positive_holds(self):
        self.assertEqual(self.compare(initial_value=120), 1)

    def test_unobserved_initial_has_no_verdict(self):
        self.assertEqual(self.compare(initial_observed=False), 2)

    def test_unobserved_confirmation_has_no_verdict(self):
        self.assertEqual(self.compare(initial_value=120, confirmation_observed=False), 2)

    def test_busy_has_no_verdict(self):
        self.assertEqual(self.compare(busy=True), 2)

    def test_quiet_windows_with_uncovered_starts_have_no_verdict(self):
        self.assertEqual(self.compare(outside=True), 2)

    def test_uncovered_confirmation_starts_with_windows_have_no_verdict(self):
        self.assertEqual(self.compare(initial_value=120, confirmation_outside=True), 2)


if __name__ == '__main__':
    unittest.main()
