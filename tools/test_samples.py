"""The v4 reader preserves accounting and rejects lossy duplicate rows."""
import unittest
import samples

HEADER = ("# bench-hashes samples v4\n# power: mains power\n# load: quiet\n"
          "contender\tscenario\tuse_case\tpoint\tunit\tns/units\tstart ms\n")
KEY = ("a", "solo", "OneMessage", "64 B")

def row(values="128/64", starts="0"):
    return f"a\tsolo\tOneMessage\t64 B\tB\t{values}\t{starts}\n"

class ReaderAccounting(unittest.TestCase):
    def test_preserves_unreduced_readings(self):
        run = samples.read(HEADER + row("128/64,256/128", "0,1"))
        self.assertEqual(run.measured[KEY], [(128, 64), (256, 128)])
        self.assertEqual(run.cells[KEY], [2, 2])
        self.assertEqual(run.starts[KEY], [0, 1])

    def test_rejects_duplicate_even_when_identical(self):
        for second in [row(), row("6400/64", "1")]:
            with self.assertRaisesRegex(AssertionError, "duplicate"):
                samples.read(HEADER + row() + second)

    def test_rejects_invalid_work_or_time(self):
        for values in ["1/0", "-1/64", "1/-64", "1/2/3"]:
            with self.subTest(values=values), self.assertRaises(AssertionError):
                samples.read(HEADER + row(values))

    def test_load_observation_requires_a_window(self):
        self.assertFalse(samples.read(HEADER + row()).load_observed)
        for load in ['quiet', 'busy']:
            text = HEADER.replace('# load: quiet', f'# load: {load}')
            text += '# load windows (start ms-end ms:other milli-CPUs:steal milli-CPUs): 0-1000:0:0\n'
            self.assertTrue(samples.read(text + row()).load_observed)
        text = HEADER.replace('# load: quiet', '# load: not measured on this platform')
        self.assertFalse(samples.read(text + row()).load_observed)

    def test_start_coverage_is_separate_from_any_observation(self):
        text = HEADER + '# load windows (start ms-end ms:other milli-CPUs:steal milli-CPUs): 0-1000:1200:0\n'
        run = samples.read(text + row('128/64,256/128', '999,1000'))
        self.assertTrue(run.load_observed)
        self.assertEqual(run.samples_outside_load_windows(KEY), 1)
        self.assertFalse(run.sample_starts_observed)
        self.assertEqual(run.samples_in_busy_windows(KEY), 1)
        covered = samples.read(text + row('128/64,256/128', '998,999'))
        self.assertTrue(covered.sample_starts_observed)
        run = samples.read(HEADER + row())
        self.assertEqual(run.samples_outside_load_windows(KEY), 1)
        self.assertFalse(run.sample_starts_observed)

    def test_requires_one_start_per_measurement(self):
        with self.assertRaisesRegex(AssertionError, "start for every sample"):
            samples.read(HEADER + row("128/64,256/128"))

if __name__ == "__main__":
    unittest.main()
