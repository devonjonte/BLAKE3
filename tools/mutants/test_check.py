"""CPU-conditioned survivor-list controls: python3 -m unittest discover -s tools/mutants."""
import subprocess
import unittest
from unittest.mock import mock_open, patch

import check


class Conditions(unittest.TestCase):
    def test_has_lacks_are_complements(self):
        for flags in [set(), {"avx512f"}, {"avx512vl"}, {"avx512f", "avx512vl"}]:
            with self.subTest(flags=flags), patch.object(check, "FLAGS", flags):
                self.assertTrue(check.applies("unconditional reason"))
                self.assertEqual(check.applies("[cpu has avx512f] reason"), "avx512f" in flags)
                self.assertEqual(check.applies("[cpu lacks avx512f] reason"), "avx512f" not in flags)
                self.assertEqual(check.applies("[cpu has avx512f avx512vl] reason"), len(flags) == 2)
                self.assertEqual(check.applies("[cpu lacks avx512f avx512vl] reason"), len(flags) != 2)

    def test_malformed_conditions_stop(self):
        for reason in ["[cpu have avx2] reason", "[cpu has ] reason", "[cpu has avx2 reason",
                       "[cpu has avx2]reason", "[cpu has avx2] ", " [cpu has avx2] reason",
                       "[CPU has avx2] reason", "[cpu has avx2, avx512f] reason"]:
            with self.subTest(reason=reason), self.assertRaisesRegex(ValueError, "malformed CPU condition"):
                check.applies(reason)

    def test_select_and_preserve_inactive_rows(self):
        rows = "files: src/platform.rs\n" + "".join(
            f"src/platform.rs\tmutant\t1\t[cpu {condition} avx2] reason\n"
            for condition in ["has", "lacks"])
        for flags, active, inactive in [({"avx2"}, "has", "lacks"), (set(), "lacks", "has")]:
            with patch.object(check, "FLAGS", flags), patch.object(check, "INACTIVE", []), \
                 patch("builtins.open", mock_open(read_data=rows)):
                files, known = check.read_known()
                self.assertEqual(files, ["src/platform.rs"])
                self.assertEqual(known, {"src/platform.rs\tmutant": (1, f"[cpu {active} avx2] reason")})
                self.assertEqual(check.INACTIVE, [f"src/platform.rs\tmutant\t1\t[cpu {inactive} avx2] reason"])

    def test_duplicate_active_rows_stop(self):
        rows = "src/platform.rs\tmutant\t1\treason\nsrc/platform.rs\tmutant\t2\t[cpu has avx2] reason\n"
        with patch.object(check, "FLAGS", {"avx2"}), patch("builtins.open", mock_open(read_data=rows)), \
             self.assertRaisesRegex(AssertionError, "two rows apply"):
            check.read_known()


class Readers(unittest.TestCase):
    def test_linux_fields(self):
        for field in ["flags", "Features"]:
            with patch.object(check.sys, "platform", "linux"), \
                 patch("builtins.open", mock_open(read_data=f"processor: 0\n{field}\t: avx2 avx512f\n")):
                self.assertEqual(check.cpu_flags(), {"avx2", "avx512f"})

    def test_linux_reader_error_propagates(self):
        with patch.object(check.sys, "platform", "linux"), patch("builtins.open", side_effect=PermissionError("denied")), \
             self.assertRaises(PermissionError):
            check.cpu_flags()

    def test_linux_missing_field_stops(self):
        with patch.object(check.sys, "platform", "linux"), patch("builtins.open", mock_open(read_data="processor: 0\n")), \
             self.assertRaisesRegex(ValueError, "no flags or Features"):
            check.cpu_flags()

    def test_macos_selection(self):
        out = subprocess.CompletedProcess([], 0, "hw.optional.avx2_0: 1\nhw.optional.avx512f: 0\n")
        with patch.object(check.sys, "platform", "darwin"), patch.object(check.subprocess, "run", return_value=out) as run:
            self.assertEqual(check.cpu_flags(), {"avx2_0"})
            run.assert_called_once_with(["sysctl", "hw.optional"], capture_output=True, text=True, check=True)

    def test_macos_reader_errors_propagate(self):
        for error in [FileNotFoundError("sysctl"), subprocess.CalledProcessError(1, ["sysctl", "hw.optional"])]:
            with patch.object(check.sys, "platform", "darwin"), patch.object(check.subprocess, "run", side_effect=error), \
                 self.assertRaises(type(error)):
                check.cpu_flags()

    def test_macos_missing_or_malformed_output_stops(self):
        for text in ["", "hw.optional.avx2_0", "hw.optional.avx2_0:", "unexpected: 1"]:
            out = subprocess.CompletedProcess([], 0, text)
            with patch.object(check.sys, "platform", "darwin"), patch.object(check.subprocess, "run", return_value=out), \
                 self.assertRaisesRegex(ValueError, "missing or malformed"):
                check.cpu_flags()

class Placeholders(unittest.TestCase):
    def test_a_new_time_outs_placeholder_names_the_stopped_tests(self):
        name = "src/lanes.rs\treplace spin_for_work -> bool with true"
        with patch.object(check, "STOPPED", {name: {"blake3-servil b_test", "blake3-servil a_test"}}):
            self.assertEqual(check.unclassified(name),
                             "UNCLASSIFIED (the clock stopped: blake3-servil a_test, blake3-servil b_test)")
            self.assertEqual(check.unclassified("src/lib.rs\tother"), "UNCLASSIFIED")


if __name__ == "__main__":
    unittest.main()
