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

class Model(unittest.TestCase):
    def test_a_name_counts_place_by_place_with_the_model(self):
        # gate20 (October 24): Finish::wait's deleted ! at two places; the
        # suite's clock stopped one, which the model catches, and the
        # other survives both. Counted by name, the caught place stood as
        # a time-out.
        name = "src/finish.rs\tdelete ! in Finish::wait"
        outcomes = {"run": {(name, "91:16"): "MissedMutant", (name, "97:75"): "TimedOut"},
                    "loom": {(name, "91:16"): "MissedMutant", (name, "97:75"): "CaughtMutant"}}
        with patch.object(check, "PLACE_OUTCOMES", outcomes), patch.object(check, "LOOM_FILES", ["src/finish.rs"]):
            found, timed = check.with_model("run", {name: 1}, {name: 1})
        self.assertEqual((found.get(name, 0), timed.get(name, 0)), (1, 0))

class Limits(unittest.TestCase):
    def test_tests_share_the_cpus_and_fit_in_memory(self):
        gib = 1 << 30
        with patch.object(check, "memory_cap", lambda shards: min(8 * gib, (15 * gib - 4 * gib) // shards)):
            threads, cap = check.test_limits(6, 20, 15 * gib)
        self.assertEqual(threads, 3)
        self.assertLessEqual(6 * threads * cap, 11 * gib, "every shard's tests at their cap fit")
        self.assertGreater(cap, 10 * 41 << 20, "ten times the heaviest honest test")
        with patch.object(check, "memory_cap", lambda shards: 8 * gib):
            self.assertEqual(check.test_limits(6, 4, 15 * gib)[0], 1, "at least one test thread")

class Leftovers(unittest.TestCase):
    def test_only_the_shards_worktrees_go(self):
        listed = "\n".join([
            "worktree /repo", "HEAD a", "",
            "worktree /tmpdir/blake3-servil-mutants/mutants-abc123", "HEAD b", "",
            "worktree /elsewhere/mutants-xyz", "HEAD c", "",
            "worktree /repo/tmp/tests-map-worktree", "HEAD d", "",
        ])
        calls = []
        def run(args, **kw):
            calls.append(args)
            return subprocess.CompletedProcess(args, 0, stdout=listed if "list" in args else "")
        with patch.object(check, "ROOT", "/repo"), patch.object(check, "WORKTREES", "/tmpdir/blake3-servil-mutants"), \
             patch.object(check, "TARGET_DIR", "/tmpdir/target"), patch.object(check.os.path, "realpath", lambda p: p), \
             patch.object(check.subprocess, "run", run), patch.object(check.shutil, "rmtree", lambda *a, **k: None), \
             patch.object(check.os, "makedirs", lambda *a, **k: None):
            check.remove_leftovers()
        removed = [a[-1] for a in calls if "remove" in a]
        self.assertEqual(removed, ["/tmpdir/blake3-servil-mutants/mutants-abc123"], "every other worktree stays")


if __name__ == "__main__":
    unittest.main()
