"""Every binary must be identical before a build may skip its tests.

These are verdict-logic controls. test_code_hash.py separately exercises the
ELF loaded-byte identity; here the hasher is explicit and records its calls.
"""
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import code_hash


class Verdict(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.state = Path(self.temp.name)
        self.names = ["blake3_servil-111", "aa_integration-222"]
        self.hashes = {name: "a" * 64 for name in self.names}
        for i, name in enumerate(self.names):
            (self.state / (name + ".path")).write_text(str(self.state / name) + "\n")
            stat = f"{100 + i} 1000.000000000 2048"
            (self.state / (name + ".stat")).write_text(stat + "\n")
            (self.state / (name + ".base")).write_text(stat + " " + self.hashes[name] + "\n")
        env = patch.dict(os.environ, MUTANTS_B3SUM="unused-logic-fixture")
        env.start()
        self.addCleanup(env.stop)
        hasher = patch.object(code_hash, "code_hash", side_effect=lambda path, _: self.hashes[Path(path).name])
        self.hasher = hasher.start()
        self.addCleanup(hasher.stop)

    def changed_metadata(self, i):
        (self.state / (self.names[i] + ".stat")).write_text(f"{200 + i} 1001.000000000 2048\n")

    def verdict(self):
        return code_hash.verdict(str(self.state))

    def test_first_build_hashes_and_records_every_binary(self):
        for name in self.names:
            (self.state / (name + ".base")).unlink()
        self.assertEqual(self.verdict(), "baseline")
        self.assertEqual([Path(c.args[0]).name for c in self.hasher.call_args_list], self.names)
        for name in self.names:
            self.assertTrue((self.state / (name + ".base")).read_text().endswith(" " + self.hashes[name] + "\n"))

    def test_the_unmodified_baseline_still_runs_tests(self):
        self.assertEqual(self.verdict(), "baseline")

    def test_unchanged_first_binary_does_not_hide_an_identical_relink(self):
        self.changed_metadata(1)
        self.assertEqual(self.verdict(), "same")
        self.assertEqual(self.hasher.call_count, 2)

    def test_unchanged_later_binary_does_not_hide_an_identical_relink(self):
        self.changed_metadata(0)
        self.assertEqual(self.verdict(), "same")
        self.assertEqual(self.hasher.call_count, 2)

    def test_unchanged_first_binary_does_not_hide_changed_loaded_bytes_later(self):
        self.changed_metadata(1)
        self.hashes[self.names[1]] = "b" * 64
        self.assertEqual(self.verdict(), "differs")

    def test_same_metadata_is_not_a_loaded_byte_proof(self):
        self.changed_metadata(1)
        self.hashes[self.names[0]] = "b" * 64
        self.assertEqual(self.verdict(), "differs")

    def test_the_common_changed_library_needs_only_one_hash(self):
        self.changed_metadata(0)
        self.hashes[self.names[0]] = "b" * 64
        self.assertEqual(self.verdict(), "differs")
        self.assertEqual([Path(c.args[0]).name for c in self.hasher.call_args_list], self.names[:1])


if __name__ == "__main__":
    unittest.main()
