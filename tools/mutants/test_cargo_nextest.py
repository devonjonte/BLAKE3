"""Unit tests for tools/mutants/cargo-nextest fast-fail phase ordering."""

import importlib.machinery
import importlib.util
import os
import subprocess
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
SHIM_PATH = os.path.join(HERE, "cargo-nextest")
spec = importlib.util.spec_from_loader("cargo_nextest_shim", importlib.machinery.SourceFileLoader("cargo_nextest_shim", SHIM_PATH))
shim = importlib.util.module_from_spec(spec)
spec.loader.exec_module(shim)


class FastLibOrdering(unittest.TestCase):
    BASE_ARGS = ["nextest", "run", "--cargo-profile=mutants", "--lib", "--tests"]

    def test_lib_failure_short_circuits_before_integration_tests(self):
        ran, execed = [], []

        def run_cmd(cmd, stdout=None):
            ran.append((cmd, stdout))
            return 100

        rc = shim.dispatch(self.BASE_ARGS, {"MUTANTS_FAST_LIB": "1"}, "/real/nextest", run_cmd, execed.append)
        self.assertEqual(rc, 100)
        self.assertEqual(execed, [])
        self.assertEqual(len(ran), 1)
        self.assertIn("--lib", ran[0][0])
        self.assertNotIn("--tests", ran[0][0])
        self.assertIn("--no-tests=pass", ran[0][0])

    def test_lib_pass_proceeds_to_integration_tests(self):
        ran, execed = [], []
        codes = iter([0, 0])

        def run_cmd(cmd, stdout=None):
            ran.append((cmd, stdout))
            return next(codes)

        rc = shim.dispatch(self.BASE_ARGS, {"MUTANTS_FAST_LIB": "1"}, "/real/nextest", run_cmd, execed.append)
        self.assertEqual(rc, 0)
        self.assertEqual(execed, [])
        self.assertEqual(len(ran), 2)
        self.assertIn("--lib", ran[0][0])
        self.assertNotIn("--tests", ran[0][0])
        self.assertIn("--tests", ran[1][0])
        self.assertNotIn("--lib", ran[1][0])

    def test_same_code_lists_all_binaries_before_lib_phase(self):
        ran, execed = [], []
        codes = iter([0, 99])

        def run_cmd(cmd, stdout=None):
            ran.append((cmd, stdout))
            return next(codes)

        env = {"MUTANTS_FAST_LIB": "1", "MUTANTS_SAME_CODE": "/tmp/sc"}
        rc = shim.dispatch(self.BASE_ARGS, env, "/real/nextest", run_cmd, execed.append)
        self.assertEqual(rc, 99)
        self.assertEqual(len(ran), 2)
        self.assertEqual(ran[0], (["/real/nextest", "nextest", "list", "--cargo-profile=mutants", "--lib", "--tests"], subprocess.DEVNULL))
        self.assertIn("--lib", ran[1][0])

    def test_reach_filter_applies_to_both_phases(self):
        ran, execed = [], []

        def run_cmd(cmd, stdout=None):
            ran.append(cmd)
            return 0

        env = {"MUTANTS_FAST_LIB": "1", "MUTANTS_REACH": "1"}
        rc = shim.dispatch(self.BASE_ARGS, env, "/real/nextest", run_cmd, execed.append, narrow_fn=lambda _: "test(=foo)")
        self.assertEqual(rc, 0)
        self.assertEqual(len(ran), 2)
        for cmd in ran:
            self.assertIn("-E", cmd)
            self.assertIn("test(=foo)", cmd)
            self.assertIn("--no-tests=pass", cmd)

    def test_no_run_passes_straight_through(self):
        ran, execed = [], []
        args = ["nextest", "run", "--no-run", "--cargo-profile=mutants", "--lib", "--tests"]
        shim.dispatch(args, {"MUTANTS_FAST_LIB": "1"}, "/real/nextest", ran.append, execed.append)
        self.assertEqual(ran, [])
        self.assertEqual(execed, [["/real/nextest", *args]])


if __name__ == "__main__":
    unittest.main()
