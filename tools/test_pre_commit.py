"""The code-commit hook requires a completed performance verdict.

A fake git supplies a staged source change; fake cargo supplies each
verdict. No Rust code is built or timed by this control.
"""
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

HOOK = Path(__file__).resolve().parent / "git-hooks" / "pre-commit"


class PerformanceVerdicts(unittest.TestCase):
    def test_code_commit_requires_a_completed_verdict(self):
        with tempfile.TemporaryDirectory() as d:
            top = Path(d)
            bin_dir = top / "bin"
            bin_dir.mkdir()
            bench = top / "bench"
            bench.mkdir()
            (bench / "Cargo.toml").write_text("")
            scripts = {
                "git": '#!/bin/sh\ncase "$1" in diff) echo src/lib.rs;; rev-parse) echo "$HOOK_TEST_TOP";; *) exit 9;; esac\n',
                "cargo": '#!/bin/sh\nexit "$HOOK_TEST_VERDICT"\n',
            }
            for name, text in scripts.items():
                p = bin_dir / name
                p.write_text(text)
                p.chmod(0o755)
            for verdict in (0, 1, 2, 3):
                with self.subTest(verdict=verdict):
                    env = dict(os.environ, PATH=str(bin_dir) + os.pathsep + os.environ["PATH"],
                               BENCH_HASHES_DIR=str(bench), HOOK_TEST_TOP=str(top), HOOK_TEST_VERDICT=str(verdict))
                    result = subprocess.run(["sh", str(HOOK)], env=env, capture_output=True, text=True, check=False)
                    self.assertEqual(result.returncode == 0, verdict == 0, result.stdout + result.stderr)
                    if verdict == 2:
                        self.assertIn("verdict pending", result.stdout)


if __name__ == "__main__":
    unittest.main()
