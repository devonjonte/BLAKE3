"""The long-proof command's exit status, using its actual shell fragments.

Exercise the runner and final verdict without invoking proofs or GitHub.
"""

from pathlib import Path
import subprocess
import tempfile
import unittest


class LongProofExit(unittest.TestCase):
    def test_success_and_failure(self):
        source = Path(__file__).with_name("long-proofs.sh").read_text()
        start = source.index("verdict=passed state=success\n")
        stop = source.index("run lean_spec ", start)
        finish = source[source.rindex('echo "long proofs '):]
        script = source[start:stop] + '\nrun control "$1"\n' + finish
        with tempfile.TemporaryDirectory() as logs:
            for command, expected, verdict in (("true", 0, "passed"), ("false", 1, "FAILED (control)")):
                with self.subTest(command=command):
                    result = subprocess.run(
                        ["sh", "-eu", "-c", script, "sh", command],
                        env={"PATH": "/usr/bin:/bin", "logs": logs, "commit": "control", "sha": "", "b3": ""},
                        capture_output=True, text=True, timeout=5,
                    )
                    self.assertEqual(result.returncode, expected, result.stderr)
                    self.assertIn("long proofs " + verdict, result.stdout)


if __name__ == "__main__":
    unittest.main()
