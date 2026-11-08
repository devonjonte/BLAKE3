"""The long-proof command's exit status, using its actual shell fragments.

Exercise the runner and final verdict without invoking proofs or GitHub.
"""

from pathlib import Path
import subprocess
import tempfile
import unittest


class LongProofExit(unittest.TestCase):
    def test_temporary_and_lean_paths_respect_the_environment(self):
        import os
        source = Path(__file__).with_name("long-proofs.sh").read_text()
        tree = [line for line in source.splitlines() if line.startswith("tree=")]
        exports = [line for line in source.splitlines()
                   if line.startswith("export ELAN_HOME=") or line.startswith("export PATH=")]
        self.assertEqual(len(tree), 1)
        script = "\n".join(tree + exports) + '\nprintf "%s\n%s\n%s\n" "$tree" "$ELAN_HOME" "$PATH"\n'
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            scratch = root / "scratch space"
            scratch.mkdir()
            for explicit in (False, True):
                env = {"PATH": os.environ["PATH"], "HOME": str(root / "home"),
                       "TMPDIR": str(scratch), "commit": "control"}
                expected = root / "custom elan" if explicit else root / "home" / ".elan"
                if explicit:
                    env["ELAN_HOME"] = str(expected)
                result = subprocess.check_output(["sh", "-eu", "-c", script], env=env, text=True).splitlines()
                self.assertEqual(result[0], str(scratch / "long-proofs-control"))
                self.assertEqual(result[1], str(expected))
                self.assertEqual(result[2].split(":")[0], str(expected / "bin"))

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


class LongProofCarryOver(unittest.TestCase):
    def test_same_proof_inputs_are_not_rerun(self):
        import os
        import shutil
        import stat
        here = Path(__file__).parent
        with tempfile.TemporaryDirectory() as td:
            root = Path(td) / "repo"
            (root / "tools" / "verify").mkdir(parents=True)
            (root / "c").mkdir()
            (root / "c" / "kernel.S").write_text("kernel\n")
            (root / "tools" / "verify" / "long-proofs.sh").write_text(
                (here / "long-proofs.sh").read_text())
            (root / "ghtokenclassic.txt").write_text("token\n")
            (root / "fixture-id.txt").write_text(str(root))
            bin_dir = Path(td) / "bin"
            bin_dir.mkdir()
            curl_log = Path(td) / "curl.log"
            curl = bin_dir / "curl"
            curl.write_text(f"#!/bin/sh\ncat >> {curl_log}\n")
            curl.chmod(curl.stat().st_mode | stat.S_IEXEC)
            git = ["git", "-C", str(root), "-c", "user.email=t@t", "-c", "user.name=t"]
            subprocess.run(git + ["init", "-q"], check=True)
            subprocess.run(git + ["add", "-A"], check=True)
            subprocess.run(git + ["commit", "-q", "-m", "proof inputs"], check=True)
            prior = subprocess.check_output(git + ["rev-parse", "HEAD"], text=True).strip()
            script = root / "tools" / "verify" / "long-proofs.sh"
            expressions = [line for line in script.read_text().splitlines() if line.startswith("inputs=$(")]
            self.assertEqual(len(expressions), 1)
            command = 'root="$1"; commit="$2"\n' + expressions[0] + '\nprintf "%s" "$inputs"\n'
            fingerprint = subprocess.check_output(
                ["sh", "-eu", "-c", command, str(script), str(root), prior], text=True)
            record = root / "tmp" / "long-proofs" / "inputs" / (fingerprint + ".txt")
            record.parent.mkdir(parents=True)
            record.write_text(prior + "\n" + "a" * 64 + "\n" + "b" * 64 + "\n")
            (root / "README.md").write_text("docs only\n")
            subprocess.run(git + ["add", "-A"], check=True)
            subprocess.run(git + ["commit", "-q", "-m", "docs only"], check=True)
            commit = subprocess.check_output(git + ["rev-parse", "HEAD"], text=True).strip()
            tree = Path(tempfile.gettempdir()) / ("long-proofs-" + commit)
            self.assertFalse(tree.exists(), "fixture owns its unique possible worktree")
            self.addCleanup(shutil.rmtree, tree, ignore_errors=True)
            env = dict(os.environ, PATH=str(bin_dir) + ":" + os.environ["PATH"])
            result = subprocess.run(
                ["sh", "tools/verify/long-proofs.sh", commit], cwd=root, env=env,
                capture_output=True, text=True, timeout=30)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertIn("same proof inputs as " + prior + ", not rerun", result.stdout)
            self.assertIn('"state": "success"', curl_log.read_text())
            self.assertFalse(tree.exists())


if __name__ == "__main__":
    unittest.main()
