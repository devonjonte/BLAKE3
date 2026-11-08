"""The long-proof cache keys checked inputs and preserves their evidence.

Exercise the script's actual key expression on real committed trees. No proof,
GitHub status, credential, or compiler is needed for these cache-identity tests.
"""
import os
from pathlib import Path
import re
import subprocess
import tempfile
import unittest

SCRIPT = Path(os.environ.get("LONG_PROOFS_SCRIPT", Path(__file__).with_name("long-proofs.sh")))


class LongProofInputs(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="long-proof-inputs-")
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.driver = SCRIPT.resolve()
        text = self.driver.read_text()
        expressions = [line for line in text.splitlines() if line.startswith("inputs=$(")]
        self.assertEqual(len(expressions), 1, "one production cache-key expression")
        self.expression = expressions[0]
        generation = [line for line in text.splitlines() if line.startswith("run generated ")]
        self.assertEqual(len(generation), 1, "one generation-agreement command")
        self.generators = sorted(set(re.findall(r"python3 (tools/gen_[A-Za-z0-9_]+\.py)", generation[0])))
        self.assertTrue(self.generators, "the generation-agreement command names its generators")
        self.git("init", "-q", "--initial-branch=main")
        self.inputs = ["c/kernel.S", "c2sp/BLAKE3/spec", "tools/verify/model.py", "tools/verify/long-proofs.sh"]
        for name in self.inputs + self.generators + ["README.md"]:
            path = self.root / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text("original\n")
        self.commit()

    def git(self, *args):
        return subprocess.check_output(["git", "-C", str(self.root), "-c", "core.hooksPath=/dev/null",
                                        "-c", "user.name=Proof Cache Test", "-c", "user.email=cache@example.invalid",
                                        "-c", "commit.gpgsign=false", *args], text=True).strip()

    def commit(self):
        self.git("add", ".")
        self.git("commit", "-qm", "fixture")
        return self.git("rev-parse", "HEAD")

    def key(self):
        command = 'root="$1"; commit="$2"\n' + self.expression + '\nprintf "%s" "$inputs"\n'
        return subprocess.check_output(["sh", "-c", command, str(self.driver), str(self.root),
                                        self.git("rev-parse", "HEAD")], text=True)

    def test_each_checked_generator_invalidates_the_cache_key(self):
        for generator in self.generators:
            before = self.key()
            with (self.root / generator).open("a") as f:
                f.write("changed generator\n")
            self.commit()
            with self.subTest(generator=generator):
                self.assertNotEqual(self.key(), before, f"{generator}: cached success must be invalidated")

    def test_kernel_specification_and_proof_tools_invalidate_the_cache_key(self):
        for name in self.inputs:
            before = self.key()
            with (self.root / name).open("a") as f:
                f.write("changed proof input\n")
            self.commit()
            with self.subTest(path=name):
                self.assertNotEqual(self.key(), before)

    def test_caller_verification_changes_invalidate_but_relocation_keeps_the_key(self):
        source = SCRIPT.read_text()
        verification = "run helpers python3 -m unittest discover -s tools/verify -p 'test_*.py'"
        self.assertEqual(source.count(verification), 1)
        commit = self.git("rev-parse", "HEAD")
        first = self.root / "caller with spaces.sh"
        second = self.root / "relocated-caller.sh"
        first.write_text(source)
        second.write_text(source)
        self.driver = first
        before = self.key()
        self.driver = second
        self.assertEqual(self.key(), before, "relocation preserves identical verification inputs")
        second.write_text(source.replace(verification, "run helpers sh -c 'exit 1'"))
        self.assertEqual(self.git("rev-parse", "HEAD"), commit, "target commit stays unchanged")
        self.assertNotEqual(self.key(), before, "changed caller verification must invalidate cached success")

    def test_log_destinations_and_cache_lookup_preserve_each_input(self):
        source = SCRIPT.read_text()
        assignments = [line for line in source.splitlines() if line.startswith("logs=")]
        self.assertEqual(len(assignments), 1)
        commit = self.git("rev-parse", "HEAD")
        before = self.key()
        caller = self.root / "changed-caller.sh"
        caller.write_text(source + "\n# another caller\n")
        self.driver = caller
        after = self.key()
        self.assertNotEqual(before, after)

        def log_path(key):
            command = 'root="$1"; commit="$2"; inputs="$3"\n' + assignments[0] + '\nprintf "%s" "$logs"\n'
            return Path(subprocess.check_output(["sh", "-eu", "-c", command, str(caller),
                                                 str(self.root), commit, key], text=True))

        first, second = log_path(before), log_path(after)
        self.assertNotEqual(first, second, "different caller inputs keep distinct evidence")
        for path, contents in [(first, "prior evidence"), (second, "new evidence")]:
            path.mkdir(parents=True)
            (path / "proof.txt").write_text(contents)
        self.assertEqual((first / "proof.txt").read_text(), "prior evidence")
        (self.root / "README.md").write_text("new target, same proof inputs\n")
        current = self.commit()
        self.assertEqual(self.key(), after, "new target retains the same proof inputs")
        start = source.index('if [ -f "$record" ]; then\n')
        block = source[start:source.index('\nfi\n', start) + len('\nfi\n')]
        b64 = [line for line in source.splitlines() if line.startswith("b64()")]
        self.assertEqual(len(b64), 1)
        record = self.root / "cached-record"
        record.write_text(commit + "\n" + "a" * 64 + "\n" + "b" * 64 + "\n")
        command = 'root="$1"; commit="$2"; inputs="$3"; record="$4"\n' + b64[0] + '\nstatus() { :; }\n' + block
        for key, expected in [(before, first), (after, second)]:
            output = subprocess.check_output(["sh", "-eu", "-c", command, str(caller),
                                              str(self.root), current, key, str(record)], text=True)
            self.assertIn(str(expected), output, "cache hit names the retained input-specific logs")

    def test_identical_inputs_and_unrelated_documentation_keep_the_cache_key(self):
        before = self.key()
        self.assertEqual(self.key(), before)
        (self.root / "README.md").write_text("documentation only\n")
        self.commit()
        self.assertEqual(self.key(), before, "unrelated changes retain the prior proof evidence")


if __name__ == "__main__":
    unittest.main()
