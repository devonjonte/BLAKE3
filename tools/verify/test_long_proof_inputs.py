"""The long-proof cache keys every checked generator, preserving unrelated reuse.

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
        text = SCRIPT.read_text()
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
        return subprocess.check_output(["sh", "-c", command, "cache-key-test", str(self.root),
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

    def test_identical_inputs_and_unrelated_documentation_keep_the_cache_key(self):
        before = self.key()
        self.assertEqual(self.key(), before)
        (self.root / "README.md").write_text("documentation only\n")
        self.commit()
        self.assertEqual(self.key(), before, "unrelated changes retain the prior proof evidence")


if __name__ == "__main__":
    unittest.main()
