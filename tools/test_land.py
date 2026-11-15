"""tools/land.py's pure parts: which gates a change needs, and how a
commit's statuses and check runs read as gates."""

import os
import sys
import unittest

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import land


class Gates(unittest.TestCase):
    def test_documents_alone_need_no_gate(self):
        self.assertEqual(land.required(["AGENTS.md", "docs/core-api.md"]), ())

    def test_code_needs_every_gate_and_proof_inputs_the_proofs(self):
        code = land.required(["src/lib.rs", "README.md"])
        self.assertEqual(code, ("CI", "check-builds", "mutants x86_64", "mutants aarch64", "mutants arm64", "tests aarch64", "tests arm64", "cells"))
        for path in ("c/blake3_neon_hybrid_aarch64.S", "tools/verify/canon.py", "tools/gen_neon_hybrid.py", "c2sp/BLAKE3/Blake3.lean"):
            self.assertEqual(land.required([path]), code + ("long proofs",), path)
        self.assertEqual(land.required(["tools/land.py"]), code, "a tool is code")

    def test_the_newest_status_of_a_gate_stands(self):
        statuses = [{"context": "cells", "state": "success", "description": "new"}, {"context": "cells", "state": "failure", "description": "old"}]
        self.assertEqual(land.verdicts(statuses, [])["cells"], ("success", "new"))

    def test_ci_is_green_only_when_every_job_is(self):
        run = lambda *c: [{"conclusion": x} for x in c]
        self.assertNotIn("CI", land.verdicts([], []), "no job has run: the gate is missing")
        self.assertEqual(land.verdicts([], run("success", "success"))["CI"][0], "success")
        self.assertEqual(land.verdicts([], run("success", "failure"))["CI"][0], "failure")
        self.assertEqual(land.verdicts([], run("success", None))["CI"][0], "pending")
        self.assertEqual(land.verdicts([], run("success", "cancelled"))["CI"][0], "failure")


if __name__ == "__main__":
    unittest.main()
