#!/usr/bin/env python3
"""Do the theorems about `push` on AArch64 notice changed code, or a statement that says something false?
Each change is made in a copy of Proof_push_arm.lean and PushBytes.lean (one file), which Lean must then
refuse. The control: the unchanged copy, checked afresh, must be accepted.

  - code: each instruction in turn becomes `mov x16, x16`, which does nothing. A change Lean accepts is an
    instruction the contract does not need.
  - statement: the contract claimed is changed to a false one.

usage: mutants_push.py"""
import pathlib, re, subprocess, sys, tempfile, time

here = pathlib.Path(__file__).resolve().parent
proof = (here / "Proof_push_arm.lean").read_text()
rest = (here / "PushBytes.lean").read_text()
assert "import Proof_push_arm\n" in rest
imports = [l for l in rest.split("\n") if l.startswith("import ") and l != "import Proof_push_arm"]
body = "\n".join(l for l in rest.split("\n") if not l.startswith("import ") and l != "open Arm64 ProofLib")
head = "\n".join(l for l in proof.split("\n") if l.startswith("import "))
proof_body = "\n".join(l for l in proof.split("\n") if not l.startswith("import "))
TEXT = head + "\n" + "\n".join(i for i in imports if i not in head.split("\n")) + "\n" + proof_body + "\n" + body
words = re.search(r'\.ofFn "b3l_push"\s*"([0-9a-f ]+)"', proof).group(1)
NOTHING = "aa1003f0"      # mov x16, x16

STATEMENTS = [
    ("the stack is said to be left as it was", "⌜Stack.Holds b' (x.new :: x.cvs)⌝", "⌜Stack.Holds b' x.cvs⌝", 1),
    ("a stack of 55 values is said to take one more", "x.cvs.length < 55 ∧ Stack.Holds x.b x.cvs", "x.cvs.length < 56 ∧ Stack.Holds x.b x.cvs", 1),
    ("the arguments are said to be the other way round",
     "prog.subroutineOk \"b3l_push\" (ArmAbi.spec (Push.byteContract st cv new cvs))",
     "prog.subroutineOk \"b3l_push\" (ArmAbi.spec (Push.byteContract cv st new cvs))", 1),
    ("the value is said to be pushed twice",
     "prog.subroutineOk \"b3l_push\" (ArmAbi.spec (Push.byteContract st cv new cvs))",
     "prog.subroutineOk \"b3l_push\" (ArmAbi.spec (Push.byteContract st cv new (new :: cvs)))", 1),
    ("the count is said to be at byte 8", "(st ↦ₛ hdr) ∗ ((st + 32#64 + (BitVec.ofNat 64 n <<< 5)) ↦ₛ mid)",
     "((st + 8#64) ↦ₛ hdr) ∗ ((st + 32#64 + (BitVec.ofNat 64 n <<< 5)) ↦ₛ mid)", 1),
]


def check(text):
    with tempfile.NamedTemporaryFile("w", suffix=".lean", dir=here, delete=False) as f:
        f.write(text)
        path = f.name
    try:
        start = time.time()
        try:
            r = subprocess.run(["lake", "env", "lean", path], cwd=here, capture_output=True, text=True, timeout=600)
        except subprocess.TimeoutExpired:
            return False, time.time() - start
        out = r.stdout + r.stderr
        return r.returncode == 0 and "error" not in out and "sorryAx" not in out, time.time() - start
    finally:
        pathlib.Path(path).unlink(missing_ok=True)


ok, secs = check(TEXT)
print(f"control: the unchanged files are {'ACCEPTED' if ok else 'REJECTED'} in {secs:.1f} s", flush=True)
if not ok:
    sys.exit("the control failed: the audit proves nothing")
tally = {}
ws = words.split()
for i, w in enumerate(ws):
    changed = " ".join(ws[:i] + [NOTHING] + ws[i + 1:])
    assert TEXT.count(words) == 1
    verdict = "ACCEPTED" if check(TEXT.replace(words, changed))[0] else "rejected"
    tally[verdict] = tally.get(verdict, 0) + 1
    print(f"{verdict}\tinstruction {i + 1} of {len(ws)} ({w}) does nothing", flush=True)
print(f"{len(ws)} instructions: " + ", ".join(f"{n} {k}" for k, n in sorted(tally.items())), flush=True)
code_ok = set(tally) == {"rejected"}
tally = {}
for what, old, new, n in STATEMENTS:
    verdict = "MALFORMED" if TEXT.count(old) != n else ("ACCEPTED" if check(TEXT.replace(old, new))[0] else "rejected")
    tally[verdict] = tally.get(verdict, 0) + 1
    print(f"{verdict}\t{what}", flush=True)
print(f"{len(STATEMENTS)} false statements: " + ", ".join(f"{n} {k}" for k, n in sorted(tally.items())))
sys.exit(0 if code_ok and set(tally) == {"rejected"} else 1)
