#!/usr/bin/env python3
"""Does `hex_neon_quiet` / `hex_neon_observed` notice code that shows the hash, or a statement that says less?
Each change is made in a copy of HexNeonQuiet.lean, which Lean must then refuse. The control: the unchanged
copy, checked afresh, must be accepted. usage: mutants_quiet.py"""
import pathlib, subprocess, sys, tempfile, time

here = pathlib.Path(__file__).resolve().parent
TEXT = (here / "HexNeonQuiet.lean").read_text()

# (what, [(old, new, how many times)])
MUTANTS = [
    ("the code moves a byte of the hash to a general register (fmov x2, d0, in place of the first `and`)",
     [("0x4e241c00", "0x9e660002", 2),
      (".simdThreeSame true false 0x0#2 0x04#5 0x03#5 0x00#5 0x00#5", ".fmovGprVec true 0x1#2 0x0#2 0x6#3 0x00#5 0x02#5", 2)]),
    ("the code branches (cbz x1, in place of the first shift)",
     [("0x6f0c0402", "0xb4000041", 2),
      (".simdImmShift true true 0x1#4 0x4#3 0x00#5 0x00#5 0x02#5", ".cbz .W64 false (.gpr 0x01#5) 0x8#64", 2)]),
    ("the code loads a byte at an index (ldrb w3, [x1, x2], in place of the first zip)",
     [("0x4e003850", "0x38626823", 2),
      (".simdPermute true 0x0#2 0x00#5 0x3#3 0x02#5 0x10#5",
       ".ldr .W32 .B8 false (.gpr 0x03#5) (.RegOffset (.gpr 0x01#5) (.gpr 0x02#5) .UXTX 0)", 2)]),
    ("the statement lets the general registers differ",
     [("  regs : s.regs = s'.regs\n", "  regs : True\n", 1)]),
    ("the statement lets the two memories be mapped differently",
     [("  map : SameMap s.mem s'.mem\n", "  map : True\n", 1)]),
    ("the observer also sees a vector register's value (then the kernel does show the hash)",
     [("  | .simdThreeSame .. => some []\n",
       "  | .simdThreeSame _ _ _ rm _ _ _ => some [.read ((s.readVReg128 rm).truncate 64) 1]\n", 1)]),
    ("the observer has no account of the stores",
     [("  | .stpSimd sz _ _ addr => some [.write (evalAddrMode s addr).1 (2 * sz.bytes)]\n", "", 1)]),
]


def check(text):
    with tempfile.NamedTemporaryFile("w", suffix=".lean", dir=here, delete=False) as f:
        f.write(text)
        name = f.name
    try:
        start = time.time()
        r = subprocess.run(["lake", "env", "lean", name], cwd=here, capture_output=True, text=True, timeout=600)
        out = r.stdout + r.stderr
        ok = r.returncode == 0 and "error" not in out and "sorryAx" not in out
        return ok, time.time() - start
    finally:
        pathlib.Path(name).unlink(missing_ok=True)


ok, secs = check(TEXT)
print(f"control: the unchanged file is {'ACCEPTED' if ok else 'REJECTED'} in {secs:.1f} s", flush=True)
if not ok:
    sys.exit("the control failed: the audit proves nothing")
tally = {}
for what, edits in MUTANTS:
    text = TEXT
    bad = False
    for old, new, n in edits:
        if text.count(old) != n:
            bad = True
        text = text.replace(old, new)
    if bad:
        verdict = "MALFORMED"
    else:
        ok, secs = check(text)
        verdict = "ACCEPTED" if ok else "rejected"
    tally[verdict] = tally.get(verdict, 0) + 1
    print(f"{verdict}\t{what}", flush=True)
print(f"{len(MUTANTS)} changes: " + ", ".join(f"{n} {k}" for k, n in sorted(tally.items())))
sys.exit(0 if set(tally) == {"rejected"} else 1)
