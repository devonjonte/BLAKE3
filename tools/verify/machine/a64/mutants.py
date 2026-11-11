#!/usr/bin/env python3
"""Does the AArch64 proof notice a changed instruction? Each mutant changes one word of the program
(and the listing line beside it, so the decoder agrees) and the build must fail."""
import pathlib, shutil, subprocess, sys, tempfile, time
here = pathlib.Path(__file__).resolve().parent
MUTANTS = [
    ("0x4AC26D22", "0x4AC26922", ".eor32ror .x2 .x9 .x2 27", ".eor32ror .x2 .x9 .x2 26"),
    ("0xB8004402", "0xB8008402", ".str32post .x2 .x0 4", ".str32post .x2 .x0 8"),
    ("0xF1001108", "0xF1002108", ".subs .x8 .x8 4", ".subs .x8 .x8 8"),
    ("0xD37EF428", "0xD37DF028", ".lsl .x8 .x1 2", ".lsl .x8 .x1 3"),
    ("0x54FFFF81", "0x54FFFFA1", ".bne 0x1008", ".bne 0x100C"),
    ("0xB9400009", "0xB9400409", ".ldr32 .x9 .x0 0", ".ldr32 .x9 .x0 4"),
    ("0xAA0203E0", "0xAA0103E0", ".mov .x0 .x2", ".mov .x0 .x1"),
    ("0xB40000E1", "0xB4000101", ".cbz .x1 0x101C", ".cbz .x1 0x1020"),
]
work = pathlib.Path(tempfile.mkdtemp(prefix="a64-mutants-"))
for f in ["A64.lean", "Code.lean", "Mem.lean", "Scan.lean", "lakefile.toml", "lean-toolchain"]:
    shutil.copy(here / f, work / f)
original = (work / "Code.lean").read_text()
def build():
    return subprocess.run(["lake", "build"], cwd=work, capture_output=True, text=True)
assert build().returncode == 0, "the unchanged proof must build"
rejected = 0
for w0, w1, i0, i1 in MUTANTS:
    assert original.count(w0) == 1 and original.count(f"some ({i0})") == 1, (w0, i0)
    (work / "Code.lean").write_text(original.replace(w0, w1).replace(f"some ({i0})", f"some ({i1})"))
    t = time.time(); r = build()
    listing_ok = "Code.lean" not in (r.stdout + r.stderr).split("Scan.lean")[0] if r.returncode else True
    verdict = "ACCEPTED" if r.returncode == 0 else ("rejected" if listing_ok else "rejected at the listing (the mutant is malformed)")
    rejected += r.returncode != 0 and listing_ok
    print(f"{verdict}\t{time.time()-t:.1f}s\t{i0} -> {i1}", flush=True)
(work / "Code.lean").write_text(original)
shutil.rmtree(work)
print(f"{rejected} of {len(MUTANTS)} rejected")
sys.exit(0 if rejected == len(MUTANTS) else 1)
