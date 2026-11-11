#!/usr/bin/env python3
"""Does the proof of the comparison notice a changed instruction? One instruction of Code.lean is
changed (its table row and its lemma alike) and the build must fail."""
import pathlib, shutil, subprocess, sys, tempfile
here = pathlib.Path(__file__).resolve().parent
FILES = ["Bytes.lean", "Attr.lean", "X86.lean", "Regions.lean", "Code.lean", "Eq.lean", "lakefile.toml", "lean-toolchain"]
MUTANTS = [
    (".loadv 1 (.mem .rdi 0x10)", ".loadv 1 (.mem .rdi 0x0)"),
    (".loadv 3 (.mem .rsi 0x10)", ".loadv 3 (.mem .rsi 0x0)"),
    (".loadv 2 (.mem .rsi 0x0)", ".loadv 2 (.mem .rdi 0x0)"),
    (".pcmpeqb 0 2", ".pcmpeqb 0 3"),
    (".pcmpeqb 1 3", ".pcmpeqb 1 1"),
    (".pand 0 1", ".pand 0 0"),
    (".pmovmskb .rax 0", ".pmovmskb .rax 1"),
    (".cmp 32 (.reg .rax) (.imm 0xFFFF)", ".cmp 32 (.reg .rax) (.imm 0x7FFF)"),
    (".cmp 32 (.reg .rax) (.imm 0xFFFF)", ".cmp 32 (.reg .rax) (.imm 0xFFFE)"),
    (".pop .rbp", ".pop .rbx"),
    (".push .rbp", ".push .rbx"),
]
src = (here / "Code.lean").read_text(); rejected = 0
for old, new in MUTANTS:
    assert src.count(old) == 2, old
    d = pathlib.Path(tempfile.mkdtemp(prefix="eq-mutant-"))
    for f in FILES: shutil.copy(here / f, d / f)
    (d / "Code.lean").write_text(src.replace(old, new))
    r = subprocess.run(["lake", "build", "Eq"], cwd=d, capture_output=True, text=True, timeout=900)
    bad = "error: Code.lean" in r.stdout + r.stderr
    shutil.rmtree(d)
    rejected += r.returncode != 0 and not bad
    print(("malformed" if bad else "rejected" if r.returncode else "ACCEPTED") + f"\t{old} -> {new}", flush=True)
print(f"{rejected} of {len(MUTANTS)} rejected")
sys.exit(0 if rejected == len(MUTANTS) else 1)
