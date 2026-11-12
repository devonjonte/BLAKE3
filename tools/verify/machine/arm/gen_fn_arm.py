#!/usr/bin/env python3
"""The compiler's proof for a word-level function printed for AArch64 (a trial: straight-line functions).

    gen_fn_arm.py NAME WORDS SPECFILE SPEC OUT.lean

NAME's instruction words (WORDS: a file of them, as the object holds them) are proved, on Google DeepMind's
model, to meet SPEC (a `Spec` of their logic in SPECFILE.lean): their tactics run the instructions and close
the proof. Nothing here is specific to the function."""
import sys
from pathlib import Path

name, wordfile, specfile, spec, out = sys.argv[1:6]
words = Path(wordfile).read_text().split()
text = f"""import Arm64
import ProofLib
import {specfile}
open Arm64 ProofLib

/-! # `{name}`, as printed for AArch64 and assembled, meets `{spec}`, on Google DeepMind's model

Written by `gen_fn_arm.py` from the assembled function's {len(words)} instruction words. -/

set_option maxRecDepth 200000

def {name}_arm_code : FnCode :=
  .ofFn "b3l_{name}"
    "{' '.join(words)}"

set_option maxHeartbeats 4000000 in
theorem {name}_arm_ok (prog : Program) (h_code : {name}_arm_code.holds prog) :
    prog.subroutineOk "b3l_{name}" {spec} := by
  wp_init x s0
  simp only [pointsTo128] at hpre ⊢
  wp_steps
  wp_done

#print axioms {name}_arm_ok
"""
with open(out, "w") as f:
    f.write(text)
print(f"{name}: {len(words)} instructions; wrote {out}")
