import Arm64
import ProofLib
import PushCells
open Arm64 ProofLib

/-! # `push`, as printed for AArch64 and assembled, meets `pushCellsSpec`, on Google DeepMind's model

Written by `gen_fn_arm.py` from the assembled function's 18 instruction words. -/

set_option maxRecDepth 200000

def push_arm_code : FnCode :=
  .ofFn "b3l_push"
    "aa0003f0 f9400210 aa1003e9 aa0103f0 aa0003f1 d2800408 8b080231 aa0903e8 d37be908 8b080231 ad400600 ad000620 aa0903f0 d2800031 8b110210 aa0003f1 f9000230 d65f03c0"

set_option maxHeartbeats 4000000 in
theorem push_arm_ok (prog : Program) (h_code : push_arm_code.holds prog) :
    prog.subroutineOk "b3l_push" pushCellsSpec := by
  wp_init x s0
  simp only [pointsTo128] at hpre ⊢
  wp_steps
  wp_done

#print axioms push_arm_ok
