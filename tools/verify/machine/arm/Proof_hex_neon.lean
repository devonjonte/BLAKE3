import Arm64
import ProofLib
import WpKernel
import HexVec
open Arm64 ProofLib

/-! # `hex_neon` meets its contract, on Google DeepMind's AArch64 model

Written by `gen_arm.py` from the source's contract clauses and the assembled kernel's 27 words. To be
read: `hex_neon_spec` and the theorem's statement. `hex_neon_ok`: in any program holding these words at the
symbol, their `subroutineOk`: a call returns to its caller, the stack pointer and callee-saved registers
as they were, memory as the contract says and otherwise as it was. Their tactics run the instructions;
the values are settled by unfolding the specification (`kernel_spec`) and `bv_decide`. -/

set_option maxRecDepth 200000

structure hex_neon_args where
  dst : BitVec 64
  src : BitVec 64
  h0 : BitVec 128
  h1 : BitVec 128
  d0 : BitVec 128
  d1 : BitVec 128
  d2 : BitVec 128
  d3 : BitVec 128

/-- The contract's clauses: vectors read at `x1`, written at `x0`. -/
abbrev hex_neon_spec : Spec hex_neon_args where
  pre := fun x s0 =>
    ⌜s0.readReg64 .x0 = x.dst ∧ s0.readReg64 .x1 = x.src⌝ ∗
    (x.src ↦₁₂₈ x.h0) ∗
    ((x.src + 16#64) ↦₁₂₈ x.h1) ∗
    (x.dst ↦₁₂₈ x.d0) ∗
    ((x.dst + 16#64) ↦₁₂₈ x.d1) ∗
    ((x.dst + 32#64) ↦₁₂₈ x.d2) ∗
    ((x.dst + 48#64) ↦₁₂₈ x.d3)
  post := fun x _ _ =>
    (x.src ↦₁₂₈ x.h0) ∗
    ((x.src + 16#64) ↦₁₂₈ x.h1) ∗
    (x.dst ↦₁₂₈ (Hex.hex16 x.h0 0)) ∗
    ((x.dst + 16#64) ↦₁₂₈ (Hex.hex16 x.h0 8)) ∗
    ((x.dst + 32#64) ↦₁₂₈ (Hex.hex16 x.h1 0)) ∗
    ((x.dst + 48#64) ↦₁₂₈ (Hex.hex16 x.h1 8))

def hex_neon_code : FnCode :=
  .ofFn "b3l_hex_neon"
    "ad400420 d2862609 f2a66649 f2c6a689 f2e6e6c9 d287270a f2ac4c2a f2cc8c6a f2ecccaa 4e081d25 4e181d45 4f00e5e4 6f0c0402 4e241c00 6f0c0423 4e241c21 4e003850 4e007851 4e013872 4e017873 4e1000b0 4e1100b1 4e1200b2 4e1300b3 ad004410 ad014c12 d65f03c0"

set_option maxHeartbeats 40000000 in
theorem hex_neon_ok (prog : Program) (h_code : hex_neon_code.holds prog) :
    prog.subroutineOk "b3l_hex_neon" hex_neon_spec := by
  wp_init x s0
  simp only [pointsTo128] at hpre ⊢
  wp_steps
  refine SepWP.of_eq (P' :=
    (x.src ↦₆₄ BitVec.extractLsb' 0 64 x.h0 ∗ (x.src + 8#64) ↦₆₄ BitVec.extractLsb' 64 64 x.h0) ∗
    ((x.src + 16#64) ↦₆₄ BitVec.extractLsb' 0 64 x.h1 ∗ ((x.src + 16#64) + 8#64) ↦₆₄ BitVec.extractLsb' 64 64 x.h1) ∗
    (x.dst ↦₆₄ BitVec.extractLsb' 0 64 (Hex.hex16 x.h0 0) ∗ (x.dst + 8#64) ↦₆₄ BitVec.extractLsb' 64 64 (Hex.hex16 x.h0 0)) ∗
    ((x.dst + 16#64) ↦₆₄ BitVec.extractLsb' 0 64 (Hex.hex16 x.h0 8) ∗ ((x.dst + 16#64) + 8#64) ↦₆₄ BitVec.extractLsb' 64 64 (Hex.hex16 x.h0 8)) ∗
    ((x.dst + 32#64) ↦₆₄ BitVec.extractLsb' 0 64 (Hex.hex16 x.h1 0) ∗ ((x.dst + 32#64) + 8#64) ↦₆₄ BitVec.extractLsb' 64 64 (Hex.hex16 x.h1 0)) ∗
    ((x.dst + 48#64) ↦₆₄ BitVec.extractLsb' 0 64 (Hex.hex16 x.h1 8) ∗ ((x.dst + 48#64) + 8#64) ↦₆₄ BitVec.extractLsb' 64 64 (Hex.hex16 x.h1 8))) ?values ?rest
  case values =>
    repeat' (first | with_reducible rfl | apply sepConj_congr | apply pointsTo64_congr_val)
    all_goals (
      generalize x.h0 = h0
      generalize x.h1 = h1
      simp only [forIn_range8_yield, forIn_range16_yield, bind_pure, Id.run_pure, Nat.reduceMul, Nat.reduceAdd,
        tbl_lt, tbl_reg, tbl_shift, kernel_spec]
      bv_decide)
  case rest =>
    wp_done

#print axioms hex_neon_ok
