import Arm64
import ProofLib
import KernelAttr
open Arm64 ProofLib

/-! # Lemmas the compiler's proofs of kernels use, over Google's proof library (not to be read) -/

/-- Eight turns of a loop that never stops early, written out (their vector permutes are such loops). -/
theorem forIn_range8_yield {β : Type} (init : β) (g : Nat → β → β) :
    (forIn (m := Id) [:8] init (fun i s => pure (ForInStep.yield (g i s)))) =
      pure (g 7 (g 6 (g 5 (g 4 (g 3 (g 2 (g 1 (g 0 init)))))))) := by
  simp [List.range']

/-- Sixteen turns of such a loop (their table lookup, `tbl`, is one). -/
theorem forIn_range16_yield {β : Type} (init : β) (g : Nat → β → β) :
    (forIn (m := Id) [:16] init (fun i s => pure (ForInStep.yield (g i s)))) =
      pure (g 15 (g 14 (g 13 (g 12 (g 11 (g 10 (g 9 (g 8 (g 7 (g 6 (g 5 (g 4 (g 3 (g 2 (g 1 (g 0 init)))))))))))))))) := by
  simp [List.range']

/-! Their `tbl` takes an index as a natural number: which table register (`index / 16`) and which byte of
it (`index % 16`). These three say the same in bit-vector terms, the form the bit-blaster takes. -/

theorem tbl_lt (x : BitVec 128) : (x.toNat < 16) = (x < 16#128) := by
  simp [BitVec.lt_def]

theorem tbl_reg (x : BitVec 128) : BitVec.ofNat 5 (x.toNat / 16) = (x >>> 4).setWidth 5 := by
  rw [← BitVec.ofNat_toNat, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem tbl_shift (t x : BitVec 128) : t >>> (x.toNat % 16 * 8) = t >>> ((x &&& 15#128) <<< 3) := by
  rw [BitVec.ushiftRight_eq' t ((x &&& 15#128) <<< 3)]
  congr 1
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_and]
  have : (15#128).toNat = 2 ^ 4 - 1 := by decide
  rw [this, Nat.and_two_pow_sub_one_eq_mod]
  omega

/-- The spatial context may be replaced by an equal one: by the specification's, which leaves the
equalities of values as goals (their `wp_done` closes only those it can, and hands none back). -/
theorem SepWP.of_eq {prog : Program} {target_pc : BitVec 64} {s : State} {P P' : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (h : P = P') (hw : SepWP prog target_pc s P' post oom) : SepWP prog target_pc s P post oom := h ▸ hw
