import Arm64
import ProofLib
import HexText
open Arm64 ProofLib

/-! # The NEON `hex` kernel on Google DeepMind's AArch64 model

`hex_neon.S` (32 instructions: no table, no branch) writes the 64 hexadecimal characters of the 32 bytes at
X1 to X0. Here its 32 words are proved, on the model of `google-deepmind/code-verification` (`Arm64`: the
decoder from the words, the semantics, the statement vocabulary; `ProofLib`: their program logic and
tactics), unchanged, to meet `hexSpec`: **`hex_neon_ok`**: in any program that holds these words at the
symbol, a call with the hash at X1 and 64 writable bytes at X0 returns to the caller, the stack pointer and
the callee-saved registers as they were, the hash unchanged, and the 64 bytes the hexadecimal; whatever
else is in memory is as it was (the frame `R` of `subroutine_ok`).

The values are stated here in 16-byte vectors (`↦₁₂₈`); `HexNeonBytes.lean` gives the statement in bytes
(`Hex.text`, the words used on x86-64). Their model has no observer of time or cache, so nothing is said
here of what the hash's value shows. Axioms: Lean's three and eight of `bv_decide`. -/

set_option maxRecDepth 200000

namespace Hex

/-- Byte `i` of a vector. -/
def byte (v : BitVec 128) (i : Nat) : BitVec 8 := v.extractLsb' (8 * i) 8

/-- The sixteen characters of bytes `k` to `k + 7` of `v`, as a vector whose lowest byte is the first. -/
def hex16 (v : BitVec 128) (k : Nat) : BitVec 128 :=
  char (byte v (k + 7) &&& 15#8) ++ char (byte v (k + 7) >>> 4) ++ char (byte v (k + 6) &&& 15#8) ++ char (byte v (k + 6) >>> 4) ++
  char (byte v (k + 5) &&& 15#8) ++ char (byte v (k + 5) >>> 4) ++ char (byte v (k + 4) &&& 15#8) ++ char (byte v (k + 4) >>> 4) ++
  char (byte v (k + 3) &&& 15#8) ++ char (byte v (k + 3) >>> 4) ++ char (byte v (k + 2) &&& 15#8) ++ char (byte v (k + 2) >>> 4) ++
  char (byte v (k + 1) &&& 15#8) ++ char (byte v (k + 1) >>> 4) ++ char (byte v k &&& 15#8) ++ char (byte v k >>> 4)

end Hex

structure HexArgs where
  out : BitVec 64
  inp : BitVec 64
  h0 : BitVec 128
  h1 : BitVec 128
  d0 : BitVec 128
  d1 : BitVec 128
  d2 : BitVec 128
  d3 : BitVec 128

abbrev hexSpec : Spec HexArgs where
  pre := fun x s0 =>
    ⌜s0.readReg64 .x0 = x.out ∧ s0.readReg64 .x1 = x.inp⌝ ∗
    (x.inp ↦₁₂₈ x.h0) ∗ ((x.inp + 16#64) ↦₁₂₈ x.h1) ∗
    (x.out ↦₁₂₈ x.d0) ∗ ((x.out + 16#64) ↦₁₂₈ x.d1) ∗ ((x.out + 32#64) ↦₁₂₈ x.d2) ∗ ((x.out + 48#64) ↦₁₂₈ x.d3)
  post := fun x _ _ =>
    (x.inp ↦₁₂₈ x.h0) ∗ ((x.inp + 16#64) ↦₁₂₈ x.h1) ∗
    (x.out ↦₁₂₈ Hex.hex16 x.h0 0) ∗ ((x.out + 16#64) ↦₁₂₈ Hex.hex16 x.h0 8) ∗
    ((x.out + 32#64) ↦₁₂₈ Hex.hex16 x.h1 0) ∗ ((x.out + 48#64) ↦₁₂₈ Hex.hex16 x.h1 8)

def hexCode : FnCode :=
  .ofFn "b3l_hex_neon"
    "ad400420 4f00e5e4 4f00e525 4f01e4e6 4f01e607 6f0c0402 4e241c00 6f0c0423 4e241c21 4e003850 4e007851 4e013872 4e017873 6e253600 6e253621 6e253642 6e253663 4e261c00 4e261c21 4e261c42 4e261c63 4e278610 4e278631 4e278652 4e278673 4e208610 4e218631 4e228652 4e238673 ad004410 ad014c12 d65f03c0"

/-- Eight turns of a loop that never stops early, written out. -/
theorem forIn_range8_yield {β : Type} (init : β) (g : Nat → β → β) :
    (forIn (m := Id) [:8] init (fun i s => pure (ForInStep.yield (g i s)))) =
      pure (g 7 (g 6 (g 5 (g 4 (g 3 (g 2 (g 1 (g 0 init)))))))) := by
  simp [List.range']

theorem Hex.char_bif (n : BitVec 8) : Hex.char n = bif n.ult 10#8 then n + 0x30#8 else n + 0x57#8 := by
  simp only [Hex.char]
  bv_decide

theorem SepWP.of_eq {prog : Program} {target_pc : BitVec 64} {s : State} {P P' : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (h : P = P') (hw : SepWP prog target_pc s P' post oom) : SepWP prog target_pc s P post oom := h ▸ hw

set_option maxHeartbeats 4000000 in
theorem hex_neon_ok (prog : Program) (h_code : hexCode.holds prog) :
    prog.subroutineOk "b3l_hex_neon" hexSpec := by
  wp_init x s0
  simp only [pointsTo128] at hpre ⊢
  wp_steps
  refine SepWP.of_eq (P' :=
    (x.inp ↦₆₄ BitVec.extractLsb' 0 64 x.h0 ∗ (x.inp + 8#64) ↦₆₄ BitVec.extractLsb' 64 64 x.h0) ∗
    ((x.inp + 16#64) ↦₆₄ BitVec.extractLsb' 0 64 x.h1 ∗ (x.inp + 16#64 + 8#64) ↦₆₄ BitVec.extractLsb' 64 64 x.h1) ∗
    (x.out ↦₆₄ BitVec.extractLsb' 0 64 (Hex.hex16 x.h0 0) ∗ (x.out + 8#64) ↦₆₄ BitVec.extractLsb' 64 64 (Hex.hex16 x.h0 0)) ∗
    ((x.out + 16#64) ↦₆₄ BitVec.extractLsb' 0 64 (Hex.hex16 x.h0 8) ∗ (x.out + 16#64 + 8#64) ↦₆₄ BitVec.extractLsb' 64 64 (Hex.hex16 x.h0 8)) ∗
    ((x.out + 32#64) ↦₆₄ BitVec.extractLsb' 0 64 (Hex.hex16 x.h1 0) ∗ (x.out + 32#64 + 8#64) ↦₆₄ BitVec.extractLsb' 64 64 (Hex.hex16 x.h1 0)) ∗
    ((x.out + 48#64) ↦₆₄ BitVec.extractLsb' 0 64 (Hex.hex16 x.h1 8) ∗ (x.out + 48#64 + 8#64) ↦₆₄ BitVec.extractLsb' 64 64 (Hex.hex16 x.h1 8))) ?values ?rest
  case values =>
    repeat' (first | with_reducible rfl | apply sepConj_congr | apply pointsTo64_congr_val)
    all_goals (
      simp only [forIn_range8_yield, bind_pure, Id.run_pure, Hex.hex16, Hex.byte, Hex.char_bif,
        Nat.reduceMul, Nat.reduceAdd]
      generalize x.h0 = h0
      generalize x.h1 = h1
      bv_decide)
  case rest =>
    wp_done

#print axioms hex_neon_ok
