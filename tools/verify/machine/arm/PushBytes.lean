import Arm64
import ProofLib
import StackBytesLemmas
import PushContract
import ArmAbi
import HexNeonBytes
import Proof_push_arm
open Arm64 ProofLib

/-! # `push` on AArch64: the contract in the words of the x86-64 one

`Proof_push_arm.lean` (written by the compiler) proves the function against a statement about cells. Here
the same code meets the statement a reader wants: for bytes at `st` that hold a stack of fewer than 55
values (`Stack.Holds`, `../spec/StackBytes.lean`, which names no machine) and a chaining value's bytes at
`cv`: the bytes at `st` hold the stack with that value pushed; the value is unchanged. By their rule
`subroutine_ok_refine_frame`; the rest is bytes to cells and back. -/

set_option maxRecDepth 200000

structure PushArgs where
  st : BitVec 64
  cv : BitVec 64
  new : Blake3.CV
  cvs : List Blake3.CV
  b : List (BitVec 8)

/-- **`push(st, cv)` on AArch64.** -/
abbrev pushSpec : Spec PushArgs where
  pre := fun x s0 =>
    ⌜s0.readReg64 .x0 = x.st ∧ s0.readReg64 .x1 = x.cv ∧ x.cvs.length < 55 ∧ Stack.Holds x.b x.cvs⌝ ∗
    (x.st ↦ₛ x.b) ∗ (x.cv ↦ₛ Cv.bytes x.new)
  post := fun x _ _ =>
    (∃∗ b', ⌜Stack.Holds b' (x.new :: x.cvs)⌝ ∗ (x.st ↦ₛ b')) ∗ (x.cv ↦ₛ Cv.bytes x.new)

/-- The count's bytes are a 64-bit cell's. -/
theorem le64_unpack (n : Nat) : Bytes.le64 n = unpack64 (BitVec.ofNat 64 n) := rfl

/-- Two vectors' bytes in memory are two vectors in memory. -/
theorem vecs_bytes (a : BitVec 64) (v0 v1 : BitVec 128) :
    (a ↦ₛ (Hex.bytes16 v0 ++ Hex.bytes16 v1)) = ((a ↦₁₂₈ v0) ∗ ((a + 16#64) ↦₁₂₈ v1)) := by
  rw [pointsToBytes_append, pointsTo128_eq_bytes, pointsTo128_eq_bytes]
  rfl

/-- Where the next value goes, as the code computes it. -/
theorem slot_addr (st : BitVec 64) (n : Nat) :
    st + BitVec.ofNat 64 (32 + 32 * n) = st + 32#64 + (BitVec.ofNat 64 n <<< 5) := by
  rw [BitVec.add_assoc]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  omega

/-- The stack's bytes in memory, as the parts `push` touches and the parts it leaves. -/
theorem stack_parts (st : BitVec 64) (n : Nat) (hdr unused flat mid after : List (BitVec 8))
    (hh : hdr.length = 8) (hu : unused.length = 24) (hf : flat.length = 32 * n) (hm : mid.length = 32) :
    (st ↦ₛ (hdr ++ unused ++ flat ++ mid ++ after)) =
      ((st ↦ₛ hdr) ∗ ((st + 32#64 + (BitVec.ofNat 64 n <<< 5)) ↦ₛ mid) ∗
        (((st + 8#64) ↦ₛ unused) ∗ ((st + 32#64) ↦ₛ flat) ∗ ((st + BitVec.ofNat 64 (64 + 32 * n)) ↦ₛ after))) := by
  simp only [List.append_assoc]
  rw [pointsToBytes_append, hh,
    pointsToBytes_append_off st 8 32 unused _ (by omega),
    pointsToBytes_append_off st 32 (32 + 32 * n) flat _ (by omega),
    pointsToBytes_append_off st (32 + 32 * n) (64 + 32 * n) mid _ (by omega),
    slot_addr]
  sep_eq

theorem push_arm_bytes_ok (prog : Program) (h_code : push_arm_code.holds prog) :
    prog.subroutineOk "b3l_push" pushSpec := by
  refine subroutine_ok_refine_frame (push_arm_ok prog h_code) ?_
  intro y R s0 hp
  simp only [sepConj_assoc] at hp
  obtain ⟨⟨h0, h1, hl, hb⟩, hp⟩ := (satisfies_pure_sepConj _ _ _).1 hp
  obtain ⟨unused, slot, after, hu, hs, ha, eb⟩ := hb.room hl
  obtain ⟨n0, n1, en, -⟩ := bytes32_vecs y.cv (Cv.bytes y.new) (Cv.bytes_length _)
  obtain ⟨d0, d1, ed, -⟩ := bytes32_vecs y.st slot hs
  have hf : (y.cvs.reverse.flatMap Cv.bytes).length = 32 * y.cvs.length := by
    rw [Cv.bytes_flat_length, List.length_reverse]
  refine ⟨⟨y.st, y.cv, BitVec.ofNat 64 y.cvs.length, n0, n1, d0, d1⟩,
    ((y.st + 8#64) ↦ₛ unused) ∗ ((y.st + 32#64) ↦ₛ y.cvs.reverse.flatMap Cv.bytes) ∗
      ((y.st + BitVec.ofNat 64 (64 + 32 * y.cvs.length)) ↦ₛ after), ?_, ?_⟩
  · -- at the call: the bytes are the cells the code reads and writes, and the rest
    simp only [sepConj_assoc]
    refine (satisfies_pure_sepConj _ _ _).2 ⟨⟨h0, h1⟩, ?_⟩
    rw [eb, stack_parts y.st y.cvs.length _ unused _ slot after (Bytes.le64_length _) hu hf hs, ed, en,
      vecs_bytes, vecs_bytes, le64_unpack, ← pointsTo64_eq_pointsToBytes] at hp
    exact Satisfies.of_eq hp (by sep_eq)
  · -- at the return: the cells and the rest are the bytes of the stack with the value pushed
    intro sf hq
    simp only [sepConj_assoc] at hq
    show sf.mem ⊨ ((∃∗ b', ⌜Stack.Holds b' (y.new :: y.cvs)⌝ ∗ (y.st ↦ₛ b')) ∗ (y.cv ↦ₛ Cv.bytes y.new)) ∗ R
    rw [sepConj_assoc]
    refine Satisfies.sepExists_intro
      (Bytes.le64 (y.cvs.length + 1) ++ unused ++ y.cvs.reverse.flatMap Cv.bytes ++ Cv.bytes y.new ++ after) ?_
    rw [sepConj_assoc]
    refine (satisfies_pure_sepConj _ _ _).2 ⟨Stack.Holds.pushed y.new hl hu ha, ?_⟩
    rw [stack_parts y.st y.cvs.length _ unused _ (Cv.bytes y.new) after (Bytes.le64_length _) hu hf (Cv.bytes_length _),
      en, vecs_bytes, vecs_bytes, le64_unpack, ← pointsTo64_eq_pointsToBytes,
      show BitVec.ofNat 64 (y.cvs.length + 1) = BitVec.ofNat 64 y.cvs.length + 1#64 from BitVec.ofNat_add ..]
    exact Satisfies.of_eq hq (by sep_eq)

#print axioms push_arm_bytes_ok

/-! ## The contract that names no machine

`Push.byteContract` (`../spec/PushContract.lean`) is what the x86-64 code of the same source function is
proved to meet on our model (`../lang/Meets_push_bytes.lean`). Here the AArch64 code meets it, read for
AArch64 (`ArmAbi.spec`). -/

/-- **The AArch64 code of `push` meets `Push.byteContract`.** -/
theorem push_arm_meets (prog : Program) (h_code : push_arm_code.holds prog)
    (st cv : BitVec 64) (new : Blake3.CV) (cvs : List Blake3.CV) :
    prog.subroutineOk "b3l_push" (ArmAbi.spec (Push.byteContract st cv new cvs)) := by
  refine subroutine_ok_refine (push_arm_bytes_ok prog h_code) ?_
  intro r R s0 hp
  simp only [ArmAbi.spec, Push.byteContract, sepConj_assoc] at hp
  obtain ⟨⟨hargs, hacc, hrl, hr⟩, hp⟩ := (satisfies_pure_sepConj _ _ _).1 hp
  obtain ⟨b0, rfl⟩ := List.length_eq_one_iff.1 hrl
  have hb0 : b0 = Cv.bytes new := (hr (Cv.byteLayout.keeps cv new, b0) (by simp)).2
  subst hb0
  simp only [List.length_cons, List.length_nil, List.take, List.cons.injEq, and_true] at hargs
  obtain ⟨h0, h1⟩ := hargs
  simp only [List.map, List.zipWith, ArmAbi.all, ArmAbi.owns, Bytes.Layout.turns, Bytes.Layout.keeps, Stack.byteLayout,
    Cv.byteLayout, sepConj_emp, sepConj_assoc] at hp
  rw [sepExists_sepConj_left] at hp
  obtain ⟨b, hp⟩ := (satisfies_sepExists _ _).1 hp
  simp only [sepConj_assoc] at hp
  obtain ⟨⟨-, hH⟩, hp⟩ := (satisfies_pure_sepConj _ _ _).1 hp
  refine ⟨⟨st, cv, new, cvs, b⟩, ?_, ?_⟩
  · simp only [sepConj_assoc]
    exact (satisfies_pure_sepConj _ _ _).2 ⟨⟨h0.symm, h1.symm, hacc, hH⟩, hp⟩
  · intro sf hq
    simp only [sepConj_assoc] at hq
    rw [sepExists_sepConj_left] at hq
    obtain ⟨b', hq⟩ := (satisfies_sepExists _ _).1 hq
    simp only [sepConj_assoc] at hq
    obtain ⟨hH', hq⟩ := (satisfies_pure_sepConj _ _ _).1 hq
    simp only [ArmAbi.spec, Push.byteContract, List.map, List.zipWith, ArmAbi.all, ArmAbi.owns, Bytes.Layout.turns,
      Bytes.Layout.keeps, Stack.byteLayout, Cv.byteLayout, sepConj_emp, sepConj_assoc, pure_true_sepConj]
    rw [sepExists_sepConj_left]
    refine (satisfies_sepExists _ _).2 ⟨b', ?_⟩
    simp only [sepConj_assoc]
    exact (satisfies_pure_sepConj _ _ _).2 ⟨⟨hH'.2.1, hH'⟩, hq⟩

#print axioms push_arm_meets
