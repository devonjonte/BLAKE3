import Arm64
import ProofLib
import HexContract
import ArmAbi
import Proof_hex_neon
open Arm64 ProofLib

/-! # The NEON `hex` kernel: the contract in bytes

`Proof_hex_neon.lean` (written by the compiler) proves the kernel against its own contract, in 16-byte vectors. Here the same code meets the
statement a reader wants, in the words used on x86-64 (`Hex.text`, `../spec/HexText.lean`): the 64 bytes at `out` become `Hex.text` of the 32
bytes at `inp`. From `hex_neon_ok` by their rule `subroutine_ok_refine`; the rest is bytes to vectors and
back. -/

set_option maxRecDepth 200000

namespace Hex

/-- The sixteen bytes of a vector, lowest first. -/
def bytes16 (v : BitVec 128) : List (BitVec 8) :=
  unpack64 (v.extractLsb' 0 64) ++ unpack64 (v.extractLsb' 64 64)

theorem bytes16_length (v : BitVec 128) : (bytes16 v).length = 16 := rfl

end Hex

/-- A vector in memory is its sixteen bytes in memory. -/
theorem pointsTo128_eq_bytes (a : BitVec 64) (v : BitVec 128) : (a ↦₁₂₈ v) = (a ↦ₛ Hex.bytes16 v) := by
  rw [pointsTo128_split64, pointsTo64_eq_pointsToBytes, pointsTo64_eq_pointsToBytes, Hex.bytes16, pointsToBytes_append]
  rfl

theorem List.cons_of_length_succ' {α : Type} {n : Nat} (l : List α) (h : l.length = n + 1) :
    ∃ a rest, l = a :: rest ∧ rest.length = n := by
  cases l with
  | nil => simp at h
  | cons a rest => exact ⟨a, rest, rfl, by simpa using h⟩

/-- Sixteen bytes are a vector's. -/
theorem Hex.exists_vec (l : List (BitVec 8)) (h : l.length = 16) : ∃ v : BitVec 128, l = Hex.bytes16 v := by
  obtain ⟨b0, r0, e0, h0⟩ := List.cons_of_length_succ' l h
  obtain ⟨b1, r1, e1, h1⟩ := List.cons_of_length_succ' r0 h0
  obtain ⟨b2, r2, e2, h2⟩ := List.cons_of_length_succ' r1 h1
  obtain ⟨b3, r3, e3, h3⟩ := List.cons_of_length_succ' r2 h2
  obtain ⟨b4, r4, e4, h4⟩ := List.cons_of_length_succ' r3 h3
  obtain ⟨b5, r5, e5, h5⟩ := List.cons_of_length_succ' r4 h4
  obtain ⟨b6, r6, e6, h6⟩ := List.cons_of_length_succ' r5 h5
  obtain ⟨b7, r7, e7, h7⟩ := List.cons_of_length_succ' r6 h6
  obtain ⟨b8, r8, e8, h8⟩ := List.cons_of_length_succ' r7 h7
  obtain ⟨b9, r9, e9, h9⟩ := List.cons_of_length_succ' r8 h8
  obtain ⟨b10, r10, e10, h10⟩ := List.cons_of_length_succ' r9 h9
  obtain ⟨b11, r11, e11, h11⟩ := List.cons_of_length_succ' r10 h10
  obtain ⟨b12, r12, e12, h12⟩ := List.cons_of_length_succ' r11 h11
  obtain ⟨b13, r13, e13, h13⟩ := List.cons_of_length_succ' r12 h12
  obtain ⟨b14, r14, e14, h14⟩ := List.cons_of_length_succ' r13 h13
  obtain ⟨b15, r15, e15, h15⟩ := List.cons_of_length_succ' r14 h14
  have enil : r15 = [] := List.eq_nil_of_length_eq_zero h15
  subst enil e15 e14 e13 e12 e11 e10 e9 e8 e7 e6 e5 e4 e3 e2 e1 e0
  refine ⟨b15 ++ b14 ++ b13 ++ b12 ++ b11 ++ b10 ++ b9 ++ b8 ++ b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0, ?_⟩
  simp only [Hex.bytes16, unpack64, List.cons_append, List.nil_append, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> bv_kernel

/-- Thirty-two bytes in memory are two vectors in memory. -/
theorem bytes32_vecs (a : BitVec 64) (l : List (BitVec 8)) (h : l.length = 32) :
    ∃ v0 v1 : BitVec 128, l = Hex.bytes16 v0 ++ Hex.bytes16 v1 ∧
      (a ↦ₛ l) = ((a ↦₁₂₈ v0) ∗ ((a + 16#64) ↦₁₂₈ v1)) := by
  obtain ⟨v0, e0⟩ := Hex.exists_vec (l.take 16) (by simp [h])
  obtain ⟨v1, e1⟩ := Hex.exists_vec (l.drop 16) (by simp [h])
  have e : l = Hex.bytes16 v0 ++ Hex.bytes16 v1 := by rw [← e0, ← e1, List.take_append_drop]
  refine ⟨v0, v1, e, ?_⟩
  rw [e, pointsToBytes_append, pointsTo128_eq_bytes, pointsTo128_eq_bytes]
  rfl

/-- Sixty-four bytes in memory are four vectors in memory. -/
theorem bytes64_vecs (a : BitVec 64) (l : List (BitVec 8)) (h : l.length = 64) :
    ∃ v0 v1 v2 v3 : BitVec 128, l = Hex.bytes16 v0 ++ Hex.bytes16 v1 ++ Hex.bytes16 v2 ++ Hex.bytes16 v3 ∧
      (a ↦ₛ l) = ((a ↦₁₂₈ v0) ∗ ((a + 16#64) ↦₁₂₈ v1) ∗ ((a + 32#64) ↦₁₂₈ v2) ∗ ((a + 48#64) ↦₁₂₈ v3)) := by
  obtain ⟨v0, e0⟩ := Hex.exists_vec (l.take 16) (by simp [h])
  obtain ⟨v1, e1⟩ := Hex.exists_vec ((l.drop 16).take 16) (by simp [h])
  obtain ⟨v2, e2⟩ := Hex.exists_vec ((l.drop 32).take 16) (by simp [h])
  obtain ⟨v3, e3⟩ := Hex.exists_vec (l.drop 48) (by simp [h])
  have e : l = Hex.bytes16 v0 ++ Hex.bytes16 v1 ++ Hex.bytes16 v2 ++ Hex.bytes16 v3 := by
    rw [← e0, ← e1, ← e2, ← e3, List.append_assoc, List.append_assoc]
    have a3 : List.take 16 (List.drop 32 l) ++ List.drop 48 l = List.drop 32 l := by
      simpa [List.drop_drop] using List.take_append_drop 16 (List.drop 32 l)
    have a2 : List.take 16 (List.drop 16 l) ++ List.drop 32 l = List.drop 16 l := by
      simpa [List.drop_drop] using List.take_append_drop 16 (List.drop 16 l)
    rw [a3, a2, List.take_append_drop]
  refine ⟨v0, v1, v2, v3, e, ?_⟩
  rw [e, pointsToBytes_append, pointsToBytes_append, pointsToBytes_append, pointsTo128_eq_bytes, pointsTo128_eq_bytes,
    pointsTo128_eq_bytes, pointsTo128_eq_bytes]
  simp only [List.length_append, Hex.bytes16_length, sepConj_assoc]

/-- A byte of a 64-bit half of a vector is a byte of the vector. -/
theorem Hex.slice8 (v : BitVec 128) (a b : Nat) (h : a + 8 ≤ 64) :
    (v.extractLsb' b 64).extractLsb' a 8 = v.extractLsb' (a + b) 8 := by
  ext i hi
  simp only [BitVec.getElem_extractLsb']
  rw [BitVec.getLsbD_extractLsb']
  have : a + i < 64 := by omega
  simp only [this, decide_true, Bool.true_and]
  congr 1; omega

seal Hex.char in
/-- The hexadecimal of eight bytes of a vector is the sixteen bytes of the vector the kernel writes for them. (With
`Hex.char` closed: each character is then a byte like any other, and the claim is one of which byte is where.) -/
theorem Hex.text_half (v : BitVec 128) (k : Nat) (hk : k = 0 ∨ k = 8) :
    Hex.text (unpack64 (v.extractLsb' (8 * k) 64)) = Hex.bytes16 (Hex.hex16 v k) := by
  rcases hk with rfl | rfl <;>
  · simp (disch := decide) only [Hex.text, Hex.bytes16, unpack64, List.cons_append, List.nil_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, List.cons.injEq, and_true, Hex.hex16, Hex.byte, Hex.slice8, Nat.reduceMul, Nat.reduceAdd]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> bv_kernel

/-- The hexadecimal of two vectors' bytes is the bytes of the four vectors the kernel writes. -/
theorem Hex.text_vecs (v0 v1 : BitVec 128) :
    Hex.text (Hex.bytes16 v0 ++ Hex.bytes16 v1) =
      Hex.bytes16 (Hex.hex16 v0 0) ++ Hex.bytes16 (Hex.hex16 v0 8) ++ Hex.bytes16 (Hex.hex16 v1 0) ++ Hex.bytes16 (Hex.hex16 v1 8) := by
  have t0 := Hex.text_half v0 0 (Or.inl rfl)
  have t1 := Hex.text_half v0 8 (Or.inr rfl)
  have t2 := Hex.text_half v1 0 (Or.inl rfl)
  have t3 := Hex.text_half v1 8 (Or.inr rfl)
  simp only [Nat.reduceMul] at t0 t1 t2 t3
  rw [← t0, ← t1, ← t2, ← t3]
  simp only [Hex.text, Hex.bytes16, List.flatMap_append, List.append_assoc]

structure HexBytesArgs where
  out : BitVec 64
  inp : BitVec 64
  hash : List (BitVec 8)
  old : List (BitVec 8)

/-- **`hex(out, hash)` on AArch64.** With 32 bytes `hash` at X1 and 64 bytes at X0: the 64 bytes become the
hexadecimal of the hash, the hash is unchanged. -/
abbrev hexBytesSpec : Spec HexBytesArgs where
  pre := fun x s0 =>
    ⌜s0.readReg64 .x0 = x.out ∧ s0.readReg64 .x1 = x.inp ∧ x.hash.length = 32 ∧ x.old.length = 64⌝ ∗
    (x.inp ↦ₛ x.hash) ∗ (x.out ↦ₛ x.old)
  post := fun x _ _ => (x.inp ↦ₛ x.hash) ∗ (x.out ↦ₛ Hex.text x.hash)

theorem hex_neon_bytes_ok (prog : Program) (h_code : hex_neon_code.holds prog) :
    prog.subroutineOk "b3l_hex_neon" hexBytesSpec := by
  refine subroutine_ok_refine (hex_neon_ok prog h_code) ?_
  intro y R s0 hp
  simp only [sepConj_assoc] at hp
  obtain ⟨⟨h0, h1, hlen, holen⟩, hp⟩ := (satisfies_pure_sepConj _ _ _).1 hp
  obtain ⟨v0, v1, eh, ehp⟩ := bytes32_vecs y.inp y.hash hlen
  obtain ⟨d0, d1, d2, d3, eo, eop⟩ := bytes64_vecs y.out y.old holen
  refine ⟨⟨y.out, y.inp, v0, v1, d0, d1, d2, d3⟩, ?_, ?_⟩
  · simp only [sepConj_assoc]
    refine (satisfies_pure_sepConj _ _ _).2 ⟨⟨h0, h1⟩, ?_⟩
    rw [ehp, eop] at hp
    simpa only [sepConj_assoc] using hp
  · intro sf hq
    have t : (y.out ↦ₛ Hex.text y.hash) =
        ((y.out ↦₁₂₈ Hex.hex16 v0 0) ∗ ((y.out + 16#64) ↦₁₂₈ Hex.hex16 v0 8) ∗
          ((y.out + 32#64) ↦₁₂₈ Hex.hex16 v1 0) ∗ ((y.out + 48#64) ↦₁₂₈ Hex.hex16 v1 8)) := by
      rw [eh, Hex.text_vecs, pointsToBytes_append, pointsToBytes_append, pointsToBytes_append, pointsTo128_eq_bytes,
        pointsTo128_eq_bytes, pointsTo128_eq_bytes, pointsTo128_eq_bytes]
      simp only [List.length_append, Hex.bytes16_length, sepConj_assoc]
    show sf.mem ⊨ ((y.inp ↦ₛ y.hash) ∗ (y.out ↦ₛ Hex.text y.hash)) ∗ R
    rw [ehp, t]
    simpa only [sepConj_assoc] using hq

#print axioms hex_neon_bytes_ok

/-! ## The contract that names no machine

`Hex.byteContract` (`../spec/HexContract.lean`) is what the x86-64 kernel is proved to meet on our model
(`../lang/Meets_hex_bytes.lean`). Here the AArch64 kernel meets it, read for AArch64 (`ArmAbi.spec`). -/

theorem Hex.text_length (l : List (BitVec 8)) : (Hex.text l).length = 2 * l.length := by
  induction l with
  | nil => rfl
  | cons b rest ih =>
    have e : Hex.text (b :: rest) = [Hex.char (b >>> 4), Hex.char (b &&& 15#8)] ++ Hex.text rest := rfl
    rw [e, List.length_append, ih, List.length_cons]
    simp only [List.length_cons, List.length_nil]
    omega

/-- **The AArch64 kernel `hex_neon` meets `Hex.byteContract`.** -/
theorem hex_neon_meets (prog : Program) (h_code : hex_neon_code.holds prog) (out inp : BitVec 64) (hash : List (BitVec 8)) :
    prog.subroutineOk "b3l_hex_neon" (ArmAbi.spec (Hex.byteContract out inp hash)) := by
  refine subroutine_ok_refine (hex_neon_bytes_ok prog h_code) ?_
  intro r R s0 hp
  simp only [ArmAbi.spec, Hex.byteContract, sepConj_assoc] at hp
  obtain ⟨⟨hargs, -, hrl, hr⟩, hp⟩ := (satisfies_pure_sepConj _ _ _).1 hp
  obtain ⟨b0, rfl⟩ := List.length_eq_one_iff.1 hrl
  obtain ⟨hl0, he0⟩ := hr ((Bytes.plain 32).keeps inp hash, b0) (by simp)
  have hlen : b0.length = 32 := hl0
  have he : b0 = hash := he0
  clear hl0 he0 hr hrl
  subst he
  simp only [List.length_cons, List.length_nil, List.take, List.cons.injEq, and_true] at hargs
  obtain ⟨h0, h1⟩ := hargs
  simp only [List.map, List.zipWith, ArmAbi.all, ArmAbi.owns, Bytes.Layout.fills, Bytes.Layout.keeps, Bytes.plain,
    sepConj_emp, sepConj_assoc] at hp
  rw [sepExists_sepConj_left] at hp
  obtain ⟨old, hp⟩ := (satisfies_sepExists _ _).1 hp
  simp only [sepConj_assoc] at hp
  obtain ⟨⟨hol, -⟩, hp⟩ := (satisfies_pure_sepConj _ _ _).1 hp
  refine ⟨⟨out, inp, b0, old⟩, ?_, ?_⟩
  · simp only [sepConj_assoc]
    refine (satisfies_pure_sepConj _ _ _).2 ⟨⟨h0.symm, h1.symm, hlen, hol⟩, ?_⟩
    exact Satisfies.of_eq hp (by sep_eq)
  · intro sf hq
    simp only [sepConj_assoc] at hq
    simp only [ArmAbi.spec, Hex.byteContract, List.map, List.zipWith, ArmAbi.all, ArmAbi.owns, Bytes.Layout.fills,
      Bytes.Layout.keeps, Bytes.plain, sepConj_emp, sepConj_assoc, pure_true_sepConj]
    rw [sepExists_sepConj_left]
    refine (satisfies_sepExists _ _).2 ⟨Hex.text b0, ?_⟩
    simp only [sepConj_assoc]
    refine (satisfies_pure_sepConj _ _ _).2 ⟨⟨by rw [Hex.text_length, hlen], trivial⟩, ?_⟩
    exact Satisfies.of_eq hq (by sep_eq)

#print axioms hex_neon_meets
