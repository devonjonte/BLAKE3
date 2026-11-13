import BytesLemmas
import Lemmas_node
import Chunk
open X86 Cells

/-! # A message's bytes in memory and the words the specification reads of them

The bridge between `Bytes.At` (a message's bytes one after another, as a contract speaks of them) and
`Blake3.wordsLE` (the sixteen little-endian words of a block, as the specification reads them, zero past
the message's end): the vectors a kernel reads at a block are those words. Written once, for every
function that hashes a message's bytes. Checked by Lean; not to be read. -/

/-- Sixteen bytes of a list from `s`, zero past its end, as a vector. -/
def Bytes.vec (l : List (BitVec 8)) (s : Nat) : V :=
  Bytes.pack (l.getD s 0) (l.getD (s + 1) 0) (l.getD (s + 2) 0) (l.getD (s + 3) 0) (l.getD (s + 4) 0) (l.getD (s + 5) 0) (l.getD (s + 6) 0) (l.getD (s + 7) 0)
    (l.getD (s + 8) 0) (l.getD (s + 9) 0) (l.getD (s + 10) 0) (l.getD (s + 11) 0) (l.getD (s + 12) 0) (l.getD (s + 13) 0) (l.getD (s + 14) 0) (l.getD (s + 15) 0)

theorem word_of_bytes (b0 b1 b2 b3 : BitVec 8) :
    ((⟨b0⟩ : UInt8).toUInt32 <<< (8 * 0 : Nat).toUInt32 ||| (⟨b1⟩ : UInt8).toUInt32 <<< (8 * 1 : Nat).toUInt32 |||
      (⟨b2⟩ : UInt8).toUInt32 <<< (8 * 2 : Nat).toUInt32 ||| (⟨b3⟩ : UInt8).toUInt32 <<< (8 * 3 : Nat).toUInt32)
      = ⟨b3 ++ b2 ++ b1 ++ b0⟩ := by
  apply UInt32.toBitVec_inj.mp
  simp
  bv_decide

theorem Bytes.At.get {m : Mem} {a : BitVec 64} {l : List (BitVec 8)} (h : Bytes.At m a l) (s i : Nat) (hi : s + i < l.length) :
    m (a + BitVec.ofNat 64 s + BitVec.ofNat 64 i) = some (l.getD (s + i) 0#8) := by
  have := h (s + i) hi
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  simpa [List.getD, List.getElem?_eq_getElem hi] using this

theorem by8_pack (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : BitVec 8) :
    by8 (Bytes.pack b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15) 0 = b0 ∧ by8 (Bytes.pack b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15) 1 = b1 ∧
    by8 (Bytes.pack b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15) 2 = b2 ∧ by8 (Bytes.pack b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15) 3 = b3 ∧
    by8 (Bytes.pack b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15) 4 = b4 ∧ by8 (Bytes.pack b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15) 5 = b5 ∧
    by8 (Bytes.pack b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15) 6 = b6 ∧ by8 (Bytes.pack b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15) 7 = b7 ∧
    by8 (Bytes.pack b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15) 8 = b8 ∧ by8 (Bytes.pack b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15) 9 = b9 ∧
    by8 (Bytes.pack b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15) 10 = b10 ∧ by8 (Bytes.pack b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15) 11 = b11 ∧
    by8 (Bytes.pack b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15) 12 = b12 ∧ by8 (Bytes.pack b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15) 13 = b13 ∧
    by8 (Bytes.pack b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15) 14 = b14 ∧ by8 (Bytes.pack b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15) 15 = b15 := by
  have e := Bytes.ofVec_pack b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15
  simpa only [Bytes.ofVec, List.cons.injEq, and_true] using e

/-- **Sixteen bytes of a message in memory are the vector code reads there.** -/
theorem Bytes.vec_at {m : Mem} {a : BitVec 64} {l : List (BitVec 8)} (h : Bytes.At m a l) (s : Nat) (hs : s + 16 ≤ l.length) :
    Vec m (a + BitVec.ofNat 64 s) (Bytes.vec l s) := by
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15⟩ :=
    by8_pack (l.getD s 0) (l.getD (s + 1) 0) (l.getD (s + 2) 0) (l.getD (s + 3) 0) (l.getD (s + 4) 0) (l.getD (s + 5) 0) (l.getD (s + 6) 0) (l.getD (s + 7) 0)
      (l.getD (s + 8) 0) (l.getD (s + 9) 0) (l.getD (s + 10) 0) (l.getD (s + 11) 0) (l.getD (s + 12) 0) (l.getD (s + 13) 0) (l.getD (s + 14) 0) (l.getD (s + 15) 0)
  unfold Vec Bytes.vec
  rw [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  exact ⟨h.get s 0 (by omega), h.get s 1 (by omega), h.get s 2 (by omega), h.get s 3 (by omega), h.get s 4 (by omega), h.get s 5 (by omega),
    h.get s 6 (by omega), h.get s 7 (by omega), h.get s 8 (by omega), h.get s 9 (by omega), h.get s 10 (by omega), h.get s 11 (by omega),
    h.get s 12 (by omega), h.get s 13 (by omega), h.get s 14 (by omega), h.get s 15 (by omega)⟩

theorem dw_pack (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : BitVec 8) :
    dw (Bytes.pack b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15) 0 = b3 ++ b2 ++ b1 ++ b0 ∧
    dw (Bytes.pack b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15) 1 = b7 ++ b6 ++ b5 ++ b4 ∧
    dw (Bytes.pack b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15) 2 = b11 ++ b10 ++ b9 ++ b8 ∧
    dw (Bytes.pack b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15) 3 = b15 ++ b14 ++ b13 ++ b12 := by
  simp only [dw, Bytes.pack]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> bv_decide

theorem word_of_bytes' (b0 b1 b2 b3 : BitVec 8) :
    ((⟨b0⟩ : UInt8).toUInt32 <<< Nat.toUInt32 0 ||| (⟨b1⟩ : UInt8).toUInt32 <<< Nat.toUInt32 8 |||
      (⟨b2⟩ : UInt8).toUInt32 <<< Nat.toUInt32 16 ||| (⟨b3⟩ : UInt8).toUInt32 <<< Nat.toUInt32 24)
      = ⟨b3 ++ b2 ++ b1 ++ b0⟩ := word_of_bytes b0 b1 b2 b3

theorem append8_get (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 : UInt32) (i : Nat) (hi : i < 8 + 8) :
    (#v[a0, a1, a2, a3, a4, a5, a6, a7] ++ #v[b0, b1, b2, b3, b4, b5, b6, b7])[i] =
      (#v[a0, a1, a2, a3, a4, a5, a6, a7, b0, b1, b2, b3, b4, b5, b6, b7] : Vector UInt32 16)[i] := by
  match i, hi with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _ | 10, _ | 11, _ | 12, _ | 13, _ | 14, _ | 15, _ => rfl
  | n + 16, h => exact absurd h (by omega)

/-- **The sixteen words the specification reads of a message at `s` are the four vectors of its bytes
there** (zero past the message's end, on both sides). -/
theorem Bytes.block_words (l : List (BitVec 8)) (s : Nat) :
    words8 (Bytes.vec l s) (Bytes.vec l (s + 16)) ++ words8 (Bytes.vec l (s + 32)) (Bytes.vec l (s + 48))
      = Blake3.wordsLE (Blake3.ofBytes l) s 16 := by
  ext i hi
  simp only [Blake3.wordsLE, Vector.getElem_ofFn, Blake3.ofBytes_get, words8, append8_get]
  match i, hi with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _ | 10, _ | 11, _ | 12, _ | 13, _ | 14, _ | 15, _ =>
    simp only [Bytes.vec, dw_pack, Nat.add_assoc, Nat.reduceAdd, Nat.reduceMul, Nat.add_zero, Nat.mul_zero]
    rw [word_of_bytes']
    rfl
  | n + 16, h => exact absurd h (by omega)
