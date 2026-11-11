import Spec32
import Bridge
open Blake3Generic

/-! # The specification itself

The theorems of this folder are stated with `specCv`: the generic text of sections 2.2 to 3.3
(`Generic.lean`) at `BitVec 32`. `Bridge.lean` proves that text at `UInt32` is the
specification's `Blake3.BLAKE3_COMPRESS`. This file proves the two word types agree: so
`specCv` of any words is the first eight words of the specification's own compression function
of the same words. -/

abbrev bv (x : UInt32) : BitVec 32 := x.toBitVec

theorem bv_add (a b : UInt32) : bv (a + b) = bv a + bv b := rfl
theorem bv_xor (a b : UInt32) : bv (a ^^^ b) = bv a ^^^ bv b := rfl
theorem bv_rot16 (a : UInt32) : bv (Blake3.rotr a 16) = (bv a).rotateRight 16 := by
  have e1 : ((16 : Nat).toUInt32) = 16 := by decide
  have e2 : ((32 - 16 : Nat).toUInt32) = 16 := by decide
  simp only [bv, Blake3.rotr, e1, e2]; bv_decide
theorem bv_rot12 (a : UInt32) : bv (Blake3.rotr a 12) = (bv a).rotateRight 12 := by
  have e1 : ((12 : Nat).toUInt32) = 12 := by decide
  have e2 : ((32 - 12 : Nat).toUInt32) = 20 := by decide
  simp only [bv, Blake3.rotr, e1, e2]; bv_decide
theorem bv_rot8 (a : UInt32) : bv (Blake3.rotr a 8) = (bv a).rotateRight 8 := by
  have e1 : ((8 : Nat).toUInt32) = 8 := by decide
  have e2 : ((32 - 8 : Nat).toUInt32) = 24 := by decide
  simp only [bv, Blake3.rotr, e1, e2]; bv_decide
theorem bv_rot7 (a : UInt32) : bv (Blake3.rotr a 7) = (bv a).rotateRight 7 := by
  have e1 : ((7 : Nat).toUInt32) = 7 := by decide
  have e2 : ((32 - 7 : Nat).toUInt32) = 25 := by decide
  simp only [bv, Blake3.rotr, e1, e2]; bv_decide
theorem bv_low (t : UInt64) : bv (Blake3.low t) = t.toBitVec.setWidth 32 := rfl
theorem bv_high (t : UInt64) : bv (Blake3.high t) = (t.toBitVec >>> 32).setWidth 32 := by
  simp only [bv, Blake3.high]; bv_decide

theorem bv_get {n : Nat} (w : Vector UInt32 n) (j : Nat) (h : j < n) : bv (w[j]) = (w.map bv)[j] := by simp
theorem bv_getFin {n : Nat} (w : Vector UInt32 n) (j : Fin n) : bv (w[j]) = (w.map bv)[j] := by simp

theorem g_bv (v : Vector UInt32 16) (a b c d : Fin 16) (x y : UInt32) :
    (G v a b c d x y).map bv = G (v.map bv) a b c d (bv x) (bv y) := by
  simp only [G, Id.run, pure, Vector.map_set, bv_add, bv_xor, Rotr.rotr, bv_rot16, bv_rot12, bv_rot8, bv_rot7, bv_getFin]

theorem permute_bv (m : Vector UInt32 16) : (PERMUTE m).map bv = PERMUTE (m.map bv) := by
  ext i hi; simp [PERMUTE]

theorem iv_bv : (IV : Vector UInt32 8).map bv = (IV : Vector (BitVec 32) 8) := by
  ext i hi
  simp only [Vector.getElem_map]
  match i, hi with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ => rfl

/-- The generic text computes the same words at `UInt32` and at `BitVec 32`. -/
theorem compress_bv (h : Vector UInt32 8) (m : Vector UInt32 16) (t : UInt64) (len flags : UInt32) :
    (BLAKE3_COMPRESS h m t len flags).map bv
      = BLAKE3_COMPRESS (h.map bv) (m.map bv) t.toBitVec (bv len) (bv flags) := by
  simp only [BLAKE3_COMPRESS, Id.run, Std.Legacy.Range.forIn_eq_forIn_range', List.range'_succ, List.range'_zero,
    List.forIn_cons, List.forIn_nil, List.finRange_succ, List.finRange_zero, List.map_cons, List.map_nil,
    bind, pure, Std.Legacy.Range.size]
  simp only [Vector.map_set, g_bv, permute_bv, bv_get, bv_getFin, bv_xor, iv_bv, Halves.low, Halves.high, bv_low, bv_high,
    Vector.map_replicate]
  rfl

/-- **`specCv` is the specification.** For any chaining value, block, counter, length and flags,
`specCv` of their bits is the first eight words (`Blake3.first8`) of the specification's
`Blake3.BLAKE3_COMPRESS`, bit for bit. -/
theorem specCv_is_the_specifications (h : Vector UInt32 8) (m : Vector UInt32 16) (t : UInt64) (len flags : UInt32) :
    specCv (h.map bv) (m.map bv) t.toBitVec (bv len) (bv flags)
      = (Blake3.first8 (Blake3.BLAKE3_COMPRESS h m t len flags)).map bv := by
  rw [← compress_is_the_specifications]
  simp only [specCv, ← compress_bv, Blake3.first8]
  ext i hi
  simp

#print axioms specCv_is_the_specifications
