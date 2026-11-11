import Whole
open Simd Flat Blake3Generic

theorem rnd_fold (v m : Vector (BitVec 32) 16) :
    G (G (G (G (G (G (G (G v 0 4 8 12 m[0] m[1]) 1 5 9 13 m[2] m[3]) 2 6 10 14 m[4] m[5]) 3 7 11 15 m[6] m[7]) 0 5 10 15 m[8] m[9]) 1 6 11 12 m[10] m[11]) 2 7 8 13 m[12] m[13]) 3 4 9 14 m[14] m[15] = rnd v m := rfl

/-- The seven rounds, the message permuted between them. -/
def rounds7 (v m : Vector (BitVec 32) 16) : Vector (BitVec 32) 16 :=
  rnd (rnd (rnd (rnd (rnd (rnd (rnd v m) (PERMUTE m)) (PERMUTE (PERMUTE m))) (PERMUTE (PERMUTE (PERMUTE m))))
    (PERMUTE (PERMUTE (PERMUTE (PERMUTE m))))) (PERMUTE (PERMUTE (PERMUTE (PERMUTE (PERMUTE m))))))
    (PERMUTE (PERMUTE (PERMUTE (PERMUTE (PERMUTE (PERMUTE m))))))

theorem rounds7_fold (v m : Vector (BitVec 32) 16) :
    rnd (rnd (rnd (rnd (rnd (rnd (rnd v m) (PERMUTE m)) (PERMUTE (PERMUTE m))) (PERMUTE (PERMUTE (PERMUTE m))))
      (PERMUTE (PERMUTE (PERMUTE (PERMUTE m))))) (PERMUTE (PERMUTE (PERMUTE (PERMUTE (PERMUTE m))))))
      (PERMUTE (PERMUTE (PERMUTE (PERMUTE (PERMUTE (PERMUTE m)))))) = rounds7 v m := rfl

/-- The sixteen words the rounds start from. -/
def initv (h : Vector (BitVec 32) 8) (t : BitVec 64) (len flags : BitVec 32) : Vector (BitVec 32) 16 :=
  #v[h[0], h[1], h[2], h[3], h[4], h[5], h[6], h[7], 0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
    t.setWidth 32, (t >>> 32).setWidth 32, len, flags]

/-- The new chaining value: the two halves of the rounds' result, xored. -/
def low8 (w : Vector (BitVec 32) 16) : Vector (BitVec 32) 8 :=
  #v[w[0] ^^^ w[8], w[1] ^^^ w[9], w[2] ^^^ w[10], w[3] ^^^ w[11], w[4] ^^^ w[12], w[5] ^^^ w[13], w[6] ^^^ w[14], w[7] ^^^ w[15]]

theorem fw0 : (((0 : Fin 8) : Nat)) = 0 := rfl
theorem fw1 : (((1 : Fin 8) : Nat)) = 1 := rfl
theorem fw2 : (((2 : Fin 8) : Nat)) = 2 := rfl
theorem fw3 : (((3 : Fin 8) : Nat)) = 3 := rfl
theorem fw4 : (((4 : Fin 8) : Nat)) = 4 := rfl
theorem fw5 : (((5 : Fin 8) : Nat)) = 5 := rfl
theorem fw6 : (((6 : Fin 8) : Nat)) = 6 := rfl
theorem fw7 : (((7 : Fin 8) : Nat)) = 7 := rfl

macro "eval_vec" : tactic => `(tactic|
  simp (config := {maxSteps := 10000000, implicitDefEqProofs := false}) only [Blake3Generic.IV, Blake3.lo, Blake3.hi, low8, initv,
    rep16, ofFn16, ofFn8, fv0, fv1, fv2, fv3, fv4, fv5, fv6, fv7, fv8, fv9, fv10, fv11, fv12, fv13, fv14, fv15, fw0, fw1, fw2, fw3, fw4, fw5, fw6, fw7,
    Vector.set_mk, List.set_toArray, List.set_cons_succ, List.set_cons_zero, Fin.isValue, Fin.getElem_fin,
    Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero,
    Fin.val_succ, Fin.val_zero, Nat.reduceAdd, Blake3Generic.Halves.low, Blake3Generic.Halves.high])

/-- The specification's last statements: the halves xored, then the first eight words. -/
def tail (h : Vector (BitVec 32) 8) (w : Vector (BitVec 32) 16) : Vector (BitVec 32) 8 := Id.run do
  let mut v := w
  for i in List.finRange 8 do
    v := v.set (Blake3.lo i) (v[Blake3.lo i] ^^^ v[Blake3.hi i])
    v := v.set (Blake3.hi i) (v[Blake3.hi i] ^^^ h[i])
  return Vector.ofFn fun i => v[Blake3.lo i]

set_option maxRecDepth 1000000 in
theorem tail_eq (h : Vector (BitVec 32) 8) (w : Vector (BitVec 32) 16) : tail h w = low8 w := by
  rw [← eta16 w]
  simp only [tail, Id.run, List.forIn_cons, List.forIn_nil, List.finRange_succ, List.finRange_zero, List.map_cons,
    List.map_nil, bind, pure]
  eval_vec

set_option maxRecDepth 1000000 in
/-- The specification's compression (sections 2.2 to 3.3, `Generic.lean`, at 32-bit words), as seven
rounds between its first and last statements. -/
theorem spec_eq (h : Vector (BitVec 32) 8) (m : Vector (BitVec 32) 16) (t : BitVec 64) (len flags : BitVec 32) :
    specCv h m t len flags = low8 (rounds7 (initv h t len flags) m) := by
  rw [← tail_eq h]
  simp only [specCv, BLAKE3_COMPRESS, tail, rounds7, initv, Id.run, Std.Legacy.Range.forIn_eq_forIn_range', List.range'_succ,
    List.range'_zero, List.forIn_cons, List.forIn_nil, List.finRange_succ, List.finRange_zero, List.map_cons, List.map_nil,
    bind, pure, Std.Legacy.Range.size, rnd_fold,
    Blake3Generic.IV, rep16, Vector.set_mk, List.set_toArray, List.set_cons_succ, List.set_cons_zero,
    Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero,
    Blake3Generic.Halves.low, Blake3Generic.Halves.high]
