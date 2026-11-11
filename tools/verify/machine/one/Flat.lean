import Machine
import Spec32
open X86 Blake3Generic

/-! The specification's compression, written out for unknown words, and as seven rounds. -/

theorem fv0 : (((0 : Fin 16) : Nat)) = 0 := rfl
theorem fv1 : (((1 : Fin 16) : Nat)) = 1 := rfl
theorem fv2 : (((2 : Fin 16) : Nat)) = 2 := rfl
theorem fv3 : (((3 : Fin 16) : Nat)) = 3 := rfl
theorem fv4 : (((4 : Fin 16) : Nat)) = 4 := rfl
theorem fv5 : (((5 : Fin 16) : Nat)) = 5 := rfl
theorem fv6 : (((6 : Fin 16) : Nat)) = 6 := rfl
theorem fv7 : (((7 : Fin 16) : Nat)) = 7 := rfl
theorem fv8 : (((8 : Fin 16) : Nat)) = 8 := rfl
theorem fv9 : (((9 : Fin 16) : Nat)) = 9 := rfl
theorem fv10 : (((10 : Fin 16) : Nat)) = 10 := rfl
theorem fv11 : (((11 : Fin 16) : Nat)) = 11 := rfl
theorem fv12 : (((12 : Fin 16) : Nat)) = 12 := rfl
theorem fv13 : (((13 : Fin 16) : Nat)) = 13 := rfl
theorem fv14 : (((14 : Fin 16) : Nat)) = 14 := rfl
theorem fv15 : (((15 : Fin 16) : Nat)) = 15 := rfl
theorem rep16 : (Vector.replicate 16 (0 : BitVec 32)) = #v[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := rfl
theorem ofFn16 (f : Fin 16 → BitVec 32) : Vector.ofFn f = #v[f 0, f 1, f 2, f 3, f 4, f 5, f 6, f 7, f 8, f 9, f 10, f 11, f 12, f 13, f 14, f 15] := rfl
theorem ofFn8 (f : Fin 8 → BitVec 32) : Vector.ofFn f = #v[f 0, f 1, f 2, f 3, f 4, f 5, f 6, f 7] := rfl

/-- One round of the specification: its eight G's. -/
def rnd (v : Vector (BitVec 32) 16) (m : Vector (BitVec 32) 16) : Vector (BitVec 32) 16 :=
  G (G (G (G (G (G (G (G v 0 4 8 12 m[0] m[1]) 1 5 9 13 m[2] m[3]) 2 6 10 14 m[4] m[5]) 3 7 11 15 m[6] m[7]) 0 5 10 15 m[8] m[9]) 1 6 11 12 m[10] m[11]) 2 7 8 13 m[12] m[13]) 3 4 9 14 m[14] m[15]

/-- Evaluate the specification's vectors: every `set` and every index, on vectors written out. -/
macro "eval_spec" : tactic => `(tactic|
  simp (config := {maxSteps := 100000000, implicitDefEqProofs := false}) only [rnd, Blake3Generic.G, Blake3Generic.PERMUTE,
    Blake3Generic.PERMUTATION, Blake3Generic.IV, Blake3.lo, Blake3.hi, Id.run, bind, pure,
    rep16, ofFn16, ofFn8, fv0, fv1, fv2, fv3, fv4, fv5, fv6, fv7, fv8, fv9, fv10, fv11, fv12, fv13, fv14, fv15,
    Vector.set_mk, List.set_toArray, List.set_cons_succ, List.set_cons_zero, Fin.isValue, Fin.getElem_fin,
    Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero,
    Fin.val_succ, Fin.val_zero, Nat.reduceAdd, Nat.reduceSub, Nat.reduceDiv, Nat.reduceMul, Nat.reduceMod,
    Blake3Generic.Rotr.rotr, Blake3Generic.Halves.low, Blake3Generic.Halves.high])

/-- The vector operations, as operations on bits. -/
macro "open_ops" : tactic => `(tactic|
  simp only [map2, map1, pshufb, shufb1, pshufd, shufps, pblendw, blend1, vpblendd, blendd1, punpcklqdq, punpckldq, punpckhdq,
    dw, mk4, by8, w16, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reducePow, ↓reduceIte, Nat.reduceEqDiff])

theorem eta16 (v : Vector (BitVec 32) 16) : #v[v[0], v[1], v[2], v[3], v[4], v[5], v[6], v[7], v[8], v[9], v[10], v[11], v[12], v[13], v[14], v[15]] = v := by
  ext i hi
  match i, hi with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | 6, _ => rfl
  | 7, _ => rfl
  | 8, _ => rfl
  | 9, _ => rfl
  | 10, _ => rfl
  | 11, _ => rfl
  | 12, _ => rfl
  | 13, _ => rfl
  | 14, _ => rfl
  | 15, _ => rfl
  | n + 16, h => exact absurd h (by omega)

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

theorem low8_0 (w : Vector (BitVec 32) 16) : (low8 w)[0] = w[0] ^^^ w[8] := rfl
theorem low8_1 (w : Vector (BitVec 32) 16) : (low8 w)[1] = w[1] ^^^ w[9] := rfl
theorem low8_2 (w : Vector (BitVec 32) 16) : (low8 w)[2] = w[2] ^^^ w[10] := rfl
theorem low8_3 (w : Vector (BitVec 32) 16) : (low8 w)[3] = w[3] ^^^ w[11] := rfl
theorem low8_4 (w : Vector (BitVec 32) 16) : (low8 w)[4] = w[4] ^^^ w[12] := rfl
theorem low8_5 (w : Vector (BitVec 32) 16) : (low8 w)[5] = w[5] ^^^ w[13] := rfl
theorem low8_6 (w : Vector (BitVec 32) 16) : (low8 w)[6] = w[6] ^^^ w[14] := rfl
theorem low8_7 (w : Vector (BitVec 32) 16) : (low8 w)[7] = w[7] ^^^ w[15] := rfl
