import Simd
import Code
import Run
import Kernel
open Simd

/-! The specification's compression, written out for 24 unknown words. -/

namespace Flat
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

/-- Evaluate the specification's vectors: every `set` and every index, on vectors written out. -/
macro "eval_spec" : tactic => `(tactic|
  simp (config := {maxSteps := 100000000, implicitDefEqProofs := false}) only [specCv, Blake3Generic.BLAKE3_COMPRESS, Blake3Generic.G, Blake3Generic.PERMUTE,
    Blake3Generic.PERMUTATION, Blake3Generic.IV, Blake3.lo, Blake3.hi, Id.run,
    Std.Legacy.Range.forIn_eq_forIn_range', List.range'_succ, List.range'_zero, List.forIn_cons, List.forIn_nil,
    List.finRange_succ, List.finRange_zero, List.map_cons, List.map_nil, bind, pure, Std.Legacy.Range.size,
    rep16, ofFn16, ofFn8, fv0, fv1, fv2, fv3, fv4, fv5, fv6, fv7, fv8, fv9, fv10, fv11, fv12, fv13, fv14, fv15,
    Vector.set_mk, List.set_toArray, List.set_cons_succ, List.set_cons_zero, Fin.isValue, Fin.getElem_fin,
    Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero,
    Fin.val_succ, Fin.val_zero, Nat.reduceAdd, Nat.reduceSub, Nat.reduceDiv, Nat.reduceMul, Nat.reduceMod,
    Blake3Generic.Rotr.rotr, Blake3Generic.Halves.low, Blake3Generic.Halves.high])

end Flat
