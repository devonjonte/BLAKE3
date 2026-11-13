import Try
import Sample_stack
import Spec_levels
open X86

/-! # The tree's levels, for trying functions on examples

How to put the levels of some chunks into memory and how to test that memory holds them. Test-side: not
proved against `Levels.At`. It follows the same words: the levels have received all the chunks but the
newest; a level that has received an odd number of values holds the newest of them in its first place;
the newest chunk is in the bottom level's next place. -/

/-- What the levels from `level` up hold when they have received `r` values of `size` chunks each:
(level, place, first chunk, chunks) for each value held. -/
def Levels.heldFrom : Nat → Nat → Nat → Nat → List (Nat × Nat × Nat × Nat)
  | 0, _, _, _ => []
  | f + 1, level, size, r =>
    (if r % 2 = 1 then [(level, 0, (r - 1) * size, size)] else []) ++ Levels.heldFrom f (level + 1) (2 * size) (r / 2)

/-- What every place in use holds for `n` chunks. -/
def Levels.held (n : Nat) : List (Nat × Nat × Nat × Nat) :=
  if n = 0 then [] else (0, (n - 1) % 2, n - 1, 1) :: Levels.heldFrom 54 0 1 (n - 1)

/-- Where a place is. -/
def Levels.slot (lv : BitVec 64) (level place : Nat) : BitVec 64 := lv + BitVec.ofNat 64 (64 + 64 * level + 32 * place)

def Levels.sample (k : Blake3.CV) (mode : Blake3.Word) : Try.Sample (Array Blake3.Node) where
  put := fun m lv chunks =>
    let m := Try.fill m lv (Array.replicate 3520 0#8)
    let m := Try.fill m lv (Try.le64 (BitVec.ofNat 64 chunks.size)).toArray
    (Levels.held chunks.size).foldl (fun m (level, place, start, size) =>
      Try.fill m (Levels.slot lv level place) (Cv.bytes (Blake3.sub k mode chunks start size)).toArray) m
  check := fun m lv chunks =>
    decide (chunks.size ≤ 2 ^ 54) && (Try.bytes? m lv 3520).isSome &&
    Try.bytes? m lv 8 == some (Try.le64 (BitVec.ofNat 64 chunks.size)) &&
    (Levels.held chunks.size).all fun (level, place, start, size) =>
      Try.bytes? m (Levels.slot lv level place) 32 == some (Cv.bytes (Blake3.sub k mode chunks start size))
