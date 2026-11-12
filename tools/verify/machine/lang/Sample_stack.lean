import Try
import Spec_stack
open X86

/-! # The stack and a chaining value, for trying functions on examples

How to put one into memory and how to test that memory holds one. Test-side: not proved against
`Stack.At` and `Cv.At`. -/

def Cv.bytes (cv : Blake3.CV) : List (BitVec 8) :=
  cv.toList.flatMap fun (w : UInt32) => (List.range 4).map fun i => BitVec.setWidth 8 (w.toBitVec >>> (8 * i))

def Cv.sample : Try.Sample Blake3.CV where
  put := fun m a cv => Try.fill m a (Cv.bytes cv).toArray
  check := fun m a cv => Try.bytes? m a 32 == some (Cv.bytes cv)

/-- Where the `j`-th newest of `n` values is. -/
def Stack.slot (st : BitVec 64) (n j : Nat) : BitVec 64 := st + 32#64 + BitVec.ofNat 64 (32 * (n - 1 - j))

def Stack.sample : Try.Sample (List Blake3.CV) where
  put := fun m st cvs =>
    let m := Try.fill m st (Array.replicate 1792 0#8)
    let m := Try.fill m st (Try.le64 (BitVec.ofNat 64 cvs.length)).toArray
    (cvs.zipIdx).foldl (fun m (cv, j) => Try.fill m (Stack.slot st cvs.length j) (Cv.bytes cv).toArray) m
  check := fun m st cvs =>
    decide (cvs.length ≤ 55) && (Try.bytes? m st 1792).isSome &&
    Try.bytes? m st 8 == some (Try.le64 (BitVec.ofNat 64 cvs.length)) &&
    (cvs.zipIdx).all fun (cv, j) => Try.bytes? m (Stack.slot st cvs.length j) 32 == some (Cv.bytes cv)
