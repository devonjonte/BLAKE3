import Try
import Spec_ptrs
open X86

/-! # A table of addresses, for trying functions on examples

How to put one into memory and how to test that memory holds it. Test-side: not proved against `Ptrs.At`. -/

def Ptrs.sample : Try.Sample (Nat → BitVec 64) where
  put := fun m a f => Try.fill m a ((List.range 32).flatMap fun j => Try.le64 (f j)).toArray
  check := fun m a f => Try.bytes? m a 256 == some ((List.range 32).flatMap fun j => Try.le64 (f j))
