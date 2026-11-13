import Try
import Sample_stack
import Spec_cvl
open X86

/-! # Chaining values one after another, for trying functions on examples

How to put some into memory and how to test that memory holds them. Test-side: not proved against `Cvl.At`. -/

def Cvl.bytes (l : List Blake3.CV) : List (BitVec 8) := l.flatMap Cv.bytes

def Cvs16.sample : Try.Sample (List Blake3.CV) where
  put := fun m a l => Try.fill m a (Cvl.bytes l).toArray
  check := fun m a l => decide (l.length = 16) && Try.bytes? m a 512 == some (Cvl.bytes l)

def Cvs32.sample : Try.Sample (List Blake3.CV) where
  put := fun m a l => Try.fill m a (Cvl.bytes l).toArray
  check := fun m a l => decide (l.length = 32) && Try.bytes? m a 1024 == some (Cvl.bytes l)

def Pairs.sample (n : BitVec 64) : Try.Sample (List Blake3.CV) where
  put := fun m a l => Try.fill m a (Cvl.bytes l).toArray
  check := fun m a l => decide (n ≤ 16#64) && decide (l.length = 2 * n.toNat) && Try.bytes? m a (64 * n.toNat) == some (Cvl.bytes l)
