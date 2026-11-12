import Try
import Spec_bytes
open X86

/-! # Plain bytes, for trying functions on examples

How to put some into memory and how to test that memory holds them. Test-side: not proved against `Bytes.At`. -/

def Bytes.sample (n : Nat) : Try.Sample (List (BitVec 8)) where
  put := fun m a bs => Try.fill m a bs.toArray
  check := fun m a bs => decide (bs.length = n) && Try.bytes? m a n == some bs
