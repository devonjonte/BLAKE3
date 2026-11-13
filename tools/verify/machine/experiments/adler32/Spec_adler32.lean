import Abi
import Spec_bytes
open X86

/-! Adler-32's contract, in the arithmetic of RFC 1950 section 8.
The checksum is not a cryptographic authentication code. -/

namespace Adler32

def step (s : Nat × Nat) (byte : BitVec 8) : Nat × Nat :=
  let a := (s.1 + byte.toNat) % 65521
  (a, (s.2 + a) % 65521)

def sums (bytes : List (BitVec 8)) : Nat × Nat := bytes.foldl step (1, 0)

def checksum (bytes : List (BitVec 8)) : BitVec 64 :=
  BitVec.ofNat 64 ((sums bytes).2 * 65536 + (sums bytes).1)

/-- n readable bytes at input, unchanged; return their Adler-32 in the low 32 bits. -/
def contract (input n : BitVec 64) (bytes : List (BitVec 8)) : Abi.Contract where
  args := [input, n]
  stack := 64#64
  accepts := n.toNat = bytes.length
  reads := [(Bytes.layout bytes.length).keeps input bytes]
  updates := []
  returns := fun result => result = checksum bytes

example : checksum [] = 1#64 := by decide
example : checksum ([87, 105, 107, 105, 112, 101, 100, 105, 97].map (BitVec.ofNat 8)) = 0x11e60398#64 := by decide

end Adler32
