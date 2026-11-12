import HexText
import KernelAttr

/-! # The hexadecimal in 16-byte vectors: what the NEON kernel computes, stated on its own terms

The kernel reads and writes sixteen bytes at a time; its own contract (the source's clauses) says which
vector is written for which read. `HexNeonBytes.lean` carries that to the reader's statement in bytes
(`Hex.text`). -/

namespace Hex

/-- Byte `i` of a vector. -/
def byte (v : BitVec 128) (i : Nat) : BitVec 8 := v.extractLsb' (8 * i) 8

/-- The sixteen characters of bytes `k` to `k + 7` of `v`, as a vector whose lowest byte is the first. -/
def hex16 (v : BitVec 128) (k : Nat) : BitVec 128 :=
  char (byte v (k + 7) &&& 15#8) ++ char (byte v (k + 7) >>> 4) ++ char (byte v (k + 6) &&& 15#8) ++ char (byte v (k + 6) >>> 4) ++
  char (byte v (k + 5) &&& 15#8) ++ char (byte v (k + 5) >>> 4) ++ char (byte v (k + 4) &&& 15#8) ++ char (byte v (k + 4) >>> 4) ++
  char (byte v (k + 3) &&& 15#8) ++ char (byte v (k + 3) >>> 4) ++ char (byte v (k + 2) &&& 15#8) ++ char (byte v (k + 2) >>> 4) ++
  char (byte v (k + 1) &&& 15#8) ++ char (byte v (k + 1) >>> 4) ++ char (byte v k &&& 15#8) ++ char (byte v k >>> 4)

/-- `char` in the form the bit-blaster takes. -/
theorem char_bif (n : BitVec 8) : char n = bif n.ult 10#8 then n + 0x30#8 else n + 0x57#8 := by
  simp only [char]
  bv_decide

attribute [kernel_spec] hex16 byte char_bif

end Hex
