import Machine
open X86

/-! # The specification of the hash's hexadecimal

Two characters a byte, the high four bits first, from `0123456789abcdef`. -/

namespace Hex

/-- The character of a number below 16. -/
def hexc (n : BitVec 8) : BitVec 8 := bif n.ult 10 then n + 0x30 else n + 0x57

/-- A byte's first character (its high four bits) and its second (its low four). -/
def hi (b : BitVec 8) : BitVec 8 := hexc (b >>> 4)
def lo (b : BitVec 8) : BitVec 8 := hexc (b &&& 0xF)

/-- The sixteen characters of bytes `k` to `k + 7` of the vector `v`, as a vector: its lowest byte
is the first character. -/
def hex8 (v : V) (k : Nat) : V :=
  lo (by8 v (k + 7)) ++ hi (by8 v (k + 7)) ++ lo (by8 v (k + 6)) ++ hi (by8 v (k + 6)) ++
    lo (by8 v (k + 5)) ++ hi (by8 v (k + 5)) ++ lo (by8 v (k + 4)) ++ hi (by8 v (k + 4)) ++
    lo (by8 v (k + 3)) ++ hi (by8 v (k + 3)) ++ lo (by8 v (k + 2)) ++ hi (by8 v (k + 2)) ++
    lo (by8 v (k + 1)) ++ hi (by8 v (k + 1)) ++ lo (by8 v k) ++ hi (by8 v k)

end Hex
