/-! # The hexadecimal of bytes: the specification

What `Hash::to_hex` writes, for every architecture's contract to name. Lean's core library only: no
machine, no code. -/

namespace Hex

/-- The character of a number below 16: `0` to `9`, then `a` to `f`. -/
def char (n : BitVec 8) : BitVec 8 := if n < 10#8 then n + 0x30#8 else n + 0x57#8

/-- The hexadecimal of bytes: two characters a byte, its high four bits first. -/
def text (bs : List (BitVec 8)) : List (BitVec 8) :=
  bs.flatMap fun (b : BitVec 8) => [char (b >>> 4), char (b &&& 15#8)]

end Hex

/-- For example: the bytes 00, 1f, a9 give the characters `001fa9`. -/
example : Hex.text [0x00#8, 0x1f#8, 0xa9#8] = [0x30#8, 0x30#8, 0x31#8, 0x66#8, 0x61#8, 0x39#8] := by decide
