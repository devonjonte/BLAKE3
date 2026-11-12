import Abi
import Spec_bytes
open X86

/-! # `hex`: what is claimed

Definitions only. The theorem is `hex_meets` (`Proof_hex.lean`, written by the compiler): for all
addresses, `Abi.MeetsQuietly` of the assembled `hex` and `Hex.contract`, the hash being what an
observer must not learn. -/

/-- The character of a number below 16: `0` to `9`, then `a` to `f`. -/
def Hex.char (n : BitVec 8) : BitVec 8 := if n < 10#8 then n + 0x30#8 else n + 0x57#8

/-- The hexadecimal of bytes: two characters a byte, its high four bits first. -/
def Hex.text (bs : List (BitVec 8)) : List (BitVec 8) :=
  bs.flatMap fun (b : BitVec 8) => [Hex.char (b >>> 4), Hex.char (b &&& 15#8)]

/-- **`hex(out, hash)`.** The 64 bytes at `out` become the hexadecimal of the 32 bytes at `hash`. -/
def Hex.contract (out inp : BitVec 64) (hash : List (BitVec 8)) : Abi.Contract where
  args := [out, inp]
  stack := 0#64
  accepts := True
  reads := [(Bytes.layout 32).keeps inp hash]
  updates := [(Bytes.layout 64).fills out (Hex.text hash)]
  returns := fun _ => True
