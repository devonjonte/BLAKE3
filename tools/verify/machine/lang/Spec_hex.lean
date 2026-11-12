import Abi
import Spec_bytes
import HexText
open X86

/-! # `hex`: what is claimed

Definitions only; the hexadecimal itself is `Hex.text` (`../spec/HexText.lean`, shared with AArch64).
The theorem is `hex_meets` (`Meets_hex.lean`): for all
addresses, `Abi.MeetsQuietly` of the assembled `hex` and `Hex.contract`, the hash being what an
observer must not learn. -/

/-- **`hex(out, hash)`.** The 64 bytes at `out` become the hexadecimal of the 32 bytes at `hash`. -/
def Hex.contract (out inp : BitVec 64) (hash : List (BitVec 8)) : Abi.Contract where
  args := [out, inp]
  stack := 0#64
  accepts := True
  reads := [(Bytes.layout 32).keeps inp hash]
  updates := [(Bytes.layout 64).fills out (Hex.text hash)]
  returns := fun _ => True
