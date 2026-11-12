import Contract
import HexText

/-! # `hex`: what is claimed, of the code for any machine

Definitions only. The theorems: `hex_meets_bytes` (`../lang/Meets_hex_bytes.lean`: the x86-64 kernel, on
our model, with what an observer sees) and `hex_neon_meets` (`../arm/HexNeonBytes.lean`: the AArch64
kernel, on Google DeepMind's model). -/

/-- **`hex(out, hash)`.** The 64 bytes at `out` become the hexadecimal of the 32 bytes at `hash`, which
are unchanged. -/
def Hex.byteContract (out inp : BitVec 64) (hash : List (BitVec 8)) : Bytes.Contract where
  args := [out, inp]
  accepts := True
  reads := [(Bytes.plain 32).keeps inp hash]
  updates := [(Bytes.plain 64).fills out (Hex.text hash)]
  returns := fun _ => True
