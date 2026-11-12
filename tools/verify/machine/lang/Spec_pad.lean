import Abi
import Spec_bytes
open X86

/-! # `pad`: what is claimed

Definitions only. The theorem is `pad_meets` (`Proof_pad.lean`, written by the compiler). -/

/-- **`pad(block, src, n)`.** The 64 bytes at `block` become the `n` bytes at `src` (at most 64) with zeros
after them: a chunk's last block as a compression reads it (C2SP's BLAKE3, section 4.2: "Short or empty
blocks are padded with zeros (0x00) to be 64 bytes"). The bytes at `src` are unchanged. -/
def Pad.contract (block src n : BitVec 64) (bytes : List (BitVec 8)) : Abi.Contract where
  args := [block, src, n]
  stack := 64#64
  accepts := n.toNat = bytes.length ∧ bytes.length ≤ 64
  reads := [(Bytes.layout bytes.length).keeps src bytes]
  updates := [(Bytes.layout 64).fills block (bytes ++ List.replicate (64 - bytes.length) 0#8)]
  returns := fun _ => True
