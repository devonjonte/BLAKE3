import Abi
import Spec_bytes
import Spec_stack
import Chunk
open X86

/-! # `hashl`: what is claimed

Definitions only. The theorem is `hashl_meets` (`Proof_hashl.lean`, written by the compiler): the whole
one-shot hash, by small functions each called by its contract. -/

/-- The first eight words of BLAKE3's output for a message under a key and a mode's flags: the output of
the root of the tree over the message's chunks (C2SP's BLAKE3, sections 4.2 to 4.4). Their 32 bytes are
`Blake3.blake3 k mode message 32` (`Blake3.blake3_32`, `../alg/Chunk.lean`). -/
def Hash.words (k : Blake3.CV) (flags : BitVec 64) (bytes : List (BitVec 8)) : Blake3.CV :=
  Blake3.rootWords (Blake3.tree k ⟨flags.setWidth 32⟩ (Blake3.chunksOf k ⟨flags.setWidth 32⟩ (Blake3.ofBytes bytes)))

/-- **`hashl(out, input, len, key, flags, plat)`.** With the `len` bytes of a message at `input` and the
key's eight words at `key`: the 32 bytes at `out` become the first 32 bytes of BLAKE3's output for the
message under that key and the mode's flags (below 256). The message and the key are unchanged. `plat`
chooses the kernels and changes nothing else. Any message whose length `len` can say: BLAKE3's own bound,
2^64 - 1 bytes (2^54 chunks, which the levels hold). -/
def Hashl.contract (out input len key flags plat : BitVec 64) (k : Blake3.CV) (bytes : List (BitVec 8)) : Abi.Contract where
  args := [out, input, len, key, flags, plat]
  stack := 4608#64
  accepts := len.toNat = bytes.length ∧ flags < 256#64
  reads := [Cv.layout.keeps key k, (Bytes.layout bytes.length).keeps input bytes]
  updates := [Cv.layout.fills out (Hash.words k flags bytes)]
  returns := fun _ => True
