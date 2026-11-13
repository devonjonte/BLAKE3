import Abi
import Spec_bytes
import Spec_node
import Chunk
open X86

/-! # `chunk_node`: what is claimed

Definitions only. The theorem is `chunk_node_meets` (`Proof_chunk_node.lean`, written by the compiler). -/

/-- The specification's node of chunk number `counter` of a message, `bytes` being the chunk's bytes, under
the key `k` and the mode's flags (`Blake3.chunkNode`, C2SP's BLAKE3 section 4.2). -/
def Chunk.node (k : Blake3.CV) (flags counter : BitVec 64) (bytes : List (BitVec 8)) : Blake3.Node :=
  Blake3.chunkNode k ⟨flags.setWidth 32⟩ (Blake3.ofBytes bytes) counter.toNat

/-- **`chunk_node(nd, input, len, counter, flags, plat)`.** With the `len` bytes (at most 1024) of chunk
number `counter` of a message at `input`, and the key in the first 32 bytes at `nd`: the 120 bytes at `nd`
become the specification's node of that chunk, its `h` in the first 32 and the rest in the 88 after them.
The chunk's bytes are unchanged. The mode's flags are below 256. `plat` chooses the kernel and changes
nothing else. -/
def ChunkNode.contract (nd input len counter flags plat : BitVec 64) (k : Blake3.CV) (bytes : List (BitVec 8)) : Abi.Contract where
  args := [nd, input, len, counter, flags, plat]
  stack := 256#64
  accepts := len.toNat = bytes.length ∧ bytes.length ≤ 1024 ∧ flags < 256#64
  reads := [(Bytes.layout bytes.length).keeps input bytes]
  updates := [Cv.layout.turns nd k (Chunk.node k flags counter bytes).h,
              NodeTail.layout.fills (nd + 32#64) (Chunk.node k flags counter bytes)]
  returns := fun _ => True
