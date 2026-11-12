import Abi
import Spec_node
open X86

/-! # `node_out`: what is claimed

Definitions only. The theorem is `node_out_meets` (`Proof_node_out.lean`, written by the compiler). -/

/-- **`node_out(out, nd, root, plat)`.** For the node at `nd`: the 32 bytes at `out` become the first eight
words of its compression: its chaining value where `root` is 0, the first 32 bytes of its output where
`root` is the `ROOT` flag (8). The node is unchanged. `plat` chooses the kernel and changes nothing else. -/
def NodeOut.contract (out nd root plat : BitVec 64) (node : Blake3.Node) : Abi.Contract where
  args := [out, nd, root, plat]
  stack := 256#64
  accepts := root = 0#64 ∨ root = 8#64
  reads := [Node.layout.keeps nd node]
  updates := [Cv.layout.fills out (Node.out node ⟨root.setWidth 32⟩)]
  returns := fun _ => True
