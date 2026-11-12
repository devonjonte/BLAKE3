import Abi
import Spec_levels
open X86

/-! # `lroot`: what is claimed

Definitions only. The theorem is `lroot_meets` (`Proof_lroot.lean`, written by the compiler): the function
`lroot` of the assembled program meets `Lroot.contract`, whatever its arguments. -/

/-- The first eight words of the specification's output for the tree over `chunks`: the root node's
compression with the `ROOT` flag and the output's counter 0 (sections 4.3.2 and 4.4). They are the first 32
bytes of `Blake3.output (Blake3.tree k mode chunks) n` for any `n ≥ 32`. -/
def Levels.rootCv (k : Blake3.CV) (mode : Blake3.Word) (chunks : Array Blake3.Node) : Blake3.CV :=
  Blake3.first8 (Blake3.BLAKE3_COMPRESS (Blake3.tree k mode chunks).h (Blake3.tree k mode chunks).m 0
    (Blake3.tree k mode chunks).len ((Blake3.tree k mode chunks).flags ||| Blake3.ROOT))

/-- **`lroot(out, lv, key, flags, plat)`.** For levels over two chunks or more at `lv`: the 32 bytes at `out`
become the first eight words of the specification's output for the tree over them; the levels and the key
are unchanged. The mode's flags are below 256. `plat` chooses the kernel and changes nothing else. -/
def Lroot.contract (out lv key flags plat : BitVec 64) (k : Blake3.CV) (chunks : Array Blake3.Node) : Abi.Contract where
  args := [out, lv, key, flags, plat]
  stack := 256#64
  accepts := 2 ≤ chunks.size ∧ flags < 256#64
  reads := [Cv.layout.keeps key k, (Levels.layout k ⟨flags.setWidth 32⟩).keeps lv chunks]
  updates := [Cv.layout.fills out (Levels.rootCv k ⟨flags.setWidth 32⟩ chunks)]
  returns := fun _ => True
