import Abi
import Spec_cvl
import Spec_ptrs
open X86

/-! # The 16-lane parent kernel: the contract its callers assume

`blake3_servil_avx512_p16` of the library (AVX-512, 16 inputs of one block at a time) is not in this
machine model: it uses registers and instructions the model does not have. A function that calls it is
proved over any program in which the kernel's address meets this contract. The library proves its kernels
with another system (Z3); this is that kernel's contract as our callers use it, written by hand, and a slow
function of ours that meets it is the witness that it can be met. Definitions only. -/

/-- One level of a tree: each pair's parent value, in order (C2SP's BLAKE3, section 4.3.1). -/
def Tree.level (k : Blake3.CV) (mode : Blake3.Word) : List Blake3.CV → List Blake3.CV
  | x :: y :: rest => (Blake3.parentNode k mode x y).cv :: Tree.level k mode rest
  | _ => []

/-- What the kernel writes for `n` pairs: their `n` parents, then the first pair's parent again in every
lane past them. -/
def P16.values (k : Blake3.CV) (flags n : BitVec 64) (l : List Blake3.CV) : List Blake3.CV :=
  Tree.level k ⟨flags.setWidth 32⟩ l ++
    List.replicate (16 - n.toNat) ((Tree.level k ⟨flags.setWidth 32⟩ l).headD (Vector.replicate 8 0))

/-- **`blake3_servil_avx512_p16(inputs, blocks, key, counter, packed, out)`**, as our callers use it: one
block an input, counter 0, the flags `flags | PARENT` with a block length of 64 packed above them; the table
at `inputs` holds the addresses of `n` pairs one after another from `base` (1 to 16 pairs) and `base` again
in the lanes past them. The 16 values at `out` become the pairs' parents under the key at `key`
(`P16.values`). The key, the table and the pairs are unchanged. -/
def P16.contract (inputs blocks key counter packed out : BitVec 64) (k : Blake3.CV) (base n flags : BitVec 64)
    (l : List Blake3.CV) : Abi.Contract where
  args := [inputs, blocks, key, counter, packed, out]
  stack := 4096#64
  accepts := blocks = 1#64 ∧ counter = 0#64 ∧ packed = flags ||| 0x40000004#64 ∧ flags < 256#64 ∧ 1#64 ≤ n ∧ n ≤ 16#64
  reads := [Cv.layout.keeps key k, Ptrs.layout.keeps inputs (Ptrs.spread base n 64#64), (Pairs.layout n).keeps base l]
  updates := [Cvs16.layout.fills out (P16.values k flags n l)]
  returns := fun _ => True
