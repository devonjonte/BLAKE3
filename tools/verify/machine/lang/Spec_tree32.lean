import Abi
import Spec_p16
open X86

/-! # `tree32`: what is claimed

Definitions only. The theorem is `tree32_meets` (`Proof_tree32.lean`, written by the compiler), over any
program in which the 16-lane parent kernel's address meets `P16.contract`. -/

/-- The value of the tree over 32 values: five levels of parents. -/
def Tree32.value (k : Blake3.CV) (flags : BitVec 64) (l : List Blake3.CV) : Blake3.CV :=
  ((Tree.level k ⟨flags.setWidth 32⟩ (Tree.level k ⟨flags.setWidth 32⟩ (Tree.level k ⟨flags.setWidth 32⟩
    (Tree.level k ⟨flags.setWidth 32⟩ (Tree.level k ⟨flags.setWidth 32⟩ l))))).headD (Vector.replicate 8 0))

/-- **`tree32(res, cvs, key, flags)`.** With 32 chaining values at `cvs` and the key at `key`: the sixteen
values at `res` all become the value of the tree over the 32 (`Tree32.value`: 16 parents, 8, 4, 2, 1), each
level by the 16-lane parent kernel (its last call has one pair, and writes that pair's parent in all sixteen
lanes). The 32 values and the key are unchanged. The mode's flags are below 256. -/
def Tree32.contract (res cvs key flags : BitVec 64) (k : Blake3.CV) (l : List Blake3.CV) : Abi.Contract where
  args := [res, cvs, key, flags]
  stack := 8192#64
  accepts := flags < 256#64
  reads := [Cv.layout.keeps key k, Cvs32.layout.keeps cvs l]
  updates := [Cvs16.layout.fills res (List.replicate 16 (Tree32.value k flags l))]
  returns := fun _ => True
