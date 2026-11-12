import Abi
import Spec_stack
import Code_merge
open X86

/-! # `merge`: what is claimed

The statement only. Its proof is `Proof_merge.lean`, written by the compiler; nothing there need be read. -/

/-- **`merge(st, key, flags, plat, target)`.** With a stack of chaining values at `st` and the key at
`key`, a target of at least one and the mode's flags below 256: on return the stack is the
specification's `mergeTo` of it (while it holds more than `target` values, the two newest become their
parent node's chaining value) and the result is its count. Only the stack's bytes may change. `plat`
chooses the kernel and changes nothing else. -/
def Merge.contract (st key flags plat target : BitVec 64) (k : Blake3.CV) (cvs : List Blake3.CV) : Abi.Contract where
  args := [st, key, flags, plat, target]
  stack := 176#64
  regions := [(st, 1792#64), (key, 32#64)]
  requires := fun m => 1#64 ≤ target ∧ flags < 256#64 ∧ Stack.At m st cvs ∧ Cv.At m key k
  ensures := fun result m =>
    Stack.At m st (Blake3.mergeTo k ⟨flags.setWidth 32⟩ target.toNat cvs) ∧
    result.toNat = (Blake3.mergeTo k ⟨flags.setWidth 32⟩ target.toNat cvs).length
  modifies := [(st, 1792#64)]

/-- The function at 0x60000 of the assembled program meets that contract, whatever its arguments. -/
def Merge.statement : Prop :=
  ∀ (st key flags plat target : BitVec 64) (k : Blake3.CV) (cvs : List Blake3.CV),
    Abi.Meets Code_merge.prog 0x60000 (Merge.contract st key flags plat target k cvs)
