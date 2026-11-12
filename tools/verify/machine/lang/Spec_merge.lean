import Abi
import Spec_stack
open X86

/-! # `merge`: what is claimed

Definitions only. The theorem is `merge_meets` (`Proof_merge.lean`, written by the compiler): the
function `merge` of the assembled program meets `Merge.contract`, whatever its arguments. -/

/-- What merging leaves of a stack `cvs`: the specification's `mergeTo` (while more than `target` values
are held, the two newest become their parent node's chaining value), under the key `k` and the mode's
flags. -/
def Merge.result (k : Blake3.CV) (flags target : BitVec 64) (cvs : List Blake3.CV) : List Blake3.CV :=
  Blake3.mergeTo k ⟨flags.setWidth 32⟩ target.toNat cvs

/-- **`merge(st, key, flags, plat, target)`.** For a target of at least one and the mode's flags below 256:
the stack at `st` turns into `Merge.result` of it, under the key at `key`, and the result is its count.
`plat` chooses the kernel and changes nothing else. -/
def Merge.contract (st key flags plat target : BitVec 64) (k : Blake3.CV) (cvs : List Blake3.CV) : Abi.Contract where
  args := [st, key, flags, plat, target]
  stack := 256#64
  accepts := 1#64 ≤ target ∧ flags < 256#64
  reads := [Cv.layout.keeps key k]
  updates := [Stack.layout.turns st cvs (Merge.result k flags target cvs)]
  returns := fun result => result.toNat = (Merge.result k flags target cvs).length
