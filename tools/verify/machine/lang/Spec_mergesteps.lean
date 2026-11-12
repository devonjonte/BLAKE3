import Abi
import Spec_stack
import Spec_merge
open X86

/-! # `merge_steps`: what is claimed

Definitions only. The theorem is `merge_steps_meets` (`Proof_merge_steps.lean`, written by the compiler). -/

/-- **`merge_steps(st, key, flags, plat, target)`**: what `Merge.contract` says of `merge`, word for word,
with more stack: this one calls `merge`, so it needs `merge`'s stack and its own. -/
def MergeSteps.contract (st key flags plat target : BitVec 64) (k : Blake3.CV) (cvs : List Blake3.CV) : Abi.Contract where
  args := [st, key, flags, plat, target]
  stack := 512#64
  accepts := 1#64 ≤ target ∧ flags < 256#64
  reads := [Cv.layout.keeps key k]
  updates := [Stack.layout.turns st cvs (Merge.result k flags target cvs)]
  returns := fun result => result.toNat = (Merge.result k flags target cvs).length
