import Abi
import Spec_stack
import Spec_merge
open X86

/-! # `add`: what is claimed

Definitions only. The theorem is `add_meets` (`Proof_add.lean`, written by the compiler). -/

/-- **`add(st, key, flags, plat, cv, target)`.** A chunk's chaining value arrives: for a stack of fewer
than 55 values at `st`, a target of at least one and the mode's flags below 256, the stack turns into
`Merge.result` of the stack with the value at `cv` on it, under the key at `key`, and the result is its count. -/
def Add.contract (st key flags plat cv target : BitVec 64) (k new : Blake3.CV) (cvs : List Blake3.CV) : Abi.Contract where
  args := [st, key, flags, plat, cv, target]
  stack := 512#64
  accepts := cvs.length < 55 ∧ 1#64 ≤ target ∧ flags < 256#64
  reads := [Cv.layout.keeps key k, Cv.layout.keeps cv new]
  updates := [Stack.layout.turns st cvs (Merge.result k flags target (new :: cvs))]
  returns := fun result => result.toNat = (Merge.result k flags target (new :: cvs)).length
