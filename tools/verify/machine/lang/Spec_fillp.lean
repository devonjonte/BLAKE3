import Abi
import Spec_ptrs
open X86

/-! # `fillp`: what is claimed

Definitions only. The theorem is `fillp_meets` (`Proof_fillp.lean`, written by the compiler). -/

/-- **`fillp(ptrs, base, n, stride)`.** The 32 addresses at `ptrs` become `base`, `base + stride`, ... for
the first `n` lanes, and `base` again for every lane past them (`Ptrs.spread`). -/
def Fillp.contract (ptrs base n stride : BitVec 64) : Abi.Contract where
  args := [ptrs, base, n, stride]
  stack := 64#64
  accepts := True
  reads := []
  updates := [Ptrs.layout.fills ptrs (Ptrs.spread base n stride)]
  returns := fun _ => True
