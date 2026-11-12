import Abi
import Spec_stack
open X86

/-! # `push`: what is claimed

Definitions only. The theorem is `push_meets` (`Proof_push.lean`, written by the compiler). -/

/-- **`push(st, cv)`.** For a stack of fewer than 55 values at `st`: the value at `cv` becomes its newest;
the value at `cv` is unchanged. (No code tests the bound: a caller shows it.) -/
def Push.contract (st cv : BitVec 64) (new : Blake3.CV) (cvs : List Blake3.CV) : Abi.Contract where
  args := [st, cv]
  stack := 64#64
  accepts := cvs.length < 55
  reads := [Cv.layout.keeps cv new]
  updates := [Stack.layout.turns st cvs (new :: cvs)]
  returns := fun _ => True
