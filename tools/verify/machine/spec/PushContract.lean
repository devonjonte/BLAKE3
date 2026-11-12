import StackBytes

/-! # `push`: what is claimed, of the code for any machine

Definitions only. The theorems: `push_meets_bytes` (`../lang/Meets_push_bytes.lean`: the x86-64 code, on
our model) and `push_arm_meets` (`../arm/PushBytes.lean`: the AArch64 code, on Google DeepMind's model).
Both codes are printed from the one function `push` of `../lang/hasher.ode`. -/

/-- **`push(st, cv)`.** For a stack of fewer than 55 values at `st`: the value at `cv` becomes its newest;
the value at `cv` is unchanged. (No code tests the bound: a caller shows it.) -/
def Push.byteContract (st cv : BitVec 64) (new : Blake3.CV) (cvs : List Blake3.CV) : Bytes.Contract where
  args := [st, cv]
  accepts := cvs.length < 55
  reads := [Cv.byteLayout.keeps cv new]
  updates := [Stack.byteLayout.turns st cvs (new :: cvs)]
  returns := fun _ => True
