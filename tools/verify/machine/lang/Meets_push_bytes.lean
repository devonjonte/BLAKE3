import Proof_push
import StackAsBytes
open X86

/-! # `push` on x86-64 meets the contract that names no machine

`Push.byteContract` (`../spec/PushContract.lean`) is the statement; `../arm/PushBytes.lean` proves the
AArch64 code of the same source function against the same statement, on Google DeepMind's model. -/

/-- **The x86-64 code of `push` meets `Push.byteContract`**, with 64 bytes of stack. -/
theorem push_meets_bytes (st cv : BitVec 64) (new : Blake3.CV) (cvs : List Blake3.CV) :
    Abi.Meets Code_push.prog 0x70000 (Abi.ofBytes (Push.byteContract st cv new cvs) 64#64) := by
  rw [Push.contract_eq]
  exact Proof_push.push_meets st cv new cvs

#print axioms push_meets_bytes
