import Arm64
import ProofLib
import Contract
open Arm64 ProofLib

/-! # A contract that names no machine, as a specification in Google DeepMind's logic

Read once. Definitions only. A `Bytes.Contract` (`../spec/Contract.lean`) says what a function is given and
leaves, of bytes at addresses. Here: what that says of AArch64 code on their model (`Spec`, of which their
`subroutineOk` says that the code, called with the precondition, returns with the postcondition, touching
no memory but what the precondition owns and its own stack). The arguments are in X0 to X5 and the result
in X0 (AAPCS64). -/

namespace ArmAbi

/-- Some bytes, as many as `size`, of which `P` holds, are at `addr`, and the function may change them. -/
def owns (addr : BitVec 64) (size : Nat) (P : List (BitVec 8) → Prop) : SepProp :=
  ∃∗ b, ⌜b.length = size ∧ P b⌝ ∗ (addr ↦ₛ b)

/-- All of these, each on memory of its own. -/
def all : List SepProp → SepProp
  | [] => SepProp.emp
  | p :: ps => p ∗ all ps

/-- **The contract `c`, for AArch64.** `r` is the bytes of the pieces the function does not change, one
list a piece: they are at their addresses at the call, as the contract says, and the same bytes are there at
the return. -/
def spec (c : Bytes.Contract) : Spec (List (List (BitVec 8))) where
  pre := fun r s0 =>
    ⌜c.args = [s0.readReg64 .x0, s0.readReg64 .x1, s0.readReg64 .x2, s0.readReg64 .x3, s0.readReg64 .x4,
        s0.readReg64 .x5].take c.args.length ∧
      c.accepts ∧ r.length = c.reads.length ∧ ∀ pb ∈ c.reads.zip r, pb.2.length = pb.1.size ∧ pb.1.before pb.2⌝ ∗
    all (c.updates.map fun p => owns p.addr p.size p.before) ∗
    all (List.zipWith (fun p b => p.addr ↦ₛ b) c.reads r)
  post := fun r _ sf =>
    ⌜c.returns (sf.readReg64 .x0)⌝ ∗
    all (c.updates.map fun p => owns p.addr p.size p.after) ∗
    all (List.zipWith (fun p b => p.addr ↦ₛ b) c.reads r)

end ArmAbi
