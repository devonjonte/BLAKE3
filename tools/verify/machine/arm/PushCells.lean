import Arm64
import ProofLib
open Arm64 ProofLib

/-! # `push` on AArch64: a contract in cells

What `push` does, said of the cells it touches, in Google's logic: the count at `st` goes up by one and the
two vectors at `cv` are copied to the next place of the stack. This is not yet `Push.contract` (which says it
of the stack as a list, over the x86-64 model's memory): for that the contracts must name no machine
(`../lang/DESIGN.md`). It is what the trial needs: the same source function, printed for AArch64, proved on
their model. -/

structure PushCellsArgs where
  st : BitVec 64
  cv : BitVec 64
  len : BitVec 64
  n0 : BitVec 128
  n1 : BitVec 128
  d0 : BitVec 128
  d1 : BitVec 128

abbrev pushCellsSpec : Spec PushCellsArgs where
  pre := fun x s0 =>
    ⌜s0.readReg64 .x0 = x.st ∧ s0.readReg64 .x1 = x.cv⌝ ∗
    (x.st ↦₆₄ x.len) ∗
    ((x.st + 32#64 + (x.len <<< 5)) ↦₁₂₈ x.d0) ∗ ((x.st + 32#64 + (x.len <<< 5) + 16#64) ↦₁₂₈ x.d1) ∗
    (x.cv ↦₁₂₈ x.n0) ∗ ((x.cv + 16#64) ↦₁₂₈ x.n1)
  post := fun x _ _ =>
    (x.st ↦₆₄ (x.len + 1#64)) ∗
    ((x.st + 32#64 + (x.len <<< 5)) ↦₁₂₈ x.n0) ∗ ((x.st + 32#64 + (x.len <<< 5) + 16#64) ↦₁₂₈ x.n1) ∗
    (x.cv ↦₁₂₈ x.n0) ∗ ((x.cv + 16#64) ↦₁₂₈ x.n1)
