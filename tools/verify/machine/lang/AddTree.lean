import Spec_add
import Stack
open X86

/-! # `add` and the specification's tree

`Add.contract` says what `add` leaves in terms of `Blake3.mergeTo`. The algorithm's theorems
(`../alg/Stack.lean`, no machine in them) say what that is: the stack of the specification's tree. This
file joins the two, so that the contract's reader may read `Blake3.Stk` in place of `mergeTo`. -/

/-- **When a chunk's value arrives, `add` keeps the stack the tree's.** If the stack holds the chaining
values of the complete subtrees of the first `m` chunks (`Blake3.Stk`: one for each one bit of `m`), the
value that arrives is chunk `m`'s, and the target is the number of one bits of `m + 1`, then what
`Add.contract` says is left is that stack for the first `m + 1` chunks. -/
theorem Add.keeps_the_tree (k : Blake3.CV) (flags target : BitVec 64) (chunks : Array Blake3.Node) (m : Nat)
    (cvs : List Blake3.CV) (h : Blake3.Stk k ⟨flags.setWidth 32⟩ chunks 0 0 cvs m)
    (ht : target.toNat = Blake3.ones (m + 1)) :
    Blake3.Stk k ⟨flags.setWidth 32⟩ chunks 0 0
      (Merge.result k flags target (Blake3.sub k ⟨flags.setWidth 32⟩ chunks m 1 :: cvs)) (m + 1) := by
  have := Blake3.merge_lazy k ⟨flags.setWidth 32⟩ chunks cvs 0 m h
  simp only [Nat.pow_zero, Nat.zero_add] at this
  simpa only [Merge.result, ht] using this

#print axioms Add.keeps_the_tree
