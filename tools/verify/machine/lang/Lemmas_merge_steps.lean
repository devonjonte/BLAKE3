import Lemmas_merge
import Spec_mergesteps
open X86 Cells

/-! # `merge_steps`: lemmas for the prover

`merge_steps` merges one level at a time, each by a call of `merge` with a target one less than the count.
Merging to a target, then to a smaller one, is merging to the smaller one. Written by hand for this
function; checked by Lean; not to be read. -/

namespace Blake3

/-- `mergeTo` on a stack of two or more, written out. -/
theorem mergeTo_cons2 (key : CV) (mode : Word) (t : Nat) (top second : CV) (below : List CV) :
    mergeTo key mode t (top :: second :: below) =
      if t < below.length + 2 then mergeTo key mode t ((parentNode key mode second top).cv :: below) else top :: second :: below := by
  rw [mergeTo]

/-- **Merging to `b`, then to `a ≤ b`, is merging to `a`.** -/
theorem mergeTo_mergeTo (key : CV) (mode : Word) (a b : Nat) (hab : a ≤ b) : ∀ (n : Nat) (l : List CV), l.length = n →
    mergeTo key mode a (mergeTo key mode b l) = mergeTo key mode a l := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro l hl
    match l, hl with
    | [], _ => simp [mergeTo]
    | [_], _ => simp [mergeTo]
    | top :: second :: below, hl =>
      rw [mergeTo_cons2 key mode b]
      split
      · rename_i hb
        rw [ih (below.length + 1) (by simp only [List.length_cons] at hl; omega) _ (by simp)]
        rw [mergeTo_cons2 key mode a, if_pos (by omega)]
      · rfl

/-- One level: a stack of `t + 1` values (two or more) merged to `t` holds `t`. -/
theorem mergeTo_pred_length (key : CV) (mode : Word) (t : Nat) (l : List CV) (hl : l.length = t + 1) (ht : 1 ≤ t) :
    (mergeTo key mode t l).length = t := by
  match l, hl with
  | [_], hl => simp only [List.length_cons, List.length_nil] at hl; omega
  | top :: second :: below, hl =>
    simp only [List.length_cons] at hl
    rw [mergeTo_cons2, if_pos (by omega)]
    match below, hl with
    | [], hl => simp only [List.length_nil] at hl; simp [mergeTo]; omega
    | s :: b', hl =>
      simp only [List.length_cons] at hl
      rw [mergeTo_cons2, if_neg (by omega)]
      simp only [List.length_cons]; omega

end Blake3

/-- The count after a level is merged. -/
theorem MergeSteps.count {m : Mem} {st len target flags : BitVec 64} {k : Blake3.CV} {now : List Blake3.CV}
    (h : Stack.At m st now) (hl : len = Stack.count now) (ht : target < len) (h1 : 1#64 ≤ target) :
    len - 1#64 = Stack.count (Merge.result k flags (len - 1#64) now) := by
  have hc := Stack.count_toNat h.1
  have hn : now.length = (len - 1#64).toNat + 1 := by rw [← hc, ← hl]; bv_omega
  have := Blake3.mergeTo_pred_length k ⟨flags.setWidth 32⟩ (len - 1#64).toNat now hn (by bv_omega)
  apply BitVec.eq_of_toNat_eq
  simp only [Stack.count, Merge.result, this, BitVec.toNat_ofNat]
  omega

/-- What is left to merge gives what it gave. -/
theorem MergeSteps.result {m : Mem} {st len target flags : BitVec 64} {k : Blake3.CV} {now cvs : List Blake3.CV}
    (h : Stack.At m st now) (hl : len = Stack.count now) (ht : target < len)
    (he : Merge.result k flags target now = Merge.result k flags target cvs) :
    Merge.result k flags target (Merge.result k flags (len - 1#64) now) = Merge.result k flags target cvs := by
  rw [← he]
  simp only [Merge.result]
  exact Blake3.mergeTo_mergeTo k ⟨flags.setWidth 32⟩ target.toNat (len - 1#64).toNat (by bv_omega) now.length now rfl
