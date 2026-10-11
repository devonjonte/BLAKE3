import HasherProofs
import Hashercore
open Aeneas Aeneas.Std Result

namespace StackProof
open hashercore

abbrev Cv := Std.Array Std.U8 32#usize

/-- The stack's values, bottom first. -/
def vals (s : CvStack) : List Cv :=
  match s.cvs with
  | some a => a.val.take s.len.val
  | none => []

/-- At most 55 values, and an array whenever there is one. -/
def Inv (s : CvStack) : Prop := s.len.val ≤ 55 ∧ (s.cvs = none → s.len.val = 0)

/-- A stack's values top first: its top two, then the rest. -/
theorem take_reverse_top2 (l : List Cv) (m : Nat) (hl : m + 2 ≤ l.length) :
    (l.take (m + 2)).reverse = l[m + 1] :: l[m] :: (l.take m).reverse := by
  rw [List.take_add_one, List.take_add_one]
  simp [List.getElem?_eq_getElem (by omega : m < l.length), List.getElem?_eq_getElem (by omega : m + 1 < l.length)]

/-- One merge: the parent in the lower one's place, the top gone. -/
theorem set_take_reverse (l : List Cv) (m : Nat) (x : Cv) (hl : m + 2 ≤ l.length) :
    ((l.set m x).take (m + 1)).reverse = x :: (l.take m).reverse := by
  rw [List.take_add_one]
  simp [List.take_set_of_le (le_refl _), List.getElem?_set_self (by omega : m < l.length)]

/-- A value set just past a prefix extends it. -/
theorem take_set_succ (l : List Cv) (n : Nat) (x : Cv) (h : n < l.length) :
    (l.set n x).take (n + 1) = l.take n ++ [x] := by
  rw [List.take_add_one]
  simp [List.take_set_of_le (le_refl _), List.getElem?_set_self h]

/-- A stack no longer than its target is left as it is. -/
theorem merge_short {α : Type} (node : α → α → α) (t : Nat) (l : List α) (h : l.length ≤ t) :
    HasherProof.merge node t l = l := by
  match l, h with
  | [], _ => simp [HasherProof.merge]
  | [_], _ => simp [HasherProof.merge]
  | b :: a :: rest, h => simp only [HasherProof.merge]; rw [if_neg (by simp at h; omega)]

/-- One iteration keeps the merge's result: the top two values replaced by
their parent, below a stack longer than the target; `abs` reads a value,
`op` the parent of two read values. -/
theorem merge_step {β : Type} (abs : Cv → β) (op : β → β → β) (t : Nat) (l : List Cv) (m : Nat) (x : Cv)
    (hl : m + 2 ≤ l.length) (hx : abs x = op (abs l[m]) (abs l[m + 1])) (ht : t < m + 2) :
    HasherProof.merge op t (((l.set m x).take (m + 1)).reverse.map abs) =
      HasherProof.merge op t ((l.take (m + 2)).reverse.map abs) := by
  rw [set_take_reverse l m _ hl, take_reverse_top2 l m hl]
  simp only [List.map_cons]
  conv_rhs => rw [HasherProof.merge]
  rw [if_pos (by simp; omega), hx]

/-- The merge loop: on a stack of at most 55 values and a target of at least
1, it ends, and the values it leaves, top first and read by `abs`, are the
Hasher algorithm's merge of the stack's (HasherProofs.lean), `op` the parent
of two read values. -/
theorem merge_loop_spec {P β : Type} (PI : Parent P) (p : P) (abs : Cv → β) (op : β → β → β)
    (hp : ∀ a b, PI.parent p a b ⦃ v => abs v = op (abs a) (abs b) ⦄)
    (s : CvStack) (target : Std.Usize) (hinv : Inv s) (ht : 1 ≤ target.val) :
    CvStack.merge_loop PI s p target ⦃ r => Inv ⟨r.1, r.2⟩ ∧
      (vals ⟨r.1, r.2⟩).reverse.map abs = HasherProof.merge op target.val ((vals s).reverse.map abs) ⦄ := by
  unfold CvStack.merge_loop
  apply loop.spec_decr_nat (fun st : CvStack => st.len.val)
    (fun st : CvStack => Inv st ∧
      HasherProof.merge op target.val ((vals st).reverse.map abs) =
        HasherProof.merge op target.val ((vals s).reverse.map abs))
  · rintro st ⟨⟨hlen, hnone⟩, heq⟩
    unfold CvStack.merge_loop.body
    by_cases hgt : st.len > target
    · -- one merge: the top two become their parent
      have h2 : 2 ≤ st.len.val := by scalar_tac
      obtain ⟨arr, harr⟩ : ∃ arr, st.cvs = some arr := by
        cases h : st.cvs with
        | none => have := hnone h; omega
        | some arr => exact ⟨arr, rfl⟩
      have harrlen : arr.val.length = 55 := by simp
      have hge : st.len ≥ 2#usize := by scalar_tac
      simp only [hgt, harr, hge, massert, not_true_eq_false, decide_false, decide_true, Bool.false_or,
        ↓reduceIte]
      step as ⟨j, hj, hj1⟩
      step as ⟨a, ha⟩
      step as ⟨k, hk, hk1⟩
      step as ⟨b, hb⟩
      step with hp a b as ⟨c, hc⟩
      step as ⟨x, hx⟩
      step as ⟨i, hi, hi1⟩
      refine ⟨⟨by scalar_tac, by simp⟩, ?_, by scalar_tac⟩
      rw [← heq]
      simp only [vals, harr, hx, Std.Array.set_val_eq]
      obtain ⟨m, hm⟩ : ∃ m, st.len.val = m + 2 := ⟨st.len.val - 2, by omega⟩
      rw [show i.val = m + 1 by omega, show j.val = m by omega, hm]
      simp only [show j.val = m by omega, show k.val = m + 1 by omega] at ha hb
      exact merge_step abs op target.val arr.val m c (by omega) (by subst ha hb; exact hc) (by scalar_tac)

    · -- the loop ends: a stack no longer than its target is left as it is
      have hle : st.len.val ≤ target.val := by scalar_tac
      simp [hgt]
      refine ⟨⟨hlen, hnone⟩, ?_⟩
      have hvl : ((vals st).reverse.map abs).length ≤ target.val := by
        unfold vals; split <;> simp <;> omega
      rw [← List.map_reverse, ← List.map_reverse, ← heq, merge_short op _ _ hvl]
  · exact ⟨hinv, rfl⟩

/-- `merge`, as compiled from src/stack_core.rs: on a stack of at most 55
values and a target of at least 1, it never fails, and its values, top
first and read by `abs`, are the Hasher algorithm's merge of the old ones
(HasherProofs.lean), `op` the parent of two read values. -/
theorem merge_spec {P β : Type} (PI : Parent P) (p : P) (abs : Cv → β) (op : β → β → β)
    (hp : ∀ a b, PI.parent p a b ⦃ v => abs v = op (abs a) (abs b) ⦄)
    (s : CvStack) (target : Std.Usize) (hinv : Inv s) (ht : 1 ≤ target.val) :
    CvStack.merge PI s p target ⦃ s' => Inv s' ∧
      (vals s').reverse.map abs = HasherProof.merge op target.val ((vals s).reverse.map abs) ⦄ := by
  unfold CvStack.merge
  step with merge_loop_spec PI p abs op hp s target hinv ht as ⟨o, i, h, h'⟩
  exact ⟨h, h'⟩

/-- `push`: on a stack of fewer than 55 values, `cv` goes on top. -/
theorem push_spec (s : CvStack) (cv : Cv) (hinv : Inv s) (hlen : s.len.val < 55) :
    CvStack.push s cv ⦃ s' => Inv s' ∧ vals s' = vals s ++ [cv] ⦄ := by
  unfold CvStack.push
  cases hc : s.cvs with
  | none =>
    have h0 := hinv.2 hc
    simp only [core.option.Option.is_none, Option.isNone_none, ↓reduceIte]
    step*
    refine ⟨⟨by scalar_tac, by simp⟩, ?_⟩
    simp [vals, *, Std.Array.set_val_eq, Std.Array.repeat_val]
  | some arr =>
    simp only [core.option.Option.is_none, Option.isNone_some, Bool.false_eq_true, ↓reduceIte]
    step*
    refine ⟨⟨by scalar_tac, by simp⟩, ?_⟩
    simp only [vals, hc, i_post, x_post, Std.Array.set_val_eq]
    exact take_set_succ _ _ _ (by simp; omega)

end StackProof

#print axioms StackProof.merge_spec
#print axioms StackProof.push_spec
