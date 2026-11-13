import Cells
import Lemmas_cvl
import Spec_tree32
open X86 Cells

/-! # `tree32`: lemmas for the prover

Written by hand for this function; its source names them. Checked by Lean; not to be read. -/

theorem Tree.level_length (k : Blake3.CV) (mode : Blake3.Word) : ∀ (n : Nat) (l : List Blake3.CV), l.length = 2 * n →
    (Tree.level k mode l).length = n := by
  intro n
  induction n with
  | zero => intro l h; have : l = [] := List.length_eq_zero_iff.mp (by omega); subst this; rfl
  | succ n ih =>
    intro l h
    match l, h with
    | x :: y :: rest, h =>
      simp only [Tree.level, List.length_cons]
      rw [ih rest (by simp only [List.length_cons] at h; omega)]

theorem P16.values_length (k : Blake3.CV) (flags n : BitVec 64) (l : List Blake3.CV) (hl : l.length = 2 * n.toNat)
    (hn : n.toNat ≤ 16) : (P16.values k flags n l).length = 16 := by
  simp only [P16.values, List.length_append, List.length_replicate, Tree.level_length k _ n.toNat l hl]; omega

/-- The kernel's first `n` values are the pairs' parents. -/
theorem P16.values_take (k : Blake3.CV) (flags n : BitVec 64) (l : List Blake3.CV) (hl : l.length = 2 * n.toNat) :
    (P16.values k flags n l).take n.toNat = Tree.level k ⟨flags.setWidth 32⟩ l := by
  have := Tree.level_length k ⟨flags.setWidth 32⟩ n.toNat l hl
  simp only [P16.values]
  rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]

/-- One pair: its parent in all sixteen lanes. -/
theorem P16.values_one (k : Blake3.CV) (flags : BitVec 64) (X : List Blake3.CV) (v : Blake3.CV)
    (h : Tree.level k ⟨flags.setWidth 32⟩ X = [v]) : P16.values k flags 1#64 X = List.replicate 16 v := by
  unfold P16.values
  rw [h]; rfl

namespace Tree32

/-- What the kernel leaves after each of the five calls. -/
abbrev l1 (k : Blake3.CV) (flags : BitVec 64) (l : List Blake3.CV) : List Blake3.CV := P16.values k flags 16#64 l
abbrev l2 (k : Blake3.CV) (flags : BitVec 64) (l : List Blake3.CV) : List Blake3.CV := P16.values k flags 8#64 (l1 k flags l)
abbrev l3 (k : Blake3.CV) (flags : BitVec 64) (l : List Blake3.CV) : List Blake3.CV := P16.values k flags 4#64 ((l2 k flags l).take 8)
abbrev l4 (k : Blake3.CV) (flags : BitVec 64) (l : List Blake3.CV) : List Blake3.CV := P16.values k flags 2#64 ((l3 k flags l).take 4)
abbrev l5 (k : Blake3.CV) (flags : BitVec 64) (l : List Blake3.CV) : List Blake3.CV := P16.values k flags 1#64 ((l4 k flags l).take 2)

variable {m : Mem} {cvs a : BitVec 64} {k : Blake3.CV} {flags : BitVec 64} {l : List Blake3.CV}

theorem len1 (hl : l.length = 32) : (l1 k flags l).length = 16 := P16.values_length k flags _ l (by rw [hl]; decide) (by decide)
theorem len2 (hl : l.length = 32) : (l2 k flags l).length = 16 := P16.values_length k flags _ _ (by rw [len1 hl]; decide) (by decide)
theorem len3 (hl : l.length = 32) : (l3 k flags l).length = 16 :=
  P16.values_length k flags _ _ (by rw [List.length_take, len2 hl]; decide) (by decide)
theorem len4 (hl : l.length = 32) : (l4 k flags l).length = 16 :=
  P16.values_length k flags _ _ (by rw [List.length_take, len3 hl]; decide) (by decide)

/-- **Before each call:** the pairs it is given. -/
theorem in1 (h : Cvs32.At m cvs l) : Pairs.At 16#64 m cvs l := ⟨by decide, by rw [h.1]; decide, h.2⟩
theorem in2 (h : Cvs16.At m a (l1 k flags l)) : Pairs.At 8#64 m a (l1 k flags l) := ⟨by decide, by rw [h.1]; decide, h.2⟩
theorem in3 (h : Cvs16.At m a (l2 k flags l)) : Pairs.At 4#64 m a ((l2 k flags l).take 8) :=
  ⟨by decide, by rw [List.length_take, h.1]; decide, Cvl.At.take _ _ _ h.2⟩
theorem in4 (h : Cvs16.At m a (l3 k flags l)) : Pairs.At 2#64 m a ((l3 k flags l).take 4) :=
  ⟨by decide, by rw [List.length_take, h.1]; decide, Cvl.At.take _ _ _ h.2⟩
theorem in5 (h : Cvs16.At m a (l4 k flags l)) : Pairs.At 1#64 m a ((l4 k flags l).take 2) :=
  ⟨by decide, by rw [List.length_take, h.1]; decide, Cvl.At.take _ _ _ h.2⟩

/-- At entry: there are 32 values. -/
theorem len (h : Cvs32.At m cvs l) : l.length = 32 := h.1

/-- The five levels are the tree's value, in all sixteen lanes of the last call. -/
theorem l5_eq (hl : l.length = 32) : l5 k flags l = List.replicate 16 (Tree32.value k flags l) := by
  have e1 : l1 k flags l = Tree.level k ⟨flags.setWidth 32⟩ l := by
    have h := P16.values_take k flags 16#64 l (by rw [hl]; decide)
    have hlen : (P16.values k flags 16#64 l).length ≤ (16#64).toNat := by
      rw [P16.values_length k flags _ l (by rw [hl]; decide) (by decide)]; decide
    rw [List.take_of_length_le hlen] at h
    exact h
  have e2 : (l2 k flags l).take 8 = Tree.level k ⟨flags.setWidth 32⟩ (Tree.level k ⟨flags.setWidth 32⟩ l) :=
    (P16.values_take k flags 8#64 (l1 k flags l) (by rw [len1 hl]; decide)).trans (congrArg _ e1)
  have e3 : (l3 k flags l).take 4 =
      Tree.level k ⟨flags.setWidth 32⟩ (Tree.level k ⟨flags.setWidth 32⟩ (Tree.level k ⟨flags.setWidth 32⟩ l)) :=
    (P16.values_take k flags 4#64 ((l2 k flags l).take 8) (by rw [List.length_take, len2 hl]; decide)).trans (congrArg _ e2)
  have e4 : (l4 k flags l).take 2 =
      Tree.level k ⟨flags.setWidth 32⟩ (Tree.level k ⟨flags.setWidth 32⟩ (Tree.level k ⟨flags.setWidth 32⟩ (Tree.level k ⟨flags.setWidth 32⟩ l))) :=
    (P16.values_take k flags 2#64 ((l3 k flags l).take 4) (by rw [List.length_take, len3 hl]; decide)).trans (congrArg _ e3)
  have n5 : (Tree.level k ⟨flags.setWidth 32⟩ ((l4 k flags l).take 2)).length = 1 :=
    Tree.level_length k _ 1 _ (by rw [List.length_take, len4 hl]; decide)
  have one : ∀ L : List Blake3.CV, L.length = 1 → L = [L.headD (Vector.replicate 8 0)] := by
    intro L hL
    match L, hL with
    | [x], _ => rfl
  have hx : Tree.level k ⟨flags.setWidth 32⟩ ((l4 k flags l).take 2) = [Tree32.value k flags l] := by
    have h := one _ n5
    rw [e4] at h ⊢
    exact h
  exact P16.values_one k flags _ _ hx

end Tree32

/-- **At the return:** all sixteen lanes hold the tree's value. -/
theorem Tree32.exit {m : Mem} {res : BitVec 64} {k : Blake3.CV} {flags : BitVec 64} {l : List Blake3.CV}
    (h : Cvs16.At m res (Tree32.l5 k flags l)) (hl : l.length = 32) :
    True ∧ Cvs16.At m res (List.replicate 16 (Tree32.value k flags l)) := by
  rw [← Tree32.l5_eq hl]; exact ⟨trivial, h⟩
