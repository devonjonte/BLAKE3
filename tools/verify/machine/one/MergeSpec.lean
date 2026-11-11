import MergeWhole
import ParentSpec
import Stack
open X86 MergeCode

/-! # The compiled `merge` runs the algorithm that is proved to be BLAKE3

`merge_is_mergeN` says the machine code runs `mergeN`, whose merges are the kernels' results on vectors
of memory. `Stack.lean` (no code named) proves that a hasher whose stack is merged by `Blake3.mergeTo`
computes the specification's tree. This file joins them: as chaining values of the specification,
`mergeN` is `Blake3.mergeTo`. -/

/-- A stack value's two vectors of memory, as the specification's chaining value. -/
def cvOf (e : V × V) : Blake3.CV := words8 e.1 e.2

theorem dw_mk4_0 (a b c d : BitVec 32) : dw (mk4 a b c d) 0 = a := by simp only [dw, mk4]; bv_decide
theorem dw_mk4_1 (a b c d : BitVec 32) : dw (mk4 a b c d) 1 = b := by simp only [dw, mk4]; bv_decide
theorem dw_mk4_2 (a b c d : BitVec 32) : dw (mk4 a b c d) 2 = c := by simp only [dw, mk4]; bv_decide
theorem dw_mk4_3 (a b c d : BitVec 32) : dw (mk4 a b c d) 3 = d := by simp only [dw, mk4]; bv_decide

/-- **What the kernels leave is the specification's parent chaining value.** `mode` is the mode's flags;
`merge` stored them with PARENT. -/
theorem merged_is_parent (k0 k1 l0 l1 r0 r1 : V) (mode : BitVec 32) (fl : BitVec 8) (hfl : fl.setWidth 32 = mode ||| 4) :
    cvOf (merged k0 k1 l0 l1 r0 r1 fl) = (Blake3.parentNode (words8 k0 k1) ⟨mode⟩ (words8 l0 l1) (words8 r0 r1)).cv := by
  have h := parentCv_is_the_specifications k0 k1 l0 l1 r0 r1 mode
  simp only [parentCv] at h
  simp only [cvOf, merged, hfl, h, words8, dw_mk4_0, dw_mk4_1, dw_mk4_2, dw_mk4_3]
  ext i hi
  match i, hi with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ => simp [bv]

/-- **`mergeN` is `Blake3.mergeTo`.** `n` merges of a stack of at least `n + 1` values, read as the
specification's chaining values, are what `mergeTo` does with the target `length - n`. -/
theorem mergeN_is_mergeTo (k0 k1 : V) (mode : BitVec 32) (fl : BitVec 8) (hfl : fl.setWidth 32 = mode ||| 4) :
    ∀ (n : Nat) (es : List (V × V)), n + 1 ≤ es.length →
      Blake3.mergeTo (words8 k0 k1) ⟨mode⟩ (es.length - n) (es.map cvOf) = (mergeN k0 k1 fl n es).map cvOf := by
  intro n
  induction n with
  | zero =>
    intro es _
    rcases es with _ | ⟨a, _ | ⟨b, rest⟩⟩
    · rw [Blake3.mergeTo]; rfl; all_goals simp
    · rw [Blake3.mergeTo]; rfl; all_goals simp
    · simp only [List.map_cons, mergeN, Nat.sub_zero, List.length_cons]
      rw [Blake3.mergeTo, if_neg (by simp)]
  | succ n ih =>
    intro es hlen
    rcases es with _ | ⟨r, _ | ⟨l, rest⟩⟩
    · simp at hlen
    · simp at hlen
    · simp only [List.length_cons] at hlen
      have h := ih (merged k0 k1 l.1 l.2 r.1 r.2 fl :: rest) (by simp only [List.length_cons]; omega)
      simp only [List.map_cons, List.length_cons] at h ⊢
      rw [Blake3.mergeTo, if_pos (by simp only [List.length_map]; omega)]
      rw [show mergeN k0 k1 fl (n + 1) (r :: l :: rest) = mergeN k0 k1 fl n (merged k0 k1 l.1 l.2 r.1 r.2 fl :: rest) from rfl]
      rw [← h, merged_is_parent k0 k1 l.1 l.2 r.1 r.2 mode fl hfl, show rest.length + 1 - n = rest.length + 1 + 1 - (n + 1) by omega]
      rfl

#print axioms mergeN_is_mergeTo

/-- **What the compiled `merge` leaves is `Blake3.mergeTo`'s stack.** The stack `merge_is_mergeN` puts in
memory, read as the specification's chaining values, is `Blake3.mergeTo` of the stack before, with the
key and the mode's flags, to `target` values: the function `Stack.lean` proves a hasher may use. -/
theorem merge_runs_mergeTo (k0 k1 : V) (flags : BitVec 8) (len target : BitVec 64) (es : List (V × V))
    (hlt : target < len) (h1 : 1#64 ≤ target) (hlen : len.toNat = es.length) :
    (mergeN k0 k1 (flags ||| 4#8) (len - target).toNat es).map cvOf =
      Blake3.mergeTo (words8 k0 k1) ⟨flags.setWidth 32⟩ target.toNat (es.map cvOf) := by
  have h := mergeN_is_mergeTo k0 k1 (flags.setWidth 32) (flags ||| 4#8) (by bv_decide) (len - target).toNat es (by bv_omega)
  rw [← h, show es.length - (len - target).toNat = target.toNat by bv_omega]

#print axioms merge_runs_mergeTo
