import Cells
import Kernels
import MergeLoop
open X86 Cells

/-! # The stack of chaining values: what the contracts of `push` and `merge` speak of

Written by hand, once for the data structure: what it means for memory to hold a stack, the function
`merge` computes, and the lemmas that take the structure apart into cells and put it together again
(`open2`, `close_merge`), that say it depends on its own bytes only (`frame`), and that unfold the
function one turn (`merged_step`, `merged_done`). The compiler's proofs use them by name. -/

namespace Stack

/-- Chaining values as pairs of vectors, the top of the stack first. -/
abbrev Cvs := List (V × V)

/-- **Memory holds a stack at `st`:** the length word, then from offset 32 the values, 32 bytes each,
the last pushed at the highest address; room for 55, all owned. -/
def holds (m : Mem) (st len : BitVec 64) (es : Cvs) : Prop :=
  len.toNat = es.length ∧ len ≤ 55#64 ∧ Quad m st len ∧ MergeCode.Entries m (st + 32#64 + (len - 1#64) <<< 5) es ∧ Region m st 1792#64

/-- **What `merge` computes:** while more than `target` values are held, the top two become their
parent (the specification's compression of the key, the two values, and the flags). -/
def merged (k0 k1 : V) (fl : BitVec 8) (target : BitVec 64) (es : Cvs) : Cvs :=
  MergeCode.mergeN k0 k1 fl (es.length - target.toNat) es

/-- What a holder of the stack knows at once: the length's cell, the bytes owned, the bound, and that
the length word counts the values. -/
theorem cells {m : Mem} {st len : BitVec 64} {es : Cvs} (h : holds m st len es) :
    Quad m st len ∧ Region m st 1792#64 ∧ len ≤ 55#64 ∧ len.toNat = es.length := ⟨h.2.2.1, h.2.2.2.2, h.2.1, h.1⟩

/-- The stack is in its own 1792 bytes: a memory that agrees on them holds it too. -/
theorem frame {m m' : Mem} {st len : BitVec 64} {es : Cvs} (h : holds m st len es)
    (same : ∀ x : BitVec 64, x - st < 1792#64 → m' x = m x) : holds m' st len es := by
  obtain ⟨hl, hb, hq, he, hr⟩ := h
  refine ⟨hl, hb, quad_congr (fun x hx => same x (by bv_omega)) hq, ?_, ?_⟩
  · refine MergeCode.entries_congr es _ (fun x hx => same x ?_) he
    rw [MergeCode.shl5] at hx; bv_omega
  · intro d hd
    rw [same _ (by bv_omega)]; exact hr d hd

/-- With two values or more: the two on top, as the four vectors the code reads. -/
theorem open2 {m : Mem} {st len : BitVec 64} {es : Cvs} (h : holds m st len es) (h2 : 2#64 ≤ len) :
    ∃ r0 r1 l0 l1 rest, es = (r0, r1) :: (l0, l1) :: rest ∧
      Vec m (st + 32#64 + (len - 2#64) <<< 5) l0 ∧ Vec m (st + 32#64 + (len - 2#64) <<< 5 + 16#64) l1 ∧
      Vec m (st + 32#64 + (len - 2#64) <<< 5 + 32#64) r0 ∧ Vec m (st + 32#64 + (len - 2#64) <<< 5 + 48#64) r1 := by
  obtain ⟨hl, hb, hq, he, hr⟩ := h
  rcases es with _ | ⟨⟨r0, r1⟩, _ | ⟨⟨l0, l1⟩, rest⟩⟩
  · simp only [List.length_nil] at hl; bv_omega
  · simp only [List.length_cons, List.length_nil] at hl; bv_omega
  obtain ⟨hR0, hR1, hL0, hL1, _⟩ := he
  have e0 : st + 32#64 + (len - 1#64) <<< 5 + 0#64 = st + 32#64 + (len - 2#64) <<< 5 + 32#64 := by bv_decide
  have e1 : st + 32#64 + (len - 1#64) <<< 5 + 16#64 = st + 32#64 + (len - 2#64) <<< 5 + 48#64 := by bv_decide
  have e2 : st + 32#64 + (len - 1#64) <<< 5 - 32#64 + 0#64 = st + 32#64 + (len - 2#64) <<< 5 := by bv_decide
  have e3 : st + 32#64 + (len - 1#64) <<< 5 - 32#64 + 16#64 = st + 32#64 + (len - 2#64) <<< 5 + 16#64 := by bv_decide
  rw [e0] at hR0; rw [e1] at hR1; rw [e2] at hL0; rw [e3] at hL1
  exact ⟨r0, r1, l0, l1, rest, rfl, hL0, hL1, hR0, hR1⟩

/-- After a turn of `merge`: the parent where the lower of the two was, the length one less, the rest
of the stack's bytes as they were: the stack again, one shorter. -/
theorem close_merge {m m' : Mem} {st len : BitVec 64} {r0 r1 l0 l1 : V} {rest : Cvs}
    (h : holds m st len ((r0, r1) :: (l0, l1) :: rest)) (h2 : 2#64 ≤ len) {p0 p1 : V}
    (hp0 : Vec m' (st + 32#64 + (len - 2#64) <<< 5) p0) (hp1 : Vec m' (st + 32#64 + (len - 2#64) <<< 5 + 16#64) p1)
    (hq : Quad m' st (len - 1#64)) (hR : Region m' st 1792#64)
    (same : ∀ x : BitVec 64, x - st < 1792#64 → 8#64 ≤ x - st → 32#64 ≤ x - (st + 32#64 + (len - 2#64) <<< 5) → m' x = m x) :
    holds m' st (len - 1#64) ((p0, p1) :: rest) := by
  obtain ⟨hl, hb, _, he, _⟩ := h
  simp only [List.length_cons] at hl
  obtain ⟨_, _, _, _, hrest⟩ := he
  have n1 : (len - 1#64).toNat = ((p0, p1) :: rest).length := by simp only [List.length_cons]; bv_omega
  have n2 : len - 1#64 ≤ 55#64 := by bv_omega
  have e0 : st + 32#64 + (len - 1#64 - 1#64) <<< 5 + 0#64 = st + 32#64 + (len - 2#64) <<< 5 := by bv_decide
  have e1 : st + 32#64 + (len - 1#64 - 1#64) <<< 5 + 16#64 = st + 32#64 + (len - 2#64) <<< 5 + 16#64 := by bv_decide
  have e2 : st + 32#64 + (len - 1#64 - 1#64) <<< 5 - 32#64 = st + (len - 2#64) <<< 5 := by bv_decide
  have e3 : st + 32#64 + (len - 1#64) <<< 5 - 32#64 - 32#64 = st + (len - 2#64) <<< 5 := by bv_decide
  rw [e3] at hrest
  refine ⟨n1, n2, hq, ?_, hR⟩
  show Vec m' (st + 32#64 + (len - 1#64 - 1#64) <<< 5 + 0#64) p0 ∧ Vec m' (st + 32#64 + (len - 1#64 - 1#64) <<< 5 + 16#64) p1 ∧
    MergeCode.Entries m' (st + 32#64 + (len - 1#64 - 1#64) <<< 5 - 32#64) rest
  rw [e0, e1, e2]
  refine ⟨hp0, hp1, ?_⟩
  refine MergeCode.entries_congr rest _ (fun x hx => ?_) hrest
  have hx' : st + (len - 2#64) <<< 5 + 31#64 - x < (len - 2#64) <<< 5 := by
    clear e0 e1 e2 e3 n1 n2
    generalize st + (len - 2#64) <<< 5 + 31#64 - x = y at hx ⊢
    rw [MergeCode.shl5]; bv_omega
  exact same x (by bv_decide) (by bv_decide) (by bv_decide)

/-- One turn of the function: with more than `target` values, merging is merging after the top two
have become their parent. -/
theorem merged_step (k0 k1 : V) (fl : BitVec 8) (target len : BitVec 64) (r0 r1 l0 l1 : V) (rest : Cvs)
    (hl : len.toNat = ((r0, r1) :: (l0, l1) :: rest).length) (ht : target < len) :
    merged k0 k1 fl target ((r0, r1) :: (l0, l1) :: rest) =
      merged k0 k1 fl target (MergeCode.merged k0 k1 l0 l1 r0 r1 fl :: rest) := by
  simp only [merged, List.length_cons] at hl ⊢
  have e : rest.length + 1 + 1 - target.toNat = (rest.length + 1 - target.toNat) + 1 := by bv_omega
  rw [e]; rfl

/-- With `target` values or fewer, merging changes nothing. -/
theorem merged_done (k0 k1 : V) (fl : BitVec 8) (target len : BitVec 64) (es : Cvs)
    (hl : len.toNat = es.length) (ht : ¬ target < len) : merged k0 k1 fl target es = es := by
  have e : es.length - target.toNat = 0 := by bv_omega
  simp only [merged, e]; rfl

unseal Kernels.out in
/-- The invariant "what is left to merge gives the whole result" after a turn: the two on top have
become what a one-block kernel leaves for the key, the two values, counter 0, length 64 and the flags. -/
theorem merged_turn {k0 k1 : V} {fl : BitVec 8} {target len : BitVec 64} {r0 r1 l0 l1 : V} {rest es0 : Cvs}
    (h : merged k0 k1 fl target ((r0, r1) :: (l0, l1) :: rest) = merged k0 k1 fl target es0)
    (hl : len.toNat = ((r0, r1) :: (l0, l1) :: rest).length) (ht : target < len) :
    merged k0 k1 fl target (((Kernels.out k0 k1 l0 l1 r0 r1 0#64 64#32 (fl.setWidth 32)).1,
      (Kernels.out k0 k1 l0 l1 r0 r1 0#64 64#32 (fl.setWidth 32)).2) :: rest) = merged k0 k1 fl target es0 :=
  (merged_step k0 k1 fl target len r0 r1 l0 l1 rest hl ht).symm.trans h

/-- The same invariant when the loop ends: the stack held is the whole result. -/
theorem merged_exit {m : Mem} {st len target : BitVec 64} {k0 k1 : V} {fl : BitVec 8} {es es0 : Cvs}
    (h : holds m st len es) (he : merged k0 k1 fl target es = merged k0 k1 fl target es0) (ht : ¬ target < len) :
    holds m st len (merged k0 k1 fl target es0) := by
  rw [← he, merged_done k0 k1 fl target len es h.1 ht]; exact h

end Stack
