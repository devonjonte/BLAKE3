import Cells
import Spec_stack
open X86 Cells

/-! # The stack in memory: lemmas for the prover

Written by hand, once for the data structure; a function's source names them. They take the stack of
`Spec_stack.lean` apart into the cells code reads and writes, and put it together again. Checked by
Lean; not to be read. By convention a lemma's memory is `m` (and the memory after, `m'`), and for a
predicate `P` over memory `P.cells` gives what its holder may read at once and `P.frame` says it
depends on its own bytes only. -/

/-- The count of a stack, as the machine holds it. -/
def Stack.count (cvs : List Blake3.CV) : BitVec 64 := BitVec.ofNat 64 cvs.length

/-- A chaining value in memory is two vectors. -/
theorem Cv.At.vectors {m : Mem} {a : BitVec 64} {cv : Blake3.CV} (h : Cv.At m a cv) :
    ∃ v0 v1 : V, Vec m a v0 ∧ Vec m (a + 16#64) v1 ∧ words8 v0 v1 = cv := h

theorem Cv.At.frame {m m' : Mem} {a : BitVec 64} {cv : Blake3.CV} (h : Cv.At m a cv)
    (same : ∀ x : BitVec 64, x - a < 32#64 → m' x = m x) : Cv.At m' a cv := by
  obtain ⟨v0, v1, h0, h1, hw⟩ := h
  exact ⟨v0, v1, vec_congr (fun x hx => same x (by bv_omega)) h0, vec_congr (fun x hx => same x (by bv_omega)) h1, hw⟩

theorem Cvs.At.frame {m m' : Mem} : ∀ (cvs : List Blake3.CV) (a : BitVec 64),
    (∀ x : BitVec 64, (a + 31#64 - x).toNat < 32 * cvs.length → m' x = m x) → Cvs.At m a cvs → Cvs.At m' a cvs := by
  intro cvs
  induction cvs with
  | nil => intros; trivial
  | cons cv rest ih =>
    intro a h ⟨hc, hr⟩
    simp only [List.length_cons] at h
    exact ⟨Cv.At.frame hc (fun x hx => h x (by bv_omega)), ih (a - 32#64) (fun x hx => h x (by bv_omega)) hr⟩

theorem Stack.count_toNat {cvs : List Blake3.CV} (hn : cvs.length ≤ 55) : (Stack.count cvs).toNat = cvs.length := by
  simp only [Stack.count, BitVec.toNat_ofNat]; omega

/-- What a holder of the stack may read at once: the count's cell, the bytes owned, the bound. -/
theorem Stack.At.cells {m : Mem} {st : BitVec 64} {cvs : List Blake3.CV} (h : Stack.At m st cvs) :
    Quad m st (Stack.count cvs) ∧ Region m st 1792#64 ∧ Stack.count cvs ≤ 55#64 := by
  have := Stack.count_toNat h.1
  exact ⟨h.2.2.1, h.2.1, by have := h.1; bv_omega⟩

/-- The stack is in its own 1792 bytes: a memory that agrees on them holds it too. -/
theorem Stack.At.frame {m m' : Mem} {st : BitVec 64} {cvs : List Blake3.CV} (h : Stack.At m st cvs)
    (same : ∀ x : BitVec 64, x - st < 1792#64 → m' x = m x) : Stack.At m' st cvs := by
  obtain ⟨hn, hr, hq, hc⟩ := h
  have hc' := Stack.count_toNat hn
  refine ⟨hn, ?_, quad_congr (fun x hx => same x (by bv_omega)) hq, Cvs.At.frame cvs _ (fun x hx => same x ?_) hc⟩
  · intro d hd
    rw [same _ (by bv_omega)]; exact hr d hd
  · show x - st < 1792#64
    change (st + 32#64 * Stack.count cvs + 31#64 - x).toNat < 32 * cvs.length at hx
    generalize Stack.count cvs = c at hx hc'
    bv_omega

/-- With two values or more: the two newest, as the four vectors the code reads. -/
theorem Stack.At.top2 {m : Mem} {st len : BitVec 64} {cvs : List Blake3.CV} (h : Stack.At m st cvs)
    (hl : len = Stack.count cvs) (h2 : 2#64 ≤ len) :
    ∃ (r l : Blake3.CV) (rest : List Blake3.CV) (r0 r1 l0 l1 : V), cvs = r :: l :: rest ∧
      Vec m (st + 32#64 + (len - 2#64) <<< 5) l0 ∧ Vec m (st + 32#64 + (len - 2#64) <<< 5 + 16#64) l1 ∧
      Vec m (st + 32#64 + (len - 2#64) <<< 5 + 32#64) r0 ∧ Vec m (st + 32#64 + (len - 2#64) <<< 5 + 48#64) r1 ∧
      words8 l0 l1 = l ∧ words8 r0 r1 = r := by
  obtain ⟨hn, hr, hq, hc⟩ := h
  rcases cvs with _ | ⟨r, _ | ⟨l, rest⟩⟩
  · subst hl; exact absurd h2 (by decide)
  · subst hl; exact absurd h2 (by simp [Stack.count])
  have hl' : BitVec.ofNat 64 (r :: l :: rest).length = len := hl.symm
  rw [hl'] at hc
  obtain ⟨⟨r0, r1, hr0, hr1, hwr⟩, ⟨l0, l1, hl0, hl1, hwl⟩, _⟩ := hc
  rw [show st + 32#64 * len = st + 32#64 + (len - 2#64) <<< 5 + 32#64 by bv_decide] at hr0
  rw [show st + 32#64 * len + 16#64 = st + 32#64 + (len - 2#64) <<< 5 + 48#64 by bv_decide] at hr1
  rw [show st + 32#64 * len - 32#64 = st + 32#64 + (len - 2#64) <<< 5 by bv_decide] at hl0
  rw [show st + 32#64 * len - 32#64 + 16#64 = st + 32#64 + (len - 2#64) <<< 5 + 16#64 by bv_decide] at hl1
  exact ⟨r, l, rest, r0, r1, l0, l1, rfl, hl0, hl1, hr0, hr1, hwl, hwr⟩

/-- After the two newest have been replaced by one value `p` (its vectors where the older of the two was,
the count one less, the rest of the stack's bytes as they were): the stack again, one shorter. -/
theorem Stack.At.merge_top {m m' : Mem} {st len : BitVec 64} {r l : Blake3.CV} {rest : List Blake3.CV}
    (h : Stack.At m st (r :: l :: rest)) (hl : len = Stack.count (r :: l :: rest)) {p0 p1 : V}
    (hp0 : Vec m' (st + 32#64 + (len - 2#64) <<< 5) p0) (hp1 : Vec m' (st + 32#64 + (len - 2#64) <<< 5 + 16#64) p1)
    (hq : Quad m' st (len - 1#64)) (hR : Region m' st 1792#64)
    (same : ∀ x : BitVec 64, x - st < 1792#64 → 8#64 ≤ x - st → 32#64 ≤ x - (st + 32#64 + (len - 2#64) <<< 5) → m' x = m x) :
    Stack.At m' st (words8 p0 p1 :: rest) := by
  obtain ⟨hn, _, _, hc⟩ := h
  have hlen : len.toNat = rest.length + 2 := by rw [hl, Stack.count_toNat hn]; rfl
  simp only [List.length_cons] at hn
  have hb : len ≤ 55#64 := by bv_omega
  have h2 : 2#64 ≤ len := by bv_omega
  have hl' : BitVec.ofNat 64 (r :: l :: rest).length = len := hl.symm
  rw [hl'] at hc
  obtain ⟨_, _, hrest⟩ := hc
  have c1 : BitVec.ofNat 64 (words8 p0 p1 :: rest).length = len - 1#64 := by
    apply BitVec.eq_of_toNat_eq; simp only [List.length_cons, BitVec.toNat_ofNat]; bv_omega
  refine ⟨by simp only [List.length_cons]; omega, hR, by rw [c1]; exact hq, ?_⟩
  rw [c1]
  show Cv.At m' (st + 32#64 * (len - 1#64)) (words8 p0 p1) ∧ Cvs.At m' (st + 32#64 * (len - 1#64) - 32#64) rest
  refine ⟨⟨p0, p1, ?_, ?_, rfl⟩, ?_⟩
  · rw [show st + 32#64 * (len - 1#64) = st + 32#64 + (len - 2#64) <<< 5 by bv_decide]; exact hp0
  · rw [show st + 32#64 * (len - 1#64) + 16#64 = st + 32#64 + (len - 2#64) <<< 5 + 16#64 by bv_decide]; exact hp1
  rw [show st + 32#64 * (len - 1#64) - 32#64 = st + 32#64 * len - 32#64 - 32#64 by bv_decide]
  refine Cvs.At.frame rest _ (fun x hx => ?_) hrest
  have hx' : st + 32#64 * len - 32#64 - 32#64 + 31#64 - x < 32#64 * (len - 2#64) := by
    generalize st + 32#64 * len - 32#64 - 32#64 + 31#64 - x = y at hx ⊢
    bv_omega
  exact same x (by bv_decide) (by bv_decide) (by bv_decide)

/-- The count after that. -/
theorem Stack.count_merge_top {len : BitVec 64} {r l p : Blake3.CV} {rest : List Blake3.CV}
    (hl : len = Stack.count (r :: l :: rest)) : len - 1#64 = Stack.count (p :: rest) := by
  subst hl
  apply BitVec.eq_of_toNat_eq
  simp only [Stack.count, List.length_cons, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega
