import StackSpec
import MergeTree
import Spec_stack
open X86 Cells MergeCode

/-! # From the statements' view of the stack to the proof's, and back

The statements (`Spec_stack.lean`) speak of the specification's chaining values; the compiler's proof
works with the pairs of vectors the kernels read and write (`StackSpec.lean`). These lemmas, written
by hand once for the data structure, carry one to the other. Checked by Lean; not to be read. -/

/-- The proof's values `es` are the statement's `cvs`. -/
def Stack.Views (es : Stack.Cvs) (cvs : List Blake3.CV) : Prop := es.map cvOf = cvs

/-- The two vectors `k0`, `k1` are the chaining value `k`. -/
def Cv.Is (k0 k1 : V) (k : Blake3.CV) : Prop := words8 k0 k1 = k

theorem Cv.vectors {m : Mem} {a : BitVec 64} {cv : Blake3.CV} (h : Cv.At m a cv) :
    ∃ v0 v1 : V, Vec m a v0 ∧ Vec m (a + 16#64) v1 ∧ Cv.Is v0 v1 cv := h

theorem Cvs.at_of_entries {m : Mem} : ∀ (es : List (V × V)) (a : BitVec 64), Entries m a es → Cvs.At m a (es.map cvOf)
  | [], _, _ => trivial
  | e :: es, a, ⟨h0, h1, hr⟩ => ⟨⟨e.1, e.2, by rw [BitVec.add_zero] at h0; exact h0, h1, rfl⟩, Cvs.at_of_entries es _ hr⟩

theorem Cvs.entries_of_at {m : Mem} : ∀ (cvs : List Blake3.CV) (a : BitVec 64), Cvs.At m a cvs → ∃ es, Entries m a es ∧ es.map cvOf = cvs
  | [], _, _ => ⟨[], trivial, rfl⟩
  | cv :: rest, a, ⟨⟨v0, v1, h0, h1, hw⟩, hr⟩ => by
    obtain ⟨es, he, hm⟩ := Cvs.entries_of_at rest _ hr
    exact ⟨(v0, v1) :: es, ⟨by rw [BitVec.add_zero]; exact h0, h1, he⟩, by simp only [List.map_cons, cvOf, hw, hm]⟩

theorem Stack.top_address (st x : BitVec 64) : st + 32#64 + (x - 1#64) <<< 5 = st + 32#64 * x := by bv_decide

theorem Stack.at_of_holds {m : Mem} {st len : BitVec 64} {es : Stack.Cvs} (h : Stack.holds m st len es) :
    Stack.At m st (es.map cvOf) ∧ len.toNat = (es.map cvOf).length := by
  obtain ⟨hl, hb, hq, he, hr⟩ := h
  have e : BitVec.ofNat 64 (es.map cvOf).length = len := by
    rw [List.length_map, ← hl]; exact BitVec.ofNat_toNat ..
  refine ⟨⟨by rw [List.length_map]; bv_omega, hr, by rw [e]; exact hq, ?_⟩, by rw [List.length_map]; exact hl⟩
  rw [e, ← Stack.top_address]; exact Cvs.at_of_entries es _ he

/-- The statement's stack, as the proof sees it: a count and the vectors. -/
theorem Stack.holds_of_at {m : Mem} {st : BitVec 64} {cvs : List Blake3.CV} (h : Stack.At m st cvs) :
    ∃ len es, Stack.holds m st len es ∧ Stack.Views es cvs := by
  obtain ⟨hn, hr, hq, hc⟩ := h
  rw [← Stack.top_address] at hc
  obtain ⟨es, he, hm⟩ := Cvs.entries_of_at cvs _ hc
  have hlen : es.length = cvs.length := by rw [← hm, List.length_map]
  refine ⟨BitVec.ofNat 64 cvs.length, es, ⟨?_, ?_, hq, he, hr⟩, hm⟩
  · rw [hlen, BitVec.toNat_ofNat]; omega
  · rw [BitVec.le_def, BitVec.toNat_ofNat]; simp only [BitVec.toNat_ofNat]; omega

/-- **When `merge`'s loop ends:** the proof's invariant gives the statement's `ensures`. -/
theorem Merge.exit {m : Mem} {st len target flags : BitVec 64} {k0 k1 : V} {k : Blake3.CV} {es es0 : Stack.Cvs} {cvs : List Blake3.CV}
    (h : Stack.holds m st len es)
    (he : Stack.merged k0 k1 (BitVec.setWidth 8 (flags ||| 4#64)) target es = Stack.merged k0 k1 (BitVec.setWidth 8 (flags ||| 4#64)) target es0)
    (hm : Stack.Views es0 cvs) (hk : Cv.Is k0 k1 k) (ht : ¬ target < len) (h1 : 1#64 ≤ target) (hfl : flags < 256#64) :
    Stack.At m st (Blake3.mergeTo k ⟨flags.setWidth 32⟩ target.toNat cvs) ∧
      len.toNat = (Blake3.mergeTo k ⟨flags.setWidth 32⟩ target.toNat cvs).length := by
  have hh := Stack.merged_exit h he ht
  have hm2 := Stack.merged_is_mergeTo k0 k1 flags target es0 hfl h1
  rw [show words8 k0 k1 = k from hk, show es0.map cvOf = cvs from hm] at hm2
  have := Stack.at_of_holds hh
  rw [hm2] at this; exact this
