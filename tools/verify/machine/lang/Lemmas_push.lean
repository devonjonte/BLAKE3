import StackLemmas
import Spec_push
open X86 Cells

/-! # `push`: lemmas for the prover

Written by hand for this function; its source names them. Checked by Lean; not to be read. -/

/-- A stack with room for one more: the count's cell, the bytes owned, the bound. -/
theorem Stack.At.room {m : Mem} {st : BitVec 64} {cvs : List Blake3.CV} (h : Stack.At m st cvs) (hn : cvs.length < 55) :
    Quad m st (Stack.count cvs) ∧ Region m st 1792#64 ∧ Stack.count cvs < 55#64 := by
  have := Stack.count_toNat h.1
  exact ⟨h.2.2.1, h.2.1, by bv_omega⟩

/-- **At the return:** the new value's two vectors above the old ones, the count one more, the rest of the
stack's bytes as they were: the stack with the value on it. -/
theorem Push.exit {m m' : Mem} {st : BitVec 64} {new : Blake3.CV} {cvs : List Blake3.CV} {n0 n1 : V}
    (h : Stack.At m st cvs) (hn : cvs.length < 55) (hw : words8 n0 n1 = new)
    (hp0 : Vec m' (st + 32#64 + (Stack.count cvs) <<< 5) n0) (hp1 : Vec m' (st + 32#64 + (Stack.count cvs) <<< 5 + 16#64) n1)
    (hq : Quad m' st (Stack.count cvs + 1#64)) (hR : Region m' st 1792#64)
    (same : ∀ x : BitVec 64, x - st < 1792#64 → 8#64 ≤ x - st → 32#64 ≤ x - (st + 32#64 + (Stack.count cvs) <<< 5) → m' x = m x) :
    True ∧ Stack.At m' st (new :: cvs) := by
  obtain ⟨hlen, _, _, hc⟩ := h
  have hc' := Stack.count_toNat hlen
  have c1 : BitVec.ofNat 64 (new :: cvs).length = Stack.count cvs + 1#64 := by
    apply BitVec.eq_of_toNat_eq; simp only [List.length_cons, BitVec.toNat_ofNat, BitVec.toNat_add]; omega
  refine ⟨trivial, by simp only [List.length_cons]; omega, hR, by rw [c1]; exact hq, ?_⟩
  rw [c1]
  show Cv.At m' (st + 32#64 * (Stack.count cvs + 1#64)) new ∧ Cvs.At m' (st + 32#64 * (Stack.count cvs + 1#64) - 32#64) cvs
  have hc0 : Cvs.At m (st + 32#64 * Stack.count cvs) cvs := hc
  generalize Stack.count cvs = c at *
  refine ⟨⟨n0, n1, ?_, ?_, hw⟩, ?_⟩
  · rw [show st + 32#64 * (c + 1#64) = st + 32#64 + c <<< 5 by bv_decide]; exact hp0
  · rw [show st + 32#64 * (c + 1#64) + 16#64 = st + 32#64 + c <<< 5 + 16#64 by bv_decide]; exact hp1
  rw [show st + 32#64 * (c + 1#64) - 32#64 = st + 32#64 * c by bv_decide]
  refine Cvs.At.frame cvs _ (fun x hx => ?_) hc0
  have hb : c < 55#64 := by bv_omega
  have hx' : st + 32#64 * c + 31#64 - x < 32#64 * c := by
    generalize st + 32#64 * c + 31#64 - x = y at hx ⊢
    bv_omega
  exact same x (by bv_decide) (by bv_decide) (by bv_decide)
