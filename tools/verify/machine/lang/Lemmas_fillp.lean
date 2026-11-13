import Cells
import Spec_fillp
open X86 Cells

/-! # `fillp`: lemmas for the prover

Written by hand for this function; its source names them. `Ptrs.Mid` is what holds at the head of the loop:
the table's first `i` addresses are what they are to be, and `cur` is the next real one. Checked by Lean; not
to be read. -/

/-- At the loop's head. -/
def Ptrs.Mid (m : Mem) (ptrs base n stride i cur : BitVec 64) : Prop :=
  i ≤ 32#64 ∧ cur = base + stride * i ∧ Region m ptrs 256#64 ∧
  ∀ j : Nat, j < i.toNat → Quad m (ptrs + BitVec.ofNat 64 (8 * j)) (Ptrs.spread base n stride j)

namespace Ptrs.Mid

variable {m m' : Mem} {ptrs base n stride i cur : BitVec 64}

/-- What its holder may use at once: the table's bytes are the program's; the index is at most 32. -/
theorem cells (h : Ptrs.Mid m ptrs base n stride i cur) : Region m ptrs 256#64 ∧ i ≤ 32#64 := ⟨h.2.2.1, h.1⟩

/-- **Before the loop:** nothing of the table is claimed yet. -/
theorem start (hR : Region m ptrs 256#64) : Ptrs.Mid m ptrs base n stride 0#64 base :=
  ⟨by decide, by simp, hR, fun j hj => absurd hj (by simp)⟩

/-- One address put at the index: the table's first `i + 1` are what they are to be. -/
theorem put {v : BitVec 64} (h : Ptrs.Mid m ptrs base n stride i cur) (hc : i < 32#64)
    (hv : Ptrs.spread base n stride i.toNat = v)
    (hp : Quad m' (ptrs + i <<< 3) v) (hR : Region m' ptrs 256#64)
    (same : ∀ x : BitVec 64, x - ptrs < 256#64 → 8#64 ≤ x - (ptrs + i <<< 3) → m' x = m x) :
    Ptrs.Mid m' ptrs base n stride (i + 1#64) (cur + stride) := by
  obtain ⟨hi, hcur, _, hall⟩ := h
  have hi32 : i.toNat < 32 := hc
  have hi1 : (i + 1#64).toNat = i.toNat + 1 := by bv_omega
  refine ⟨by bv_omega, ?_, hR, fun j hj => ?_⟩
  · rw [hcur, BitVec.mul_add, BitVec.mul_one, BitVec.add_assoc]
  · by_cases e : j = i.toNat
    · subst e
      have ea : BitVec.ofNat 64 (8 * i.toNat) = i <<< 3 := by
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_ofNat, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
        omega
      rw [ea, hv]; exact hp
    · have hj' : j < i.toNat := by omega
      have ej : (BitVec.ofNat 64 (8 * j)).toNat = 8 * j := by rw [BitVec.toNat_ofNat]; omega
      have es : (i <<< 3).toNat = 8 * i.toNat := by rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega
      refine quad_congr (fun x hx => same x ?_ ?_) (hall j hj')
      · generalize BitVec.ofNat 64 (8 * j) = c at ej hx; bv_omega
      · generalize BitVec.ofNat 64 (8 * j) = c at ej hx
        generalize i <<< 3 = d at es
        bv_omega

/-- **A turn in the first `n` lanes: the next address.** -/
theorem real (h : Ptrs.Mid m ptrs base n stride i cur) (hc : i < 32#64) (hb : i < n)
    (hp : Quad m' (ptrs + i <<< 3) cur) (hR : Region m' ptrs 256#64)
    (same : ∀ x : BitVec 64, x - ptrs < 256#64 → 8#64 ≤ x - (ptrs + i <<< 3) → m' x = m x) :
    Ptrs.Mid m' ptrs base n stride (i + 1#64) (cur + stride) := by
  refine put h hc ?_ hp hR same
  have hlt : i.toNat < n.toNat := hb
  simp only [Ptrs.spread, hlt, if_true, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  exact h.2.1.symm

/-- **A turn past them: the first address again.** -/
theorem dup (h : Ptrs.Mid m ptrs base n stride i cur) (hc : i < 32#64) (hb : ¬ i < n)
    (hp : Quad m' (ptrs + i <<< 3) base) (hR : Region m' ptrs 256#64)
    (same : ∀ x : BitVec 64, x - ptrs < 256#64 → 8#64 ≤ x - (ptrs + i <<< 3) → m' x = m x) :
    Ptrs.Mid m' ptrs base n stride (i + 1#64) (cur + stride) := by
  refine put h hc ?_ hp hR same
  have hge : ¬ i.toNat < n.toNat := hb
  simp only [Ptrs.spread, hge, if_false]

end Ptrs.Mid

/-- A table is in its own 256 bytes. -/
theorem Ptrs.At.frame {m m' : Mem} {a : BitVec 64} {f : Nat → BitVec 64} (h : Ptrs.At m a f)
    (same : ∀ x : BitVec 64, x - a < 256#64 → m' x = m x) : Ptrs.At m' a f := by
  intro j hj
  have ej : (BitVec.ofNat 64 (8 * j)).toNat = 8 * j := by rw [BitVec.toNat_ofNat]; omega
  refine quad_congr (fun x hx => same x ?_) (h j hj)
  generalize BitVec.ofNat 64 (8 * j) = c at ej hx
  bv_omega

/-- **When the loop ends:** the table holds its 32 addresses. -/
theorem Fillp.exit {m : Mem} {ptrs base n stride i cur : BitVec 64}
    (h : Ptrs.Mid m ptrs base n stride i cur) (hc : ¬ i < 32#64) :
    True ∧ Ptrs.At m ptrs (Ptrs.spread base n stride) := by
  obtain ⟨hi, _, _, hall⟩ := h
  have i32 : i.toNat = 32 := by bv_omega
  exact ⟨trivial, fun j hj => hall j (by omega)⟩
