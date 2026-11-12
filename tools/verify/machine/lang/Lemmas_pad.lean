import Cells
import Spec_pad
open X86 Cells

/-! # `pad`: lemmas for the prover

Written by hand for this function; its source names them. `Pad.Mid` is what holds at the head of the loop:
the block's bytes from `i` on are what they are to be. Checked by Lean; not to be read. -/

/-- At the loop's head: byte `j` of the block, for every `j` from `i` on, is the message's byte `j`, or zero
past the message's end. -/
def Pad.Mid (m : Mem) (block src : BitVec 64) (bytes : List (BitVec 8)) (n i : BitVec 64) : Prop :=
  n.toNat = bytes.length ∧ bytes.length ≤ 64 ∧ i ≤ 64#64 ∧ Bytes.At m src bytes ∧ Region m block 64#64 ∧
  ∀ j : Nat, i.toNat ≤ j → j < 64 → m (block + BitVec.ofNat 64 j) = some (bytes.getD j 0#8)

namespace Pad.Mid

variable {m m' : Mem} {block src n i : BitVec 64} {bytes : List (BitVec 8)}

/-- What its holder may use at once: the block's bytes are the program's; the index is at most 64. -/
theorem cells (h : Pad.Mid m block src bytes n i) : Region m block 64#64 ∧ i ≤ 64#64 := ⟨h.2.2.2.2.1, h.2.2.1⟩

theorem src_same (hb : Bytes.At m src bytes) (sameSrc : ∀ x : BitVec 64, x - src < BitVec.ofNat 64 bytes.length → m' x = m x)
    (hl : bytes.length ≤ 64) : Bytes.At m' src bytes := by
  intro k hk
  rw [sameSrc _ (by
    have e : src + BitVec.ofNat 64 k - src = BitVec.ofNat 64 k := by bv_omega
    rw [e]; simp only [BitVec.lt_def, BitVec.toNat_ofNat]; omega)]
  exact hb k hk

/-- **Before the loop:** nothing of the block is claimed yet. -/
theorem start (hb : Bytes.At m src bytes) (hn : n.toNat = bytes.length) (hl : bytes.length ≤ 64)
    (hR : Region m' block 64#64)
    (sameSrc : ∀ x : BitVec 64, x - src < BitVec.ofNat 64 bytes.length → m' x = m x) :
    Pad.Mid m' block src bytes n 64#64 :=
  ⟨hn, hl, by decide, src_same hb sameSrc hl, hR, fun j h1 h2 => absurd h2 (by simp at h1; omega)⟩

/-- A byte of the message the turn reads: the one before the index. -/
theorem next (h : Pad.Mid m block src bytes n i) (hpos : 0#64 < i) (hc : i - 1#64 < n) :
    ∃ b : BitVec 8, Byte m (src + (i - 1#64)) b ∧ bytes.getD (i - 1#64).toNat 0#8 = b := by
  obtain ⟨hn, hl, hi, hb, _, _⟩ := h
  have hk : (i - 1#64).toNat < bytes.length := by rw [← hn]; exact hc
  refine ⟨bytes[(i - 1#64).toNat], ?_, by generalize (i - 1#64).toNat = k at hk ⊢; simp [List.getD, List.getElem?_eq_getElem hk]⟩
  have := hb _ hk
  rwa [BitVec.ofNat_toNat, BitVec.setWidth_eq] at this

/-- One byte put before the index: the block's bytes from one lower on are what they are to be. -/
theorem put {v : BitVec 8} (h : Pad.Mid m block src bytes n i) (hpos : 0#64 < i) (hv : bytes.getD (i - 1#64).toNat 0#8 = v)
    (hp : Byte m' (block + (i - 1#64)) v)
    (same : ∀ x : BitVec 64, x - block < 64#64 → 1#64 ≤ x - (block + (i - 1#64)) → m' x = m x)
    (sameSrc : ∀ x : BitVec 64, x - src < BitVec.ofNat 64 bytes.length → m' x = m x) :
    Pad.Mid m' block src bytes n (i - 1#64) := by
  obtain ⟨hn, hl, hi, hb, hR, hall⟩ := h
  have hi1 : (i - 1#64).toNat = i.toNat - 1 := by bv_omega
  have hin : 0 < i.toNat ∧ i.toNat ≤ 64 := by constructor <;> bv_omega
  refine ⟨hn, hl, by bv_omega, src_same hb sameSrc hl, ?_, fun j h1 h2 => ?_⟩
  · intro d hd
    by_cases e : d = i - 1#64
    · subst e; simp [show m' (block + (i - 1#64)) = some v from hp]
    · rw [same _ (by bv_omega) (by bv_omega)]; exact hR d hd
  · by_cases e : j = i.toNat - 1
    · subst e
      have ea : BitVec.ofNat 64 (i.toNat - 1) = i - 1#64 := by
        apply BitVec.eq_of_toNat_eq; rw [hi1, BitVec.toNat_ofNat]; omega
      rw [ea, show m' (block + (i - 1#64)) = some v from hp, ← hv, hi1]
    · have hj : i.toNat ≤ j := by omega
      have ej : (BitVec.ofNat 64 j).toNat = j := by rw [BitVec.toNat_ofNat]; omega
      rw [same _ (by bv_omega) (by bv_omega)]
      exact hall j hj h2

/-- **A turn that copies a byte of the message.** -/
theorem copy {b : BitVec 8} (h : Pad.Mid m block src bytes n i) (hpos : 0#64 < i) (hc : i - 1#64 < n)
    (hb : bytes.getD (i - 1#64).toNat 0#8 = b) (hp : Byte m' (block + (i - 1#64)) b)
    (same : ∀ x : BitVec 64, x - block < 64#64 → 1#64 ≤ x - (block + (i - 1#64)) → m' x = m x)
    (sameSrc : ∀ x : BitVec 64, x - src < BitVec.ofNat 64 bytes.length → m' x = m x) :
    Pad.Mid m' block src bytes n (i - 1#64) := put h hpos hb hp same sameSrc

/-- **A turn past the message's end: a zero.** -/
theorem zero (h : Pad.Mid m block src bytes n i) (hpos : 0#64 < i) (hc : ¬ i - 1#64 < n)
    (hp : Byte m' (block + (i - 1#64)) 0#8)
    (same : ∀ x : BitVec 64, x - block < 64#64 → 1#64 ≤ x - (block + (i - 1#64)) → m' x = m x)
    (sameSrc : ∀ x : BitVec 64, x - src < BitVec.ofNat 64 bytes.length → m' x = m x) :
    Pad.Mid m' block src bytes n (i - 1#64) := by
  refine put h hpos ?_ hp same sameSrc
  have hk : bytes.length ≤ (i - 1#64).toNat := by rw [← h.1]; exact BitVec.not_lt.mp hc
  generalize (i - 1#64).toNat = k at hk ⊢
  simp [List.getD, List.getElem?_eq_none hk]

end Pad.Mid

/-- **When the loop ends:** every byte of the block is what it is to be. -/
theorem Pad.exit {m : Mem} {block src n i : BitVec 64} {bytes : List (BitVec 8)}
    (h : Pad.Mid m block src bytes n i) (hc : ¬ 0#64 < i) :
    True ∧ (bytes ++ List.replicate (64 - bytes.length) 0#8).length = 64 ∧
      Bytes.At m block (bytes ++ List.replicate (64 - bytes.length) 0#8) := by
  obtain ⟨hn, hl, hi, hb, hR, hall⟩ := h
  have i0 : i.toNat = 0 := by bv_omega
  have hlen : (bytes ++ List.replicate (64 - bytes.length) 0#8).length = 64 := by simp; omega
  refine ⟨trivial, hlen, fun j hj => ?_⟩
  rw [hall j (by omega) (by omega)]
  congr 1
  by_cases hjl : j < bytes.length
  · simp [List.getD, List.getElem?_eq_getElem hjl, List.getElem_append_left hjl]
  · simp [List.getD, List.getElem?_eq_none (Nat.le_of_not_lt hjl), List.getElem_append_right (Nat.le_of_not_lt hjl)]
