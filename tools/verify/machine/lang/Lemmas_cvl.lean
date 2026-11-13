import Cells
import StackLemmas
import Spec_cvl
open X86 Cells

/-! # Chaining values one after another: lemmas for the prover

Written by hand, once for the data structure. Checked by Lean; not to be read. -/

theorem Cvl.At.frame {m m' : Mem} : ∀ (l : List Blake3.CV) (a : BitVec 64), 32 * l.length < 2 ^ 64 →
    (∀ x : BitVec 64, (x - a).toNat < 32 * l.length → m' x = m x) → Cvl.At m a l → Cvl.At m' a l := by
  intro l
  induction l with
  | nil => intros; trivial
  | cons cv rest ih =>
    intro a hl h ⟨hc, hr⟩
    simp only [List.length_cons] at h hl
    exact ⟨Cv.At.frame hc (fun x hx => h x (by bv_omega)), ih (a + 32#64) (by omega) (fun x hx => h x (by bv_omega)) hr⟩

theorem Cvl.At.take {m : Mem} : ∀ (l : List Blake3.CV) (a : BitVec 64) (n : Nat), Cvl.At m a l → Cvl.At m a (l.take n) := by
  intro l
  induction l with
  | nil => intros; simp [Cvl.At]
  | cons cv rest ih =>
    intro a n ⟨hc, hr⟩
    cases n with
    | zero => simp [Cvl.At]
    | succ n => exact ⟨hc, ih (a + 32#64) n hr⟩

theorem Cvl.At.head {m : Mem} {a : BitVec 64} {cv : Blake3.CV} {rest : List Blake3.CV} (h : Cvl.At m a (cv :: rest)) :
    Cv.At m a cv := h.1

/-- Sixteen values are in their own 512 bytes. -/
theorem Cvs16.At.frame {m m' : Mem} {a : BitVec 64} {l : List Blake3.CV} (h : Cvs16.At m a l)
    (same : ∀ x : BitVec 64, x - a < 512#64 → m' x = m x) : Cvs16.At m' a l :=
  ⟨h.1, Cvl.At.frame l a (by rw [h.1]; decide) (fun x hx => same x (by rw [h.1] at hx; bv_omega)) h.2⟩

/-- Pairs are in their own bytes. -/
theorem Pairs.At.frame {m m' : Mem} {n a : BitVec 64} {l : List Blake3.CV} (h : Pairs.At n m a l)
    (same : ∀ x : BitVec 64, x - a < n <<< 6 → m' x = m x) : Pairs.At n m' a l := by
  obtain ⟨hn, hl, hat⟩ := h
  have hn' : n.toNat ≤ 16 := hn
  have es : (n <<< 6).toNat = 64 * n.toNat := by rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega
  refine ⟨hn, hl, Cvl.At.frame l a (by rw [hl]; omega) (fun x hx => same x ?_) hat⟩
  rw [hl] at hx
  generalize n <<< 6 = c at es
  bv_omega

/-- Thirty-two values are in their own 1024 bytes. -/
theorem Cvs32.At.frame {m m' : Mem} {a : BitVec 64} {l : List Blake3.CV} (h : Cvs32.At m a l)
    (same : ∀ x : BitVec 64, x - a < 1024#64 → m' x = m x) : Cvs32.At m' a l :=
  ⟨h.1, Cvl.At.frame l a (by rw [h.1]; decide) (fun x hx => same x (by rw [h.1] at hx; bv_omega)) h.2⟩
