import StackLemmas
import Spec_merge
import Kernels
open X86 Cells

/-! # `merge`: lemmas for the prover

Written by hand for this function; its source names them. `Merge.turn` carries the loop's invariant
across a turn (what a kernel leaves for the key and the two newest values is the specification's
parent, so merging what is left gives the same result); `Merge.exit` gives the statement's `ensures`
when the loop ends. Checked by Lean; not to be read. -/

theorem dw_mk4_0 (a b c d : BitVec 32) : dw (mk4 a b c d) 0 = a := by simp only [dw, mk4]; bv_decide
theorem dw_mk4_1 (a b c d : BitVec 32) : dw (mk4 a b c d) 1 = b := by simp only [dw, mk4]; bv_decide
theorem dw_mk4_2 (a b c d : BitVec 32) : dw (mk4 a b c d) 2 = c := by simp only [dw, mk4]; bv_decide
theorem dw_mk4_3 (a b c d : BitVec 32) : dw (mk4 a b c d) 3 = d := by simp only [dw, mk4]; bv_decide

unseal Kernels.out in
/-- **What a one-block kernel leaves for the key, two values, counter 0, length 64 and the flags with
PARENT is the specification's parent node's chaining value.** -/
theorem Merge.parent (k0 k1 l0 l1 r0 r1 : V) (flags : BitVec 64) (hf : flags < 256#64) :
    words8 (Kernels.out k0 k1 l0 l1 r0 r1 0#64 64#32 (BitVec.setWidth 32 (BitVec.setWidth 8 (flags ||| 4#64)))).1
        (Kernels.out k0 k1 l0 l1 r0 r1 0#64 64#32 (BitVec.setWidth 32 (BitVec.setWidth 8 (flags ||| 4#64)))).2
      = (Blake3.parentNode (words8 k0 k1) ⟨flags.setWidth 32⟩ (words8 l0 l1) (words8 r0 r1)).cv := by
  have hfl : BitVec.setWidth 32 (BitVec.setWidth 8 (flags ||| 4#64)) = flags.setWidth 32 ||| 4#32 := by bv_decide
  have h := parentCv_is_the_specifications k0 k1 l0 l1 r0 r1 (flags.setWidth 32)
  simp only [parentCv, BitVec.ofNat_eq_ofNat] at h
  simp only [Kernels.out, hfl, h, words8, dw_mk4_0, dw_mk4_1, dw_mk4_2, dw_mk4_3]
  ext i hi
  match i, hi with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ => simp [bv]

/-- **Across a turn:** the two newest values replaced by what the kernel leaves, merging gives what it gave. -/
theorem Merge.turn {k : Blake3.CV} {flags target len : BitVec 64} {r l : Blake3.CV} {rest cvs : List Blake3.CV}
    {k0 k1 l0 l1 r0 r1 : V}
    (h : Merge.result k flags target (r :: l :: rest) = Merge.result k flags target cvs)
    (hk : words8 k0 k1 = k) (hwl : words8 l0 l1 = l) (hwr : words8 r0 r1 = r)
    (hl : len = Stack.count (r :: l :: rest)) (ht : target < len) (hf : flags < 256#64) :
    Merge.result k flags target
        (words8 (Kernels.out k0 k1 l0 l1 r0 r1 0#64 64#32 (BitVec.setWidth 32 (BitVec.setWidth 8 (flags ||| 4#64)))).1
          (Kernels.out k0 k1 l0 l1 r0 r1 0#64 64#32 (BitVec.setWidth 32 (BitVec.setWidth 8 (flags ||| 4#64)))).2 :: rest)
      = Merge.result k flags target cvs := by
  have hlt : target.toNat < rest.length + 2 := by
    have h1 : len.toNat ≤ rest.length + 2 := by
      rw [hl]; simp only [Stack.count, List.length_cons, BitVec.toNat_ofNat]; exact Nat.mod_le _ _
    have h2 := BitVec.lt_def.mp ht
    omega
  rw [Merge.parent k0 k1 l0 l1 r0 r1 flags hf, hk, hwl, hwr, ← h]
  simp only [Merge.result]
  conv => rhs; rw [Blake3.mergeTo]
  rw [if_pos hlt]

/-- With `target` values or fewer, merging changes nothing. -/
theorem Merge.result_done (k : Blake3.CV) (flags target : BitVec 64) (cvs : List Blake3.CV)
    (h : ¬ target.toNat < cvs.length) : Merge.result k flags target cvs = cvs := by
  simp only [Merge.result]
  rcases cvs with _ | ⟨a, _ | ⟨b, rest⟩⟩
  · rw [Blake3.mergeTo]; all_goals simp
  · rw [Blake3.mergeTo]; all_goals simp
  · simp only [List.length_cons] at h
    rw [Blake3.mergeTo, if_neg h]

/-- **When the loop ends:** the invariant gives the statement's `ensures`. -/
theorem Merge.exit {m : Mem} {st len target flags : BitVec 64} {k : Blake3.CV} {now cvs : List Blake3.CV}
    (h : Stack.At m st now) (hl : len = Stack.count now)
    (he : Merge.result k flags target now = Merge.result k flags target cvs) (ht : ¬ target < len) :
    len.toNat = (Merge.result k flags target cvs).length ∧ Stack.At m st (Merge.result k flags target cvs) := by
  have hc := Stack.count_toNat h.1
  have hd : ¬ target.toNat < now.length := by rw [← hc, ← hl]; exact fun x => ht (BitVec.lt_def.mpr x)
  rw [← he, Merge.result_done k flags target now hd]
  exact ⟨by rw [hl, hc], h⟩
