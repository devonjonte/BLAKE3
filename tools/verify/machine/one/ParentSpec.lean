import Bridge32
import ParentCv
open X86

/-! # The parent chaining value, in the specification's own words

`parentCv`, which `parent_cv_by_the_crates_code` proves the compiled code leaves, is the chaining
value of the specification's `Blake3.parentNode` (section 4.2 and 4.3 of C2SP's BLAKE3). -/

/-- Eight words of the specification from two vectors of memory. -/
def words8 (a b : V) : Vector UInt32 8 :=
  #v[⟨dw a 0⟩, ⟨dw a 1⟩, ⟨dw a 2⟩, ⟨dw a 3⟩, ⟨dw b 0⟩, ⟨dw b 1⟩, ⟨dw b 2⟩, ⟨dw b 3⟩]

theorem words8_bv (a b : V) : (words8 a b).map bv = cvWords a b := by
  ext i hi
  simp only [Vector.getElem_map]
  match i, hi with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ => rfl

theorem block_bv (l0 l1 r0 r1 : V) : (words8 l0 l1 ++ words8 r0 r1).map bv = blockWords l0 l1 r0 r1 := by
  ext i hi
  simp only [Vector.getElem_map]
  match i, hi with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _ | 10, _ | 11, _ | 12, _ | 13, _ | 14, _ | 15, _ => rfl
  | n + 16, h => exact absurd h (by omega)

/-- **The compiled code's result is the specification's parent node's chaining value.** -/
theorem parentCv_is_the_specifications (k0 k1 l0 l1 r0 r1 : V) (mode : BitVec 32) :
    parentCv (cvWords k0 k1) l0 l1 r0 r1 mode
      = (Blake3.parentNode (words8 k0 k1) ⟨mode⟩ (words8 l0 l1) (words8 r0 r1)).cv.map bv := by
  have h := specCv_is_the_specifications (words8 k0 k1) (words8 l0 l1 ++ words8 r0 r1) 0 64 (⟨mode⟩ ||| Blake3.PARENT)
  rw [words8_bv, block_bv] at h
  exact h

#print axioms parentCv_is_the_specifications
