import StackSpec
import MergeSpec
open X86 MergeCode

/-! # What `merge`'s contract promises, in the specification's terms

The contract in hasher.ode ends with the stack `Stack.merged k0 k1 fl target es0`. Read as the
specification's chaining values, that is `Blake3.mergeTo`: the function `alg/Stack.lean` proves a
hasher may merge its stack with and still compute BLAKE3's tree (`stack_is_the_tree`). Written by hand:
it is about the specification, not about any code. -/

/-- **`Stack.merged` is `Blake3.mergeTo`.** For the mode's flags below 256 and a target of at least one. -/
theorem Stack.merged_is_mergeTo (k0 k1 : V) (flags target : BitVec 64) (es : Stack.Cvs)
    (hfl : flags < 256#64) (h1 : 1#64 ≤ target) :
    (Stack.merged k0 k1 ((flags ||| 4#64).setWidth 8) target es).map cvOf =
      Blake3.mergeTo (words8 k0 k1) ⟨flags.setWidth 32⟩ target.toNat (es.map cvOf) := by
  have hf : ((flags ||| 4#64).setWidth 8).setWidth 32 = flags.setWidth 32 ||| 4 := by bv_decide
  have ht : 1 ≤ target.toNat := by bv_omega
  by_cases h : target.toNat < es.length
  · have := mergeN_is_mergeTo k0 k1 (flags.setWidth 32) ((flags ||| 4#64).setWidth 8) hf (es.length - target.toNat) es (by omega)
    rw [show es.length - (es.length - target.toNat) = target.toNat by omega] at this
    simp only [Stack.merged]; exact this.symm
  · have e : es.length - target.toNat = 0 := by omega
    simp only [Stack.merged, e]
    rcases es with _ | ⟨a, _ | ⟨b, rest⟩⟩
    · rw [Blake3.mergeTo]; rfl; all_goals simp
    · rw [Blake3.mergeTo]; rfl; all_goals simp
    · simp only [List.map_cons, mergeN, List.length_cons] at h ⊢
      rw [Blake3.mergeTo, if_neg (by simp only [List.length_map]; omega)]

#print axioms Stack.merged_is_mergeTo
