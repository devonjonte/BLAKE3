import Abi
import Spec_merge
import Spec_mergesteps
import Spec_push
import Spec_add
import Spec_hex
import Spec_ladd
import Spec_lroot
import Lemmas_ladd
open X86

/-! # Each contract can be used

For each contract, arguments and a memory that give it everything it asks: so no theorem here is about a
contract nothing can satisfy. The memory is the plainest there is (every address the program's, every byte
zero; an empty stack; a key, a value and a hash of zeroes): this shows the requirements do not contradict
one another, and no more. The examples (`Example_*.lean`) are the richer test, by running. -/

/-- Every address the program's, every byte zero. -/
def zeroMem : Mem := fun _ => some 0#8

theorem zeroMem_region (b n : BitVec 64) : Cells.Region zeroMem b n := fun _ _ => rfl
theorem zeroMem_quad (a : BitVec 64) : Quad zeroMem a 0#64 := by
  simp only [Quad, zeroMem, Option.some.injEq, byte]; decide
theorem zeroMem_vec (a : BitVec 64) : Vec zeroMem a 0#128 := by
  simp only [Vec, zeroMem, Option.some.injEq, by8]; decide

/-- The chaining value of zeroes. -/
def zeroCv : Blake3.CV := words8 0#128 0#128

theorem zeroMem_cv (a : BitVec 64) : Cv.At zeroMem a zeroCv := ⟨0#128, 0#128, zeroMem_vec a, zeroMem_vec _, rfl⟩
theorem zeroMem_stack (a : BitVec 64) : Stack.At zeroMem a [] := ⟨by decide, zeroMem_region _ _, zeroMem_quad a, trivial⟩

theorem Merge.usable : (Merge.contract 0x100000#64 0x200000#64 0#64 5#64 1#64 zeroCv []).Usable := by
  refine ⟨0x7ff00000#64, zeroMem, zeroMem_region _ _, ?_, ?_, ?_⟩
  · simp only [Merge.contract, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, Abi.AllApart, Abi.Apart]; decide
  · simp only [Merge.contract]; decide
  · simp only [Merge.contract, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
    exact ⟨zeroMem_stack _, zeroMem_cv _⟩

theorem MergeSteps.usable : (MergeSteps.contract 0x100000#64 0x200000#64 0#64 5#64 1#64 zeroCv []).Usable := by
  refine ⟨0x7ff00000#64, zeroMem, zeroMem_region _ _, ?_, ?_, ?_⟩
  · simp only [MergeSteps.contract, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, Abi.AllApart, Abi.Apart]; decide
  · simp only [MergeSteps.contract]; decide
  · simp only [MergeSteps.contract, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
    exact ⟨zeroMem_stack _, zeroMem_cv _⟩

theorem Push.usable : (Push.contract 0x100000#64 0x200000#64 zeroCv []).Usable := by
  refine ⟨0x7ff00000#64, zeroMem, zeroMem_region _ _, ?_, ?_, ?_⟩
  · simp only [Push.contract, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, Abi.AllApart, Abi.Apart]; decide
  · simp only [Push.contract]; decide
  · simp only [Push.contract, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
    exact ⟨zeroMem_stack _, zeroMem_cv _⟩

theorem Add.usable : (Add.contract 0x100000#64 0x200000#64 0#64 5#64 0x300000#64 1#64 zeroCv zeroCv []).Usable := by
  refine ⟨0x7ff00000#64, zeroMem, zeroMem_region _ _, ?_, ?_, ?_⟩
  · simp only [Add.contract, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, Abi.AllApart, Abi.Apart]; decide
  · simp only [Add.contract]; decide
  · simp only [Add.contract, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
    exact ⟨zeroMem_stack _, zeroMem_cv _, zeroMem_cv _⟩

theorem Hex.usable : (Hex.contract 0x100000#64 0x200000#64 (List.replicate 32 0#8)).Usable := by
  refine ⟨0x7ff00000#64, zeroMem, zeroMem_region _ _, ?_, ?_, ?_⟩
  · simp only [Hex.contract, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, Abi.AllApart, Abi.Apart]; decide
  · simp only [Hex.contract]
  · simp only [Hex.contract, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
    refine ⟨zeroMem_region _ _, List.length_replicate, ?_⟩
    intro i h
    simp only [zeroMem, List.getElem_replicate]

/-- Any chaining value is two vectors of memory. -/
theorem cv_vectors (c : Blake3.CV) : ∃ v0 v1 : V, words8 v0 v1 = c :=
  ⟨mk4 c[0].toBitVec c[1].toBitVec c[2].toBitVec c[3].toBitVec, mk4 c[4].toBitVec c[5].toBitVec c[6].toBitVec c[7].toBitVec, by
    simp only [words8, dw_mk4_0, dw_mk4_1, dw_mk4_2, dw_mk4_3]
    ext i hi
    match i, hi with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ => rfl⟩

/-- No chunk yet, and a first chunk's value (a node of zeroes') at its address. -/
theorem Ladd.usable : (Ladd.contract 0x100000#64 0x200000#64 0#64 5#64 0x300000#64 zeroCv #[] default).Usable := by
  obtain ⟨v0, v1, hv⟩ := cv_vectors (default : Blake3.Node).cv
  have hq := zeroMem_quad 0x100000#64
  obtain ⟨k0, k1, hk0, hk1, hk⟩ := zeroMem_cv 0x200000#64
  refine ⟨0x7ff00000#64, (zeroMem.put128 0x300000#64 v0).put128 (0x300000#64 + 16#64) v1,
    Cells.region_put128 _ _ (Cells.region_put128 _ _ (zeroMem_region _ _)), ?_, ?_, ?_⟩
  · simp only [Ladd.contract, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, Abi.AllApart, Abi.Apart]; decide
  · simp only [Ladd.contract]; decide
  · simp only [Ladd.contract, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
    refine ⟨⟨by decide, Cells.region_put128 _ _ (Cells.region_put128 _ _ (zeroMem_region _ _)), ?_, fun h => absurd h (by decide)⟩,
      ⟨k0, k1, ?_, ?_, hk⟩, ⟨v0, v1, ?_, ?_, hv⟩⟩
    · show Quad _ _ 0#64
      exact Cells.quad_put128_far _ _ _ _ _ (by decide) (Cells.quad_put128_far _ _ _ _ _ (by decide) hq)
    · exact Cells.vec_put128_far _ _ _ _ _ (by decide) (Cells.vec_put128_far _ _ _ _ _ (by decide) hk0)
    · exact Cells.vec_put128_far _ _ _ _ _ (by decide) (Cells.vec_put128_far _ _ _ _ _ (by decide) hk1)
    · exact Cells.vec_put128_far _ _ _ _ _ (by decide) (vec_put128 _ _ _)
    · exact vec_put128 _ _ _

/-- Two chunks (two nodes of zeroes') in the bottom level's two places, the count 2, a key of zeroes. -/
theorem Lroot.usable : (Lroot.contract 0x300000#64 0x100000#64 0x200000#64 0#64 5#64 zeroCv #[default, default]).Usable := by
  obtain ⟨v0, v1, hv⟩ := cv_vectors (default : Blake3.Node).cv
  obtain ⟨k0, k1, hk0, hk1, hk⟩ := zeroMem_cv 0x200000#64
  have reg : ∀ b n : BitVec 64, Cells.Region
      (((((zeroMem.put64 0x100000#64 2#64).put128 0x100040#64 v0).put128 0x100050#64 v1).put128 0x100060#64 v0).put128 0x100070#64 v1) b n :=
    fun b n => Cells.region_put128 _ _ (Cells.region_put128 _ _ (Cells.region_put128 _ _ (Cells.region_put128 _ _ (Cells.region_put64 _ _ (zeroMem_region b n)))))
  refine ⟨0x7ff00000#64, ((((zeroMem.put64 0x100000#64 2#64).put128 0x100040#64 v0).put128 0x100050#64 v1).put128 0x100060#64 v0).put128 0x100070#64 v1,
    reg _ _, ?_, ?_, ?_⟩
  · simp only [Lroot.contract, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, Abi.AllApart, Abi.Apart]; decide
  · simp only [Lroot.contract]; decide
  · simp only [Lroot.contract, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
    have sub0 : Blake3.sub zeroCv ⟨BitVec.setWidth 32 0#64⟩ #[default, default] 0 1 = (default : Blake3.Node).cv := by
      simp only [Blake3.sub, Blake3.go_one]; rfl
    have sub1 : Blake3.sub zeroCv ⟨BitVec.setWidth 32 0#64⟩ #[default, default] 1 1 = (default : Blake3.Node).cv := by
      simp only [Blake3.sub, Blake3.go_one]; rfl
    refine ⟨reg _ _, ⟨k0, k1, ?_, ?_, hk⟩, by decide, reg _ _, ?_, fun _ => ⟨?_, ⟨v0, v1, ?_, ?_, ?_⟩⟩⟩
    · exact Cells.vec_put128_far _ _ _ _ _ (by decide) (Cells.vec_put128_far _ _ _ _ _ (by decide) (Cells.vec_put128_far _ _ _ _ _ (by decide) (Cells.vec_put128_far _ _ _ _ _ (by decide) (Cells.vec_put64_far _ _ _ _ _ (by decide) hk0))))
    · exact Cells.vec_put128_far _ _ _ _ _ (by decide) (Cells.vec_put128_far _ _ _ _ _ (by decide) (Cells.vec_put128_far _ _ _ _ _ (by decide) (Cells.vec_put128_far _ _ _ _ _ (by decide) (Cells.vec_put64_far _ _ _ _ _ (by decide) hk1))))
    · show Quad _ _ 2#64
      exact Cells.quad_put128_far _ _ _ _ _ (by decide) (Cells.quad_put128_far _ _ _ _ _ (by decide) (Cells.quad_put128_far _ _ _ _ _ (by decide) (Cells.quad_put128_far _ _ _ _ _ (by decide) (quad_put64 _ _ _))))
    · show Levels.Lev _ _ _ _ (53 + 1) _ 1 1
      rw [Levels.Lev_succ]
      refine ⟨fun _ => ⟨v0, v1, ?_, ?_, by rw [hv]; exact sub0.symm⟩, Levels.Lev_none _ _ _ _⟩
      · exact Cells.vec_put128_far _ _ _ _ _ (by decide) (Cells.vec_put128_far _ _ _ _ _ (by decide) (Cells.vec_put128_far _ _ _ _ _ (by decide) (vec_put128 _ _ _)))
      · exact Cells.vec_put128_far _ _ _ _ _ (by decide) (Cells.vec_put128_far _ _ _ _ _ (by decide) (vec_put128 _ _ _))
    · exact Cells.vec_put128_far _ _ _ _ _ (by decide) (vec_put128 _ _ _)
    · exact vec_put128 _ _ _
    · rw [hv]; exact sub1.symm

#print axioms Merge.usable
#print axioms Lroot.usable
#print axioms Ladd.usable
#print axioms Push.usable
#print axioms Add.usable
#print axioms Hex.usable
