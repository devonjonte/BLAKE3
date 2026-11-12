import Abi
import Spec_merge
import Spec_mergesteps
import Spec_push
import Spec_add
import Spec_hex
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

#print axioms Merge.usable
#print axioms Push.usable
#print axioms Add.usable
#print axioms Hex.usable
