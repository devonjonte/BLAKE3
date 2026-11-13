import Cells
import AbiProof
import Proof_tree32
open X86 Cells

/-! # The checked entry of `tree32` meets `Tree32.contract … |>.checked`

Written by check_fn.py from what `#checks Tree32.contract` read in the contract; not edited by hand, and not to be read
but for the theorem's statement: Lean checks the rest. -/

namespace Checked_tree32

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- **The checked entry of `tree32`, as assembled, meets the contract's checked form, whatever its arguments:**
it does as `Tree32.contract` says where that accepts them, and returns 18446744073709551615 having changed nothing where it does not. -/
theorem tree32_checked_meets (ext : Nat → Option (Instr × Nat)) (hA_parents16 : ∀ x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10, Abi.Meets (Code_tree32.prog ext) 0x18000 (P16.contract x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10)) : ∀ (res cvs key flags : BitVec 64) (k : Blake3.CV) (l : List Blake3.CV),
    Abi.Meets (Code_tree32.prog ext) 0x120190 ((Tree32.contract res cvs key flags k l).checked 18446744073709551615#64) := by
  intro res cvs key flags k l s ra hpc hargs hra hstack hap _ hreq
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r12, r13, r14, r15, zf, cf, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, mem, pc⟩ := s
  have hargs0 := hargs
  simp only [Tree32.contract, Abi.Contract.checked, List.length_cons, List.length_nil, List.take, List.cons.injEq, and_true] at hargs0
  obtain ⟨ha0, ha1, ha2, ha3⟩ := hargs0
  simp only at hpc
  subst pc rdi rsi rdx rcx
  have hra' := hra
  simp only at hra'
  by_cases h0 : flags < 256#64
  · have c0 : (flags).ult (256#64) = true := by bv_decide
    exact Abi.checked_accepted (Proof_tree32.tree32_meets ext hA_parents16 res cvs key flags k l) (K := 3) (by run_fn [c0]; rfl)
      (show flags < 256#64 from h0) hargs hra hstack hap hreq
  · have c0 : (flags).ult (256#64) = false := by bv_decide
    exact Abi.checked_refused (K := 4) (by run_fn [c0]; rfl)
      (fun h => absurd (show flags < 256#64 from h) h0) hreq

#print axioms tree32_checked_meets

end Checked_tree32
