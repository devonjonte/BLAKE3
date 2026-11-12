import Cells
import AbiProof
import Proof_merge
open X86 Cells

/-! # The checked entry of `merge` meets `Merge.contract … |>.checked`

Written by check_fn.py from what `#checks Merge.contract` read in the contract; not edited by hand, and not to be read
but for the theorem's statement: Lean checks the rest. -/

namespace Checked_merge

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- **The checked entry of `merge`, as assembled, meets the contract's checked form, whatever its arguments:**
it does as `Merge.contract` says where that accepts them, and returns 18446744073709551615 having changed nothing where it does not. -/
theorem merge_checked_meets : ∀ (st key flags plat target : BitVec 64) (k : Blake3.CV) (cvs : List Blake3.CV),
    Abi.Meets Code_merge.prog 0x60140 ((Merge.contract st key flags plat target k cvs).checked 18446744073709551615#64) := by
  intro st key flags plat target k cvs s ra hpc hargs hra hstack hap _ hreq
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r12, r13, r14, r15, zf, cf, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, mem, pc⟩ := s
  have hargs0 := hargs
  simp only [Merge.contract, Abi.Contract.checked, List.length_cons, List.length_nil, List.take, List.cons.injEq, and_true] at hargs0
  obtain ⟨ha0, ha1, ha2, ha3, ha4⟩ := hargs0
  simp only at hpc
  subst pc rdi rsi rdx rcx r8
  have hra' := hra
  simp only at hra'
  by_cases h0 : 1#64 ≤ target
  · have c0 : (target).ult (1#64) = false := by bv_decide
    by_cases h1 : flags < 256#64
    · have c1 : (flags).ult (256#64) = true := by bv_decide
      exact Abi.checked_accepted (Proof_merge.merge_meets st key flags plat target k cvs) (K := 5) (by run_fn [c0, c1]; rfl)
        (show 1#64 ≤ target ∧ flags < 256#64 from ⟨h0, h1⟩) hargs hra hstack hap hreq
    · have c1 : (flags).ult (256#64) = false := by bv_decide
      exact Abi.checked_refused (K := 6) (by run_fn [c0, c1]; rfl)
        (fun h => absurd (show 1#64 ≤ target ∧ flags < 256#64 from h).2 h1) hreq
  · have c0 : (target).ult (1#64) = true := by bv_decide
    exact Abi.checked_refused (K := 5) (by run_fn [c0]; rfl)
      (fun h => absurd (show 1#64 ≤ target ∧ flags < 256#64 from h).1 h0) hreq

#print axioms merge_checked_meets

end Checked_merge
