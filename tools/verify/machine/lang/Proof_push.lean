import Cells
import Kernels
import AbiProof
import Spec_push
import Lemmas_push
import Code_push
open X86 Cells

/-! # `push`, as assembled, meets `Push.contract`

Written by prove_fn.py from hasher.ode and the compiler's layout; not edited by hand, and not to be read
but for its last theorem's statement: Lean checks the rest. The frame: 24 bytes below the stack pointer at entry
(`fb` is its lowest address), the caller's rbx, rbp, r12 at its top.
-/

namespace Proof_push

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option linter.unusedVariables false

theorem whole (fb st cv ra : BitVec 64) (sv : Abi.Saved) (new : Blake3.CV) (cvs : List Blake3.CV) (m0 : Mem)
    (s : State) (hP : Abi.Pre 0x70000 (Abi.Contract.framed (Push.contract st cv new cvs) 24#64) fb ra sv m0 s) : ∃ n_ s', steps Code_push.prog n_ s = some s' ∧ Abi.Post (Abi.Contract.framed (Push.contract st cv new cvs) 24#64) fb ra sv m0 s' := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r12, r13, r14, r15, zf, cf, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, mem, pc⟩ := s
  obtain ⟨hpc, hsp, hargs, hbx, hbp, h12, h13, h14, h15, hmem, hF, hRa, hAp, hAcc, hReq⟩ := hP
  simp only [Push.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true] at hpc hsp hargs hbx hbp h12 h13 h14 h15 hmem hF hRa
  simp only [List.length_cons, List.length_nil, List.take, List.cons.injEq, and_true] at hargs
  obtain ⟨ha0, ha1⟩ := hargs
  subst pc rsp rdi rsi rbx rbp r12 r13 r14 r15 mem
  have hAp0 := hAp
  simp only [Push.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, Abi.AllApart, Abi.Apart, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, BitVec.reduceAdd] at hAp
  split_ands hAp
  have hAcc0 := hAcc
  try (simp only [Push.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true] at hAcc; split_ands hAcc)
  have hReq0 := hReq
  simp only [Push.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true] at hReq
  split_ands hReq
  have_by hE0 := Stack.At.room (m := m0)
  try norm_addr at hE0
  split_ands hE0
  have_by hO0 := Cv.At.vectors (m := m0)
  obtain ⟨n0, n1, hO0⟩ := hO0
  try norm_addr at hO0
  split_ands hO0
  refine runs_then (a := 26) (s1 := ?_) ?_ ?_
  case refine_2 => run_fn []; rfl
  refine runs_done ⟨rfl, by simp only [Push.contract, Abi.Contract.framed]; bv_decide, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  all_goals try dsimp only
  · intro x hx hmod
    have hx' := hx
    have hmod' := hmod
    simp only [Push.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, BitVec.reduceAdd] at hx' hmod'
    first | rfl | mem_away
  · simp only [Push.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
    apply Push.exit <;> mem_auto

/-- **`push`, as assembled, meets its contract, whatever its arguments.** -/
theorem push_meets : ∀ (st cv : BitVec 64) (new : Blake3.CV) (cvs : List Blake3.CV),
    Abi.Meets Code_push.prog 0x70000 (Push.contract st cv new cvs) := by
  intro st cv new cvs
  refine Abi.meets_of_triple 24#64 (by dsimp only [Push.contract]; decide) (by dsimp only [Push.contract]; decide) (fun fb ra sv m0 => ?_)
  intro s hP
  exact whole fb st cv ra sv new cvs m0 s hP

#print axioms push_meets

end Proof_push
