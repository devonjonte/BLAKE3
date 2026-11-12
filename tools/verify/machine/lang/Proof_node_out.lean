import Cells
import Kernels
import AbiProof
import Spec_nodeout
import Lemmas_node
import Code_node_out
open X86 Cells

/-! # `node_out`, as assembled, meets `NodeOut.contract`

Written by prove_fn.py from levels.ode and the compiler's layout; not edited by hand, and not to be read
but for its last theorem's statement: Lean checks the rest. The frame: 80 bytes below the stack pointer at entry
(`fb` is its lowest address), the caller's rbx, rbp, r12, r13, r14, r15 at its top.
-/

namespace Proof_node_out

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option linter.unusedVariables false

theorem whole (fb out nd root plat ra : BitVec 64) (sv : Abi.Saved) (node : Blake3.Node) (m0 : Mem)
    (s : State) (hP : Abi.Pre 0xD0000 (Abi.Contract.framed (NodeOut.contract out nd root plat node) 80#64) fb ra sv m0 s) : ∃ n_ s', steps Code_node_out.prog n_ s = some s' ∧ Abi.Post (Abi.Contract.framed (NodeOut.contract out nd root plat node) 80#64) fb ra sv m0 s' := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r12, r13, r14, r15, zf, cf, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, mem, pc⟩ := s
  obtain ⟨hpc, hsp, hargs, hbx, hbp, h12, h13, h14, h15, hmem, hF, hRa, hAp, hAcc, hReq⟩ := hP
  simp only [NodeOut.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true] at hpc hsp hargs hbx hbp h12 h13 h14 h15 hmem hF hRa
  simp only [List.length_cons, List.length_nil, List.take, List.cons.injEq, and_true] at hargs
  obtain ⟨ha0, ha1, ha2, ha3⟩ := hargs
  subst pc rsp rdi rsi rdx rcx rbx rbp r12 r13 r14 r15 mem
  have hAp0 := hAp
  simp only [NodeOut.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, Abi.AllApart, Abi.Apart, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, BitVec.reduceAdd] at hAp
  split_ands hAp
  have hAcc0 := hAcc
  try (simp only [NodeOut.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true] at hAcc; split_ands hAcc)
  have hReq0 := hReq
  simp only [NodeOut.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true] at hReq
  split_ands hReq
  have_by hE0 := Node.At.cells (m := m0)
  try norm_addr at hE0
  split_ands hE0
  have_by hO0 := Node.At.vectors (m := m0)
  obtain ⟨h0, h1, b0, b1, b2, b3, hO0⟩ := hO0
  try norm_addr at hO0
  split_ands hO0
  by_cases hs0 : plat = 5#64
  · have c0 : (plat - 5#64 == 0#64) = true := by bv_decide
    refine runs_then (a := 43) (s1 := ?_) ?_ ?_
    case refine_2 => run_fn [c0]; rfl
    refine Kernels.call_avx_runs Code_node_out.has_kernels (by mem_auto) (by mem_auto) (by mem_auto) (by mem_auto) (by mem_auto) (by mem_auto) (by mem_auto) (by mem_auto) ?_
    intro rax' rcx' rdx' rsi' rdi' r8' r9' zf' cf' y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15
    refine runs_then (a := 9) (s1 := ?_) ?_ ?_
    case refine_2 => run_fn [c0]; rfl
    refine runs_done ⟨rfl, by simp only [NodeOut.contract, Abi.Contract.framed]; bv_decide, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
    all_goals try dsimp only
    · intro x hx hmod
      have hx' := hx
      have hmod' := hmod
      simp only [NodeOut.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, BitVec.reduceAdd] at hx' hmod'
      first | rfl | mem_away
    · simp only [NodeOut.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
      apply NodeOut.exit <;> mem_auto
  · have c0 : (plat - 5#64 == 0#64) = false := by bv_decide
    refine runs_then (a := 43) (s1 := ?_) ?_ ?_
    case refine_2 => run_fn [c0]; rfl
    refine Kernels.call_sse_runs Code_node_out.has_kernels (by mem_auto) (by mem_auto) (by mem_auto) (by mem_auto) (by mem_auto) (by mem_auto) (by mem_auto) (by mem_auto) (by mem_auto) (by mem_auto) ?_
    intro rax' rcx' rdx' rsi' rdi' r8' r9' zf' cf' y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15
    refine runs_then (a := 8) (s1 := ?_) ?_ ?_
    case refine_2 => run_fn [c0]; rfl
    refine runs_done ⟨rfl, by simp only [NodeOut.contract, Abi.Contract.framed]; bv_decide, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
    all_goals try dsimp only
    · intro x hx hmod
      have hx' := hx
      have hmod' := hmod
      simp only [NodeOut.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, BitVec.reduceAdd] at hx' hmod'
      first | rfl | mem_away
    · simp only [NodeOut.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
      apply NodeOut.exit <;> mem_auto

/-- **`node_out`, as assembled, meets its contract, whatever its arguments.** -/
theorem node_out_meets : ∀ (out nd root plat : BitVec 64) (node : Blake3.Node),
    Abi.Meets Code_node_out.prog 0xD0000 (NodeOut.contract out nd root plat node) := by
  intro out nd root plat node
  refine Abi.meets_of_triple 80#64 (by dsimp only [NodeOut.contract]; decide) (by dsimp only [NodeOut.contract]; decide) (fun fb ra sv m0 => ?_)
  intro s hP
  exact whole fb out nd root plat ra sv node m0 s hP

#print axioms node_out_meets

end Proof_node_out
