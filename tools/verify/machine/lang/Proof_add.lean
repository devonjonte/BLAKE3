import Cells
import Kernels
import AbiProof
import AbiCall
import Spec_add
import Proof_push
import Proof_merge
import Code_add
open X86 Cells

/-! # `add`, as assembled, meets `Add.contract`

Written by prove_fn.py from hasher.ode and the compiler's layout; not edited by hand, and not to be read
but for its last theorem's statement: Lean checks the rest. The frame: 320 bytes below the stack pointer at entry
(`fb` is its lowest address), the caller's rbx, rbp, r12, r13, r14, r15 at its top.
-/

namespace Proof_add

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option linter.unusedVariables false

theorem whole (fb st key flags plat cv target ra : BitVec 64) (sv : Abi.Saved) (k : Blake3.CV) (new : Blake3.CV) (cvs : List Blake3.CV) (m0 : Mem)
    (s : State) (hP : Abi.Pre 0x80000 (Abi.Contract.framed (Add.contract st key flags plat cv target k new cvs) 320#64) fb ra sv m0 s) : ∃ n_ s', steps Code_add.prog n_ s = some s' ∧ Abi.Post (Abi.Contract.framed (Add.contract st key flags plat cv target k new cvs) 320#64) fb ra sv m0 s' := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r12, r13, r14, r15, zf, cf, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, mem, pc⟩ := s
  obtain ⟨hpc, hsp, hargs, hbx, hbp, h12, h13, h14, h15, hmem, hF, hRa, hAp, hAcc, hReq⟩ := hP
  simp only [Add.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true] at hpc hsp hargs hbx hbp h12 h13 h14 h15 hmem hF hRa
  simp only [List.length_cons, List.length_nil, List.take, List.cons.injEq, and_true] at hargs
  obtain ⟨ha0, ha1, ha2, ha3, ha4, ha5⟩ := hargs
  subst pc rsp rdi rsi rdx rcx r8 r9 rbx rbp r12 r13 r14 r15 mem
  have hAp0 := hAp
  simp only [Add.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, Abi.AllApart, Abi.Apart, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, BitVec.reduceAdd] at hAp
  split_ands hAp
  have hAcc0 := hAcc
  try (simp only [Add.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true] at hAcc; split_ands hAcc)
  have hReq0 := hReq
  simp only [Add.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true] at hReq
  split_ands hReq
  refine runs_then (a := 16) (s1 := ?_) ?_ ?_
  case refine_2 => run_fn []; rfl
  refine Abi.call_meets (c := Push.contract st cv new cvs) (ra := 524331#64)
    (Abi.Meets.mono Code_add.has_push (Proof_push.push_meets st cv new cvs)) rfl rfl ?_ ?_ ?_ ?_ ?_ ?_
  · dsimp only; mem_fact
  · dsimp only [Push.contract]; mem_subregion
  · dsimp only
    simp only [Push.contract, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, Abi.AllApart, Abi.Apart, BitVec.reduceAdd]
    try simp only [add_sub_lit, BitVec.add_assoc, BitVec.add_zero, BitVec.reduceAdd, BitVec.reduceSub]
    repeat' (with_reducible apply And.intro)
    all_goals bv_decide
  · simp only [Push.contract]
    repeat' (with_reducible apply And.intro)
    all_goals assumption
  · dsimp only
    simp only [Push.contract, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
    repeat' (with_reducible apply And.intro)
    all_goals (first | mem_auto | (apply_frame <;> mem_auto))
  · intro s1 hpc1 hsp1 hbx1 hbp1 h12_1 h13_1 h14_1 h15_1 hens1 hout1 hown1
    obtain ⟨rax_1, rcx_1, rdx_1, rbx_1, rsp_1, rbp_1, rsi_1, rdi_1, r8_1, r9_1, r12_1, r13_1, r14_1, r15_1, zf_1, cf_1, y1_0, y1_1, y1_2, y1_3, y1_4, y1_5, y1_6, y1_7, y1_8, y1_9, y1_10, y1_11, y1_12, y1_13, y1_14, y1_15, mem1, pc_1⟩ := s1
    dsimp only at hpc1 hsp1 hbx1 hbp1 h12_1 h13_1 h14_1 h15_1 hens1 hout1 hown1
    subst pc_1 rsp_1 rbx_1 rbp_1 r12_1 r13_1 r14_1 r15_1
    simp only [Push.contract, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true] at hens1
    split_ands hens1
    simp only [Push.contract, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, add_sub_lit, BitVec.add_assoc, BitVec.add_zero, BitVec.reduceAdd, BitVec.reduceSub] at hout1
    have hF1 : Region mem1 fb 320#64 := hown1 fb 320#64 (by mem_region)
    have hS1_0 : Quad mem1 (fb + 320#64) ra := X86.Quad.frame (by mem_fact) (fun x hx => hout1 x (by bv_decide) (by bv_decide))
    have hS1_1 : Quad mem1 (fb + 312#64) sv.rbx := X86.Quad.frame (by mem_fact) (fun x hx => hout1 x (by bv_decide) (by bv_decide))
    have hS1_2 : Quad mem1 (fb + 304#64) sv.rbp := X86.Quad.frame (by mem_fact) (fun x hx => hout1 x (by bv_decide) (by bv_decide))
    have hS1_3 : Quad mem1 (fb + 296#64) sv.r12 := X86.Quad.frame (by mem_fact) (fun x hx => hout1 x (by bv_decide) (by bv_decide))
    have hS1_4 : Quad mem1 (fb + 288#64) sv.r13 := X86.Quad.frame (by mem_fact) (fun x hx => hout1 x (by bv_decide) (by bv_decide))
    have hS1_5 : Quad mem1 (fb + 280#64) sv.r14 := X86.Quad.frame (by mem_fact) (fun x hx => hout1 x (by bv_decide) (by bv_decide))
    have hS1_6 : Quad mem1 (fb + 272#64) sv.r15 := X86.Quad.frame (by mem_fact) (fun x hx => hout1 x (by bv_decide) (by bv_decide))
    have hK1_0 : Cv.At mem1 key k := Cv.At.frame (m := m0) (by assumption) (fun x hx => by rw [hout1 x (by bv_decide) (by bv_decide)]; first | rfl | mem_away)
    have hOut1 : (∀ x : BitVec 64, (Abi.Contract.framed (Add.contract st key flags plat cv target k new cvs) 320#64).stack + 8#64 ≤ x - fb → (∀ r ∈ (Abi.Contract.framed (Add.contract st key flags plat cv target k new cvs) 320#64).modifies, r.2 ≤ x - r.1) → mem1 x = m0 x) := by
      intro x hx hmod
      have hx' := hx
      have hmod' := hmod
      simp only [Add.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, BitVec.reduceAdd] at hx' hmod'
      rw [hout1 x (by bv_decide) (by bv_decide)]
      first | rfl | mem_away
    clear hout1 hown1
    refine runs_then (a := 6) (s1 := ?_) ?_ ?_
    case refine_2 => run_fn []; rfl
    refine Abi.call_meets (c := Merge.contract st key flags plat target k (new :: cvs)) (ra := 524351#64)
      (Abi.Meets.mono Code_add.has_merge (Proof_merge.merge_meets st key flags plat target k (new :: cvs))) rfl rfl ?_ ?_ ?_ ?_ ?_ ?_
    · dsimp only; mem_fact
    · dsimp only [Merge.contract]; mem_subregion
    · dsimp only
      simp only [Merge.contract, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, Abi.AllApart, Abi.Apart, BitVec.reduceAdd]
      try simp only [add_sub_lit, BitVec.add_assoc, BitVec.add_zero, BitVec.reduceAdd, BitVec.reduceSub]
      repeat' (with_reducible apply And.intro)
      all_goals bv_decide
    · simp only [Merge.contract]
      repeat' (with_reducible apply And.intro)
      all_goals assumption
    · dsimp only
      simp only [Merge.contract, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
      repeat' (with_reducible apply And.intro)
      all_goals (first | mem_auto | (apply_frame <;> mem_auto))
    · intro s2 hpc2 hsp2 hbx2 hbp2 h12_2 h13_2 h14_2 h15_2 hens2 hout2 hown2
      obtain ⟨rax_2, rcx_2, rdx_2, rbx_2, rsp_2, rbp_2, rsi_2, rdi_2, r8_2, r9_2, r12_2, r13_2, r14_2, r15_2, zf_2, cf_2, y2_0, y2_1, y2_2, y2_3, y2_4, y2_5, y2_6, y2_7, y2_8, y2_9, y2_10, y2_11, y2_12, y2_13, y2_14, y2_15, mem2, pc_2⟩ := s2
      dsimp only at hpc2 hsp2 hbx2 hbp2 h12_2 h13_2 h14_2 h15_2 hens2 hout2 hown2
      subst pc_2 rsp_2 rbx_2 rbp_2 r12_2 r13_2 r14_2 r15_2
      simp only [Merge.contract, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true] at hens2
      split_ands hens2
      simp only [Merge.contract, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, add_sub_lit, BitVec.add_assoc, BitVec.add_zero, BitVec.reduceAdd, BitVec.reduceSub] at hout2
      have hF2 : Region mem2 fb 320#64 := hown2 fb 320#64 (by mem_region)
      have hS2_0 : Quad mem2 (fb + 320#64) ra := X86.Quad.frame (by mem_fact) (fun x hx => hout2 x (by bv_decide) (by bv_decide))
      have hS2_1 : Quad mem2 (fb + 312#64) sv.rbx := X86.Quad.frame (by mem_fact) (fun x hx => hout2 x (by bv_decide) (by bv_decide))
      have hS2_2 : Quad mem2 (fb + 304#64) sv.rbp := X86.Quad.frame (by mem_fact) (fun x hx => hout2 x (by bv_decide) (by bv_decide))
      have hS2_3 : Quad mem2 (fb + 296#64) sv.r12 := X86.Quad.frame (by mem_fact) (fun x hx => hout2 x (by bv_decide) (by bv_decide))
      have hS2_4 : Quad mem2 (fb + 288#64) sv.r13 := X86.Quad.frame (by mem_fact) (fun x hx => hout2 x (by bv_decide) (by bv_decide))
      have hS2_5 : Quad mem2 (fb + 280#64) sv.r14 := X86.Quad.frame (by mem_fact) (fun x hx => hout2 x (by bv_decide) (by bv_decide))
      have hS2_6 : Quad mem2 (fb + 272#64) sv.r15 := X86.Quad.frame (by mem_fact) (fun x hx => hout2 x (by bv_decide) (by bv_decide))
      have hOut2 : (∀ x : BitVec 64, (Abi.Contract.framed (Add.contract st key flags plat cv target k new cvs) 320#64).stack + 8#64 ≤ x - fb → (∀ r ∈ (Abi.Contract.framed (Add.contract st key flags plat cv target k new cvs) 320#64).modifies, r.2 ≤ x - r.1) → mem2 x = m0 x) := by
        intro x hx hmod
        have hx' := hx
        have hmod' := hmod
        simp only [Add.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, BitVec.reduceAdd] at hx' hmod'
        rw [hout2 x (by bv_decide) (by bv_decide)]
        refine Eq.trans ?_ (hOut1 x hx hmod); first | rfl | mem_away
      clear hout2 hown2
      refine runs_then (a := 9) (s1 := ?_) ?_ ?_
      case refine_2 => run_fn []; rfl
      refine runs_done ⟨rfl, by simp only [Add.contract, Abi.Contract.framed]; bv_decide, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
      all_goals try dsimp only
      · intro x hx hmod
        exact hOut2 x hx hmod
      · simp only [Add.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
        repeat' (with_reducible apply And.intro)
        all_goals (first | trivial | assumption)

/-- **`add`, as assembled, meets its contract, whatever its arguments.** -/
theorem add_meets : ∀ (st key flags plat cv target : BitVec 64) (k : Blake3.CV) (new : Blake3.CV) (cvs : List Blake3.CV),
    Abi.Meets Code_add.prog 0x80000 (Add.contract st key flags plat cv target k new cvs) := by
  intro st key flags plat cv target k new cvs
  refine Abi.meets_of_triple 320#64 (by dsimp only [Add.contract]; decide) (by dsimp only [Add.contract]; decide) (fun fb ra sv m0 => ?_)
  intro s hP
  exact whole fb st key flags plat cv target ra sv k new cvs m0 s hP

#print axioms add_meets

end Proof_add
