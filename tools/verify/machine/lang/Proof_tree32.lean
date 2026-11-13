import Cells
import Kernels
import AbiProof
import AbiCall
import Spec_tree32
import Lemmas_tree32
import Proof_fillp
import Code_tree32
open X86 Cells

/-! # `tree32`, as assembled, meets `Tree32.contract`

Written by prove_fn.py from levels.ode and the compiler's layout; not edited by hand, and not to be read
but for its last theorem's statement: Lean checks the rest. The frame: 5424 bytes below the stack pointer at entry
(`fb` is its lowest address), the caller's rbx, rbp, r12, r13, r14 at its top.
-/

namespace Proof_tree32

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option linter.unusedVariables false

theorem whole (ext : Nat → Option (Instr × Nat)) (hA_parents16 : ∀ x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10, Abi.Meets (Code_tree32.prog ext) 0x18000 (P16.contract x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10)) (fb res cvs key flags ra : BitVec 64) (sv : Abi.Saved) (k : Blake3.CV) (l : List Blake3.CV) (m0 : Mem)
    (s : State) (hP : Abi.Pre 0x120000 (Abi.Contract.framed (Tree32.contract res cvs key flags k l) 5424#64) fb ra sv m0 s) : ∃ n_ s', steps (Code_tree32.prog ext) n_ s = some s' ∧ Abi.Post (Abi.Contract.framed (Tree32.contract res cvs key flags k l) 5424#64) fb ra sv m0 s' := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r12, r13, r14, r15, zf, cf, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, mem, pc⟩ := s
  obtain ⟨hpc, hsp, hargs, hbx, hbp, h12, h13, h14, h15, hmem, hF, hRa, hAp, hAcc, hReq⟩ := hP
  simp only [Tree32.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true] at hpc hsp hargs hbx hbp h12 h13 h14 h15 hmem hF hRa
  simp only [List.length_cons, List.length_nil, List.take, List.cons.injEq, and_true] at hargs
  obtain ⟨ha0, ha1, ha2, ha3⟩ := hargs
  subst pc rsp rdi rsi rdx rcx rbx rbp r12 r13 r14 r15 mem
  have hAp0 := hAp
  simp only [Tree32.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, Abi.AllApart, Abi.Apart, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, BitVec.reduceAdd] at hAp
  split_ands hAp
  have hAcc0 := hAcc
  try (simp only [Tree32.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true] at hAcc; split_ands hAcc)
  have hReq0 := hReq
  simp only [Tree32.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true] at hReq
  split_ands hReq
  have_by hE0 := Tree32.len (m := m0)
  try norm_addr at hE0
  split_ands hE0
  refine runs_then (a := 18) (s1 := ?_) ?_ ?_
  case refine_2 => run_fn []; rfl
  refine Abi.call_meets (c := Fillp.contract (fb + 4104#64) cvs 16#64 64#64) (ra := 1179713#64)
    (Abi.Meets.mono (Code_tree32.has_fillp ext) (Proof_fillp.fillp_meets (fb + 4104#64) cvs 16#64 64#64)) rfl rfl ?_ ?_ ?_ ?_ ?_ ?_
  · dsimp only; mem_fact
  · dsimp only [Fillp.contract]; mem_subregion
  · dsimp only
    simp only [Fillp.contract, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, Abi.AllApart, Abi.Apart, BitVec.reduceAdd]
    try simp only [add_sub_lit, BitVec.add_assoc, BitVec.add_zero, BitVec.reduceAdd, BitVec.reduceSub]
    repeat' (with_reducible apply And.intro)
    all_goals bv_decide
  · simp only [Fillp.contract]
    repeat' (with_reducible apply And.intro)
    all_goals (first | assumption | bv_decide)
  · dsimp only
    simp only [Fillp.contract, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
    repeat' (with_reducible apply And.intro)
    all_goals (first | mem_auto | (apply_frame <;> mem_auto) | (apply_intro <;> first | mem_auto | (apply_frame <;> mem_auto)))
  · intro s1 hpc1 hsp1 hbx1 hbp1 h12_1 h13_1 h14_1 h15_1 hens1 hout1 hown1
    obtain ⟨rax_1, rcx_1, rdx_1, rbx_1, rsp_1, rbp_1, rsi_1, rdi_1, r8_1, r9_1, r12_1, r13_1, r14_1, r15_1, zf_1, cf_1, y1_0, y1_1, y1_2, y1_3, y1_4, y1_5, y1_6, y1_7, y1_8, y1_9, y1_10, y1_11, y1_12, y1_13, y1_14, y1_15, mem1, pc_1⟩ := s1
    dsimp only at hpc1 hsp1 hbx1 hbp1 h12_1 h13_1 h14_1 h15_1 hens1 hout1 hown1
    subst pc_1 rsp_1 rbx_1 rbp_1 r12_1 r13_1 r14_1 r15_1
    simp only [Fillp.contract, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true] at hens1
    split_ands hens1
    simp only [Fillp.contract, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, add_sub_lit, BitVec.add_assoc, BitVec.add_zero, BitVec.reduceAdd, BitVec.reduceSub] at hout1
    have hF1 : Region mem1 fb 5424#64 := hown1 fb 5424#64 (by mem_region)
    have hS1_0 : Quad mem1 (fb + 5424#64) ra := X86.Quad.frame (by mem_fact) (fun x hx => hout1 x (by bv_decide) (by bv_decide))
    have hS1_1 : Quad mem1 (fb + 5416#64) sv.rbx := X86.Quad.frame (by mem_fact) (fun x hx => hout1 x (by bv_decide) (by bv_decide))
    have hS1_2 : Quad mem1 (fb + 5408#64) sv.rbp := X86.Quad.frame (by mem_fact) (fun x hx => hout1 x (by bv_decide) (by bv_decide))
    have hS1_3 : Quad mem1 (fb + 5400#64) sv.r12 := X86.Quad.frame (by mem_fact) (fun x hx => hout1 x (by bv_decide) (by bv_decide))
    have hS1_4 : Quad mem1 (fb + 5392#64) sv.r13 := X86.Quad.frame (by mem_fact) (fun x hx => hout1 x (by bv_decide) (by bv_decide))
    have hS1_5 : Quad mem1 (fb + 5384#64) sv.r14 := X86.Quad.frame (by mem_fact) (fun x hx => hout1 x (by bv_decide) (by bv_decide))
    have hK1_0 : Cv.At mem1 key k := Cv.At.frame (m := m0) (by assumption) (fun x hx => by rw [hout1 x (by bv_decide) (by bv_decide)]; first | rfl | mem_away)
    have hK1_1 : Cvs32.At mem1 cvs l := Cvs32.At.frame (m := m0) (by assumption) (fun x hx => by rw [hout1 x (by bv_decide) (by bv_decide)]; first | rfl | mem_away)
    have hK1_2 : Region mem1 res 512#64 := hown1 _ _ (by mem_region)
    have hOut : (∀ x : BitVec 64, (Abi.Contract.framed (Tree32.contract res cvs key flags k l) 5424#64).stack + 8#64 ≤ x - fb → (∀ r ∈ (Abi.Contract.framed (Tree32.contract res cvs key flags k l) 5424#64).modifies, r.2 ≤ x - r.1) → mem1 x = m0 x) := by
      intro x hx hmod
      have hx' := hx
      have hmod' := hmod
      simp only [Tree32.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, BitVec.reduceAdd] at hx' hmod'
      rw [hout1 x (by bv_decide) (by bv_decide)]
      first | rfl | mem_away
    clear hout1 hown1
    refine runs_then (a := 7) (s1 := ?_) ?_ ?_
    case refine_2 => run_fn []; rfl
    have_by hN2_0 := Tree32.in1 (m := mem1)
    try norm_addr at hN2_0
    split_ands hN2_0
    refine Abi.call_meets (c := P16.contract (fb + 4104#64) 1#64 key 0#64 (flags ||| 1073741828#64) (fb + 4360#64) k cvs 16#64 flags l) (ra := 1179750#64)
      (hA_parents16 (fb + 4104#64) 1#64 key 0#64 (flags ||| 1073741828#64) (fb + 4360#64) k cvs 16#64 flags l) rfl rfl ?_ ?_ ?_ ?_ ?_ ?_
    · dsimp only; mem_fact
    · dsimp only [P16.contract]; mem_subregion
    · dsimp only
      simp only [P16.contract, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, Abi.AllApart, Abi.Apart, BitVec.reduceAdd]
      try simp only [add_sub_lit, BitVec.add_assoc, BitVec.add_zero, BitVec.reduceAdd, BitVec.reduceSub]
      repeat' (with_reducible apply And.intro)
      all_goals bv_decide
    · simp only [P16.contract]
      repeat' (with_reducible apply And.intro)
      all_goals (first | assumption | bv_decide)
    · dsimp only
      simp only [P16.contract, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
      repeat' (with_reducible apply And.intro)
      all_goals (first | mem_auto | (apply_frame <;> mem_auto) | (apply_intro <;> first | mem_auto | (apply_frame <;> mem_auto)))
    · intro s2 hpc2 hsp2 hbx2 hbp2 h12_2 h13_2 h14_2 h15_2 hens2 hout2 hown2
      obtain ⟨rax_2, rcx_2, rdx_2, rbx_2, rsp_2, rbp_2, rsi_2, rdi_2, r8_2, r9_2, r12_2, r13_2, r14_2, r15_2, zf_2, cf_2, y2_0, y2_1, y2_2, y2_3, y2_4, y2_5, y2_6, y2_7, y2_8, y2_9, y2_10, y2_11, y2_12, y2_13, y2_14, y2_15, mem2, pc_2⟩ := s2
      dsimp only at hpc2 hsp2 hbx2 hbp2 h12_2 h13_2 h14_2 h15_2 hens2 hout2 hown2
      subst pc_2 rsp_2 rbx_2 rbp_2 r12_2 r13_2 r14_2 r15_2
      simp only [P16.contract, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true] at hens2
      split_ands hens2
      simp only [P16.contract, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, add_sub_lit, BitVec.add_assoc, BitVec.add_zero, BitVec.reduceAdd, BitVec.reduceSub] at hout2
      have hF2 : Region mem2 fb 5424#64 := hown2 fb 5424#64 (by mem_region)
      have hS2_0 : Quad mem2 (fb + 5424#64) ra := X86.Quad.frame (by mem_fact) (fun x hx => hout2 x (by bv_decide) (by bv_decide))
      have hS2_1 : Quad mem2 (fb + 5416#64) sv.rbx := X86.Quad.frame (by mem_fact) (fun x hx => hout2 x (by bv_decide) (by bv_decide))
      have hS2_2 : Quad mem2 (fb + 5408#64) sv.rbp := X86.Quad.frame (by mem_fact) (fun x hx => hout2 x (by bv_decide) (by bv_decide))
      have hS2_3 : Quad mem2 (fb + 5400#64) sv.r12 := X86.Quad.frame (by mem_fact) (fun x hx => hout2 x (by bv_decide) (by bv_decide))
      have hS2_4 : Quad mem2 (fb + 5392#64) sv.r13 := X86.Quad.frame (by mem_fact) (fun x hx => hout2 x (by bv_decide) (by bv_decide))
      have hS2_5 : Quad mem2 (fb + 5384#64) sv.r14 := X86.Quad.frame (by mem_fact) (fun x hx => hout2 x (by bv_decide) (by bv_decide))
      have hK2_0 : Cv.At mem2 key k := Cv.At.frame (m := mem1) (by assumption) (fun x hx => by rw [hout2 x (by bv_decide) (by bv_decide)]; first | rfl | mem_away)
      have hK2_1 : Region mem2 res 512#64 := hown2 _ _ (by mem_region)
      have hOut : (∀ x : BitVec 64, (Abi.Contract.framed (Tree32.contract res cvs key flags k l) 5424#64).stack + 8#64 ≤ x - fb → (∀ r ∈ (Abi.Contract.framed (Tree32.contract res cvs key flags k l) 5424#64).modifies, r.2 ≤ x - r.1) → mem2 x = m0 x) := by
        intro x hx hmod
        have hx' := hx
        have hmod' := hmod
        simp only [Tree32.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, BitVec.reduceAdd] at hx' hmod'
        rw [hout2 x (by bv_decide) (by bv_decide)]
        refine Eq.trans ?_ (hOut x hx hmod); first | rfl | mem_away
      clear hout2 hown2
      refine runs_then (a := 5) (s1 := ?_) ?_ ?_
      case refine_2 => run_fn []; rfl
      refine Abi.call_meets (c := Fillp.contract (fb + 4104#64) (fb + 4360#64) 8#64 64#64) (ra := 1179781#64)
        (Abi.Meets.mono (Code_tree32.has_fillp ext) (Proof_fillp.fillp_meets (fb + 4104#64) (fb + 4360#64) 8#64 64#64)) rfl rfl ?_ ?_ ?_ ?_ ?_ ?_
      · dsimp only; mem_fact
      · dsimp only [Fillp.contract]; mem_subregion
      · dsimp only
        simp only [Fillp.contract, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, Abi.AllApart, Abi.Apart, BitVec.reduceAdd]
        try simp only [add_sub_lit, BitVec.add_assoc, BitVec.add_zero, BitVec.reduceAdd, BitVec.reduceSub]
        repeat' (with_reducible apply And.intro)
        all_goals bv_decide
      · simp only [Fillp.contract]
        repeat' (with_reducible apply And.intro)
        all_goals (first | assumption | bv_decide)
      · dsimp only
        simp only [Fillp.contract, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
        repeat' (with_reducible apply And.intro)
        all_goals (first | mem_auto | (apply_frame <;> mem_auto) | (apply_intro <;> first | mem_auto | (apply_frame <;> mem_auto)))
      · intro s3 hpc3 hsp3 hbx3 hbp3 h12_3 h13_3 h14_3 h15_3 hens3 hout3 hown3
        obtain ⟨rax_3, rcx_3, rdx_3, rbx_3, rsp_3, rbp_3, rsi_3, rdi_3, r8_3, r9_3, r12_3, r13_3, r14_3, r15_3, zf_3, cf_3, y3_0, y3_1, y3_2, y3_3, y3_4, y3_5, y3_6, y3_7, y3_8, y3_9, y3_10, y3_11, y3_12, y3_13, y3_14, y3_15, mem3, pc_3⟩ := s3
        dsimp only at hpc3 hsp3 hbx3 hbp3 h12_3 h13_3 h14_3 h15_3 hens3 hout3 hown3
        subst pc_3 rsp_3 rbx_3 rbp_3 r12_3 r13_3 r14_3 r15_3
        simp only [Fillp.contract, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true] at hens3
        split_ands hens3
        simp only [Fillp.contract, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, add_sub_lit, BitVec.add_assoc, BitVec.add_zero, BitVec.reduceAdd, BitVec.reduceSub] at hout3
        have hF3 : Region mem3 fb 5424#64 := hown3 fb 5424#64 (by mem_region)
        have hS3_0 : Quad mem3 (fb + 5424#64) ra := X86.Quad.frame (by mem_fact) (fun x hx => hout3 x (by bv_decide) (by bv_decide))
        have hS3_1 : Quad mem3 (fb + 5416#64) sv.rbx := X86.Quad.frame (by mem_fact) (fun x hx => hout3 x (by bv_decide) (by bv_decide))
        have hS3_2 : Quad mem3 (fb + 5408#64) sv.rbp := X86.Quad.frame (by mem_fact) (fun x hx => hout3 x (by bv_decide) (by bv_decide))
        have hS3_3 : Quad mem3 (fb + 5400#64) sv.r12 := X86.Quad.frame (by mem_fact) (fun x hx => hout3 x (by bv_decide) (by bv_decide))
        have hS3_4 : Quad mem3 (fb + 5392#64) sv.r13 := X86.Quad.frame (by mem_fact) (fun x hx => hout3 x (by bv_decide) (by bv_decide))
        have hS3_5 : Quad mem3 (fb + 5384#64) sv.r14 := X86.Quad.frame (by mem_fact) (fun x hx => hout3 x (by bv_decide) (by bv_decide))
        have hK3_0 : Cv.At mem3 key k := Cv.At.frame (m := mem2) (by assumption) (fun x hx => by rw [hout3 x (by bv_decide) (by bv_decide)]; first | rfl | mem_away)
        have hK3_1 : Cvs16.At mem3 (fb + 4360#64) (Tree32.l1 k flags l) := Cvs16.At.frame (m := mem2) (by assumption) (fun x hx => by rw [hout3 x (by bv_decide) (by bv_decide)]; first | rfl | mem_away)
        have hK3_2 : Region mem3 res 512#64 := hown3 _ _ (by mem_region)
        have hOut : (∀ x : BitVec 64, (Abi.Contract.framed (Tree32.contract res cvs key flags k l) 5424#64).stack + 8#64 ≤ x - fb → (∀ r ∈ (Abi.Contract.framed (Tree32.contract res cvs key flags k l) 5424#64).modifies, r.2 ≤ x - r.1) → mem3 x = m0 x) := by
          intro x hx hmod
          have hx' := hx
          have hmod' := hmod
          simp only [Tree32.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, BitVec.reduceAdd] at hx' hmod'
          rw [hout3 x (by bv_decide) (by bv_decide)]
          refine Eq.trans ?_ (hOut x hx hmod); first | rfl | mem_away
        clear hout3 hown3
        refine runs_then (a := 7) (s1 := ?_) ?_ ?_
        case refine_2 => run_fn []; rfl
        have_by hN4_0 := Tree32.in2 (m := mem3)
        try norm_addr at hN4_0
        split_ands hN4_0
        refine Abi.call_meets (c := P16.contract (fb + 4104#64) 1#64 key 0#64 (flags ||| 1073741828#64) (fb + 4872#64) k (fb + 4360#64) 8#64 flags (Tree32.l1 k flags l)) (ra := 1179818#64)
          (hA_parents16 (fb + 4104#64) 1#64 key 0#64 (flags ||| 1073741828#64) (fb + 4872#64) k (fb + 4360#64) 8#64 flags (Tree32.l1 k flags l)) rfl rfl ?_ ?_ ?_ ?_ ?_ ?_
        · dsimp only; mem_fact
        · dsimp only [P16.contract]; mem_subregion
        · dsimp only
          simp only [P16.contract, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, Abi.AllApart, Abi.Apart, BitVec.reduceAdd]
          try simp only [add_sub_lit, BitVec.add_assoc, BitVec.add_zero, BitVec.reduceAdd, BitVec.reduceSub]
          repeat' (with_reducible apply And.intro)
          all_goals bv_decide
        · simp only [P16.contract]
          repeat' (with_reducible apply And.intro)
          all_goals (first | assumption | bv_decide)
        · dsimp only
          simp only [P16.contract, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
          repeat' (with_reducible apply And.intro)
          all_goals (first | mem_auto | (apply_frame <;> mem_auto) | (apply_intro <;> first | mem_auto | (apply_frame <;> mem_auto)))
        · intro s4 hpc4 hsp4 hbx4 hbp4 h12_4 h13_4 h14_4 h15_4 hens4 hout4 hown4
          obtain ⟨rax_4, rcx_4, rdx_4, rbx_4, rsp_4, rbp_4, rsi_4, rdi_4, r8_4, r9_4, r12_4, r13_4, r14_4, r15_4, zf_4, cf_4, y4_0, y4_1, y4_2, y4_3, y4_4, y4_5, y4_6, y4_7, y4_8, y4_9, y4_10, y4_11, y4_12, y4_13, y4_14, y4_15, mem4, pc_4⟩ := s4
          dsimp only at hpc4 hsp4 hbx4 hbp4 h12_4 h13_4 h14_4 h15_4 hens4 hout4 hown4
          subst pc_4 rsp_4 rbx_4 rbp_4 r12_4 r13_4 r14_4 r15_4
          simp only [P16.contract, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true] at hens4
          split_ands hens4
          simp only [P16.contract, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, add_sub_lit, BitVec.add_assoc, BitVec.add_zero, BitVec.reduceAdd, BitVec.reduceSub] at hout4
          have hF4 : Region mem4 fb 5424#64 := hown4 fb 5424#64 (by mem_region)
          have hS4_0 : Quad mem4 (fb + 5424#64) ra := X86.Quad.frame (by mem_fact) (fun x hx => hout4 x (by bv_decide) (by bv_decide))
          have hS4_1 : Quad mem4 (fb + 5416#64) sv.rbx := X86.Quad.frame (by mem_fact) (fun x hx => hout4 x (by bv_decide) (by bv_decide))
          have hS4_2 : Quad mem4 (fb + 5408#64) sv.rbp := X86.Quad.frame (by mem_fact) (fun x hx => hout4 x (by bv_decide) (by bv_decide))
          have hS4_3 : Quad mem4 (fb + 5400#64) sv.r12 := X86.Quad.frame (by mem_fact) (fun x hx => hout4 x (by bv_decide) (by bv_decide))
          have hS4_4 : Quad mem4 (fb + 5392#64) sv.r13 := X86.Quad.frame (by mem_fact) (fun x hx => hout4 x (by bv_decide) (by bv_decide))
          have hS4_5 : Quad mem4 (fb + 5384#64) sv.r14 := X86.Quad.frame (by mem_fact) (fun x hx => hout4 x (by bv_decide) (by bv_decide))
          have hK4_0 : Cv.At mem4 key k := Cv.At.frame (m := mem3) (by assumption) (fun x hx => by rw [hout4 x (by bv_decide) (by bv_decide)]; first | rfl | mem_away)
          have hK4_1 : Region mem4 res 512#64 := hown4 _ _ (by mem_region)
          have hOut : (∀ x : BitVec 64, (Abi.Contract.framed (Tree32.contract res cvs key flags k l) 5424#64).stack + 8#64 ≤ x - fb → (∀ r ∈ (Abi.Contract.framed (Tree32.contract res cvs key flags k l) 5424#64).modifies, r.2 ≤ x - r.1) → mem4 x = m0 x) := by
            intro x hx hmod
            have hx' := hx
            have hmod' := hmod
            simp only [Tree32.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, BitVec.reduceAdd] at hx' hmod'
            rw [hout4 x (by bv_decide) (by bv_decide)]
            refine Eq.trans ?_ (hOut x hx hmod); first | rfl | mem_away
          clear hout4 hown4
          refine runs_then (a := 5) (s1 := ?_) ?_ ?_
          case refine_2 => run_fn []; rfl
          refine Abi.call_meets (c := Fillp.contract (fb + 4104#64) (fb + 4872#64) 4#64 64#64) (ra := 1179849#64)
            (Abi.Meets.mono (Code_tree32.has_fillp ext) (Proof_fillp.fillp_meets (fb + 4104#64) (fb + 4872#64) 4#64 64#64)) rfl rfl ?_ ?_ ?_ ?_ ?_ ?_
          · dsimp only; mem_fact
          · dsimp only [Fillp.contract]; mem_subregion
          · dsimp only
            simp only [Fillp.contract, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, Abi.AllApart, Abi.Apart, BitVec.reduceAdd]
            try simp only [add_sub_lit, BitVec.add_assoc, BitVec.add_zero, BitVec.reduceAdd, BitVec.reduceSub]
            repeat' (with_reducible apply And.intro)
            all_goals bv_decide
          · simp only [Fillp.contract]
            repeat' (with_reducible apply And.intro)
            all_goals (first | assumption | bv_decide)
          · dsimp only
            simp only [Fillp.contract, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
            repeat' (with_reducible apply And.intro)
            all_goals (first | mem_auto | (apply_frame <;> mem_auto) | (apply_intro <;> first | mem_auto | (apply_frame <;> mem_auto)))
          · intro s5 hpc5 hsp5 hbx5 hbp5 h12_5 h13_5 h14_5 h15_5 hens5 hout5 hown5
            obtain ⟨rax_5, rcx_5, rdx_5, rbx_5, rsp_5, rbp_5, rsi_5, rdi_5, r8_5, r9_5, r12_5, r13_5, r14_5, r15_5, zf_5, cf_5, y5_0, y5_1, y5_2, y5_3, y5_4, y5_5, y5_6, y5_7, y5_8, y5_9, y5_10, y5_11, y5_12, y5_13, y5_14, y5_15, mem5, pc_5⟩ := s5
            dsimp only at hpc5 hsp5 hbx5 hbp5 h12_5 h13_5 h14_5 h15_5 hens5 hout5 hown5
            subst pc_5 rsp_5 rbx_5 rbp_5 r12_5 r13_5 r14_5 r15_5
            simp only [Fillp.contract, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true] at hens5
            split_ands hens5
            simp only [Fillp.contract, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, add_sub_lit, BitVec.add_assoc, BitVec.add_zero, BitVec.reduceAdd, BitVec.reduceSub] at hout5
            have hF5 : Region mem5 fb 5424#64 := hown5 fb 5424#64 (by mem_region)
            have hS5_0 : Quad mem5 (fb + 5424#64) ra := X86.Quad.frame (by mem_fact) (fun x hx => hout5 x (by bv_decide) (by bv_decide))
            have hS5_1 : Quad mem5 (fb + 5416#64) sv.rbx := X86.Quad.frame (by mem_fact) (fun x hx => hout5 x (by bv_decide) (by bv_decide))
            have hS5_2 : Quad mem5 (fb + 5408#64) sv.rbp := X86.Quad.frame (by mem_fact) (fun x hx => hout5 x (by bv_decide) (by bv_decide))
            have hS5_3 : Quad mem5 (fb + 5400#64) sv.r12 := X86.Quad.frame (by mem_fact) (fun x hx => hout5 x (by bv_decide) (by bv_decide))
            have hS5_4 : Quad mem5 (fb + 5392#64) sv.r13 := X86.Quad.frame (by mem_fact) (fun x hx => hout5 x (by bv_decide) (by bv_decide))
            have hS5_5 : Quad mem5 (fb + 5384#64) sv.r14 := X86.Quad.frame (by mem_fact) (fun x hx => hout5 x (by bv_decide) (by bv_decide))
            have hK5_0 : Cv.At mem5 key k := Cv.At.frame (m := mem4) (by assumption) (fun x hx => by rw [hout5 x (by bv_decide) (by bv_decide)]; first | rfl | mem_away)
            have hK5_1 : Cvs16.At mem5 (fb + 4872#64) (Tree32.l2 k flags l) := Cvs16.At.frame (m := mem4) (by assumption) (fun x hx => by rw [hout5 x (by bv_decide) (by bv_decide)]; first | rfl | mem_away)
            have hK5_2 : Region mem5 res 512#64 := hown5 _ _ (by mem_region)
            have hOut : (∀ x : BitVec 64, (Abi.Contract.framed (Tree32.contract res cvs key flags k l) 5424#64).stack + 8#64 ≤ x - fb → (∀ r ∈ (Abi.Contract.framed (Tree32.contract res cvs key flags k l) 5424#64).modifies, r.2 ≤ x - r.1) → mem5 x = m0 x) := by
              intro x hx hmod
              have hx' := hx
              have hmod' := hmod
              simp only [Tree32.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, BitVec.reduceAdd] at hx' hmod'
              rw [hout5 x (by bv_decide) (by bv_decide)]
              refine Eq.trans ?_ (hOut x hx hmod); first | rfl | mem_away
            clear hout5 hown5
            refine runs_then (a := 7) (s1 := ?_) ?_ ?_
            case refine_2 => run_fn []; rfl
            have_by hN6_0 := Tree32.in3 (m := mem5)
            try norm_addr at hN6_0
            split_ands hN6_0
            refine Abi.call_meets (c := P16.contract (fb + 4104#64) 1#64 key 0#64 (flags ||| 1073741828#64) (fb + 4360#64) k (fb + 4872#64) 4#64 flags ((Tree32.l2 k flags l).take 8)) (ra := 1179886#64)
              (hA_parents16 (fb + 4104#64) 1#64 key 0#64 (flags ||| 1073741828#64) (fb + 4360#64) k (fb + 4872#64) 4#64 flags ((Tree32.l2 k flags l).take 8)) rfl rfl ?_ ?_ ?_ ?_ ?_ ?_
            · dsimp only; mem_fact
            · dsimp only [P16.contract]; mem_subregion
            · dsimp only
              simp only [P16.contract, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, Abi.AllApart, Abi.Apart, BitVec.reduceAdd]
              try simp only [add_sub_lit, BitVec.add_assoc, BitVec.add_zero, BitVec.reduceAdd, BitVec.reduceSub]
              repeat' (with_reducible apply And.intro)
              all_goals bv_decide
            · simp only [P16.contract]
              repeat' (with_reducible apply And.intro)
              all_goals (first | assumption | bv_decide)
            · dsimp only
              simp only [P16.contract, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
              repeat' (with_reducible apply And.intro)
              all_goals (first | mem_auto | (apply_frame <;> mem_auto) | (apply_intro <;> first | mem_auto | (apply_frame <;> mem_auto)))
            · intro s6 hpc6 hsp6 hbx6 hbp6 h12_6 h13_6 h14_6 h15_6 hens6 hout6 hown6
              obtain ⟨rax_6, rcx_6, rdx_6, rbx_6, rsp_6, rbp_6, rsi_6, rdi_6, r8_6, r9_6, r12_6, r13_6, r14_6, r15_6, zf_6, cf_6, y6_0, y6_1, y6_2, y6_3, y6_4, y6_5, y6_6, y6_7, y6_8, y6_9, y6_10, y6_11, y6_12, y6_13, y6_14, y6_15, mem6, pc_6⟩ := s6
              dsimp only at hpc6 hsp6 hbx6 hbp6 h12_6 h13_6 h14_6 h15_6 hens6 hout6 hown6
              subst pc_6 rsp_6 rbx_6 rbp_6 r12_6 r13_6 r14_6 r15_6
              simp only [P16.contract, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true] at hens6
              split_ands hens6
              simp only [P16.contract, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, add_sub_lit, BitVec.add_assoc, BitVec.add_zero, BitVec.reduceAdd, BitVec.reduceSub] at hout6
              have hF6 : Region mem6 fb 5424#64 := hown6 fb 5424#64 (by mem_region)
              have hS6_0 : Quad mem6 (fb + 5424#64) ra := X86.Quad.frame (by mem_fact) (fun x hx => hout6 x (by bv_decide) (by bv_decide))
              have hS6_1 : Quad mem6 (fb + 5416#64) sv.rbx := X86.Quad.frame (by mem_fact) (fun x hx => hout6 x (by bv_decide) (by bv_decide))
              have hS6_2 : Quad mem6 (fb + 5408#64) sv.rbp := X86.Quad.frame (by mem_fact) (fun x hx => hout6 x (by bv_decide) (by bv_decide))
              have hS6_3 : Quad mem6 (fb + 5400#64) sv.r12 := X86.Quad.frame (by mem_fact) (fun x hx => hout6 x (by bv_decide) (by bv_decide))
              have hS6_4 : Quad mem6 (fb + 5392#64) sv.r13 := X86.Quad.frame (by mem_fact) (fun x hx => hout6 x (by bv_decide) (by bv_decide))
              have hS6_5 : Quad mem6 (fb + 5384#64) sv.r14 := X86.Quad.frame (by mem_fact) (fun x hx => hout6 x (by bv_decide) (by bv_decide))
              have hK6_0 : Cv.At mem6 key k := Cv.At.frame (m := mem5) (by assumption) (fun x hx => by rw [hout6 x (by bv_decide) (by bv_decide)]; first | rfl | mem_away)
              have hK6_1 : Region mem6 res 512#64 := hown6 _ _ (by mem_region)
              have hOut : (∀ x : BitVec 64, (Abi.Contract.framed (Tree32.contract res cvs key flags k l) 5424#64).stack + 8#64 ≤ x - fb → (∀ r ∈ (Abi.Contract.framed (Tree32.contract res cvs key flags k l) 5424#64).modifies, r.2 ≤ x - r.1) → mem6 x = m0 x) := by
                intro x hx hmod
                have hx' := hx
                have hmod' := hmod
                simp only [Tree32.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, BitVec.reduceAdd] at hx' hmod'
                rw [hout6 x (by bv_decide) (by bv_decide)]
                refine Eq.trans ?_ (hOut x hx hmod); first | rfl | mem_away
              clear hout6 hown6
              refine runs_then (a := 5) (s1 := ?_) ?_ ?_
              case refine_2 => run_fn []; rfl
              refine Abi.call_meets (c := Fillp.contract (fb + 4104#64) (fb + 4360#64) 2#64 64#64) (ra := 1179917#64)
                (Abi.Meets.mono (Code_tree32.has_fillp ext) (Proof_fillp.fillp_meets (fb + 4104#64) (fb + 4360#64) 2#64 64#64)) rfl rfl ?_ ?_ ?_ ?_ ?_ ?_
              · dsimp only; mem_fact
              · dsimp only [Fillp.contract]; mem_subregion
              · dsimp only
                simp only [Fillp.contract, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, Abi.AllApart, Abi.Apart, BitVec.reduceAdd]
                try simp only [add_sub_lit, BitVec.add_assoc, BitVec.add_zero, BitVec.reduceAdd, BitVec.reduceSub]
                repeat' (with_reducible apply And.intro)
                all_goals bv_decide
              · simp only [Fillp.contract]
                repeat' (with_reducible apply And.intro)
                all_goals (first | assumption | bv_decide)
              · dsimp only
                simp only [Fillp.contract, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
                repeat' (with_reducible apply And.intro)
                all_goals (first | mem_auto | (apply_frame <;> mem_auto) | (apply_intro <;> first | mem_auto | (apply_frame <;> mem_auto)))
              · intro s7 hpc7 hsp7 hbx7 hbp7 h12_7 h13_7 h14_7 h15_7 hens7 hout7 hown7
                obtain ⟨rax_7, rcx_7, rdx_7, rbx_7, rsp_7, rbp_7, rsi_7, rdi_7, r8_7, r9_7, r12_7, r13_7, r14_7, r15_7, zf_7, cf_7, y7_0, y7_1, y7_2, y7_3, y7_4, y7_5, y7_6, y7_7, y7_8, y7_9, y7_10, y7_11, y7_12, y7_13, y7_14, y7_15, mem7, pc_7⟩ := s7
                dsimp only at hpc7 hsp7 hbx7 hbp7 h12_7 h13_7 h14_7 h15_7 hens7 hout7 hown7
                subst pc_7 rsp_7 rbx_7 rbp_7 r12_7 r13_7 r14_7 r15_7
                simp only [Fillp.contract, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true] at hens7
                split_ands hens7
                simp only [Fillp.contract, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, add_sub_lit, BitVec.add_assoc, BitVec.add_zero, BitVec.reduceAdd, BitVec.reduceSub] at hout7
                have hF7 : Region mem7 fb 5424#64 := hown7 fb 5424#64 (by mem_region)
                have hS7_0 : Quad mem7 (fb + 5424#64) ra := X86.Quad.frame (by mem_fact) (fun x hx => hout7 x (by bv_decide) (by bv_decide))
                have hS7_1 : Quad mem7 (fb + 5416#64) sv.rbx := X86.Quad.frame (by mem_fact) (fun x hx => hout7 x (by bv_decide) (by bv_decide))
                have hS7_2 : Quad mem7 (fb + 5408#64) sv.rbp := X86.Quad.frame (by mem_fact) (fun x hx => hout7 x (by bv_decide) (by bv_decide))
                have hS7_3 : Quad mem7 (fb + 5400#64) sv.r12 := X86.Quad.frame (by mem_fact) (fun x hx => hout7 x (by bv_decide) (by bv_decide))
                have hS7_4 : Quad mem7 (fb + 5392#64) sv.r13 := X86.Quad.frame (by mem_fact) (fun x hx => hout7 x (by bv_decide) (by bv_decide))
                have hS7_5 : Quad mem7 (fb + 5384#64) sv.r14 := X86.Quad.frame (by mem_fact) (fun x hx => hout7 x (by bv_decide) (by bv_decide))
                have hK7_0 : Cv.At mem7 key k := Cv.At.frame (m := mem6) (by assumption) (fun x hx => by rw [hout7 x (by bv_decide) (by bv_decide)]; first | rfl | mem_away)
                have hK7_1 : Cvs16.At mem7 (fb + 4360#64) (Tree32.l3 k flags l) := Cvs16.At.frame (m := mem6) (by assumption) (fun x hx => by rw [hout7 x (by bv_decide) (by bv_decide)]; first | rfl | mem_away)
                have hK7_2 : Region mem7 res 512#64 := hown7 _ _ (by mem_region)
                have hOut : (∀ x : BitVec 64, (Abi.Contract.framed (Tree32.contract res cvs key flags k l) 5424#64).stack + 8#64 ≤ x - fb → (∀ r ∈ (Abi.Contract.framed (Tree32.contract res cvs key flags k l) 5424#64).modifies, r.2 ≤ x - r.1) → mem7 x = m0 x) := by
                  intro x hx hmod
                  have hx' := hx
                  have hmod' := hmod
                  simp only [Tree32.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, BitVec.reduceAdd] at hx' hmod'
                  rw [hout7 x (by bv_decide) (by bv_decide)]
                  refine Eq.trans ?_ (hOut x hx hmod); first | rfl | mem_away
                clear hout7 hown7
                refine runs_then (a := 7) (s1 := ?_) ?_ ?_
                case refine_2 => run_fn []; rfl
                have_by hN8_0 := Tree32.in4 (m := mem7)
                try norm_addr at hN8_0
                split_ands hN8_0
                refine Abi.call_meets (c := P16.contract (fb + 4104#64) 1#64 key 0#64 (flags ||| 1073741828#64) (fb + 4872#64) k (fb + 4360#64) 2#64 flags ((Tree32.l3 k flags l).take 4)) (ra := 1179954#64)
                  (hA_parents16 (fb + 4104#64) 1#64 key 0#64 (flags ||| 1073741828#64) (fb + 4872#64) k (fb + 4360#64) 2#64 flags ((Tree32.l3 k flags l).take 4)) rfl rfl ?_ ?_ ?_ ?_ ?_ ?_
                · dsimp only; mem_fact
                · dsimp only [P16.contract]; mem_subregion
                · dsimp only
                  simp only [P16.contract, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, Abi.AllApart, Abi.Apart, BitVec.reduceAdd]
                  try simp only [add_sub_lit, BitVec.add_assoc, BitVec.add_zero, BitVec.reduceAdd, BitVec.reduceSub]
                  repeat' (with_reducible apply And.intro)
                  all_goals bv_decide
                · simp only [P16.contract]
                  repeat' (with_reducible apply And.intro)
                  all_goals (first | assumption | bv_decide)
                · dsimp only
                  simp only [P16.contract, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
                  repeat' (with_reducible apply And.intro)
                  all_goals (first | mem_auto | (apply_frame <;> mem_auto) | (apply_intro <;> first | mem_auto | (apply_frame <;> mem_auto)))
                · intro s8 hpc8 hsp8 hbx8 hbp8 h12_8 h13_8 h14_8 h15_8 hens8 hout8 hown8
                  obtain ⟨rax_8, rcx_8, rdx_8, rbx_8, rsp_8, rbp_8, rsi_8, rdi_8, r8_8, r9_8, r12_8, r13_8, r14_8, r15_8, zf_8, cf_8, y8_0, y8_1, y8_2, y8_3, y8_4, y8_5, y8_6, y8_7, y8_8, y8_9, y8_10, y8_11, y8_12, y8_13, y8_14, y8_15, mem8, pc_8⟩ := s8
                  dsimp only at hpc8 hsp8 hbx8 hbp8 h12_8 h13_8 h14_8 h15_8 hens8 hout8 hown8
                  subst pc_8 rsp_8 rbx_8 rbp_8 r12_8 r13_8 r14_8 r15_8
                  simp only [P16.contract, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true] at hens8
                  split_ands hens8
                  simp only [P16.contract, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, add_sub_lit, BitVec.add_assoc, BitVec.add_zero, BitVec.reduceAdd, BitVec.reduceSub] at hout8
                  have hF8 : Region mem8 fb 5424#64 := hown8 fb 5424#64 (by mem_region)
                  have hS8_0 : Quad mem8 (fb + 5424#64) ra := X86.Quad.frame (by mem_fact) (fun x hx => hout8 x (by bv_decide) (by bv_decide))
                  have hS8_1 : Quad mem8 (fb + 5416#64) sv.rbx := X86.Quad.frame (by mem_fact) (fun x hx => hout8 x (by bv_decide) (by bv_decide))
                  have hS8_2 : Quad mem8 (fb + 5408#64) sv.rbp := X86.Quad.frame (by mem_fact) (fun x hx => hout8 x (by bv_decide) (by bv_decide))
                  have hS8_3 : Quad mem8 (fb + 5400#64) sv.r12 := X86.Quad.frame (by mem_fact) (fun x hx => hout8 x (by bv_decide) (by bv_decide))
                  have hS8_4 : Quad mem8 (fb + 5392#64) sv.r13 := X86.Quad.frame (by mem_fact) (fun x hx => hout8 x (by bv_decide) (by bv_decide))
                  have hS8_5 : Quad mem8 (fb + 5384#64) sv.r14 := X86.Quad.frame (by mem_fact) (fun x hx => hout8 x (by bv_decide) (by bv_decide))
                  have hK8_0 : Cv.At mem8 key k := Cv.At.frame (m := mem7) (by assumption) (fun x hx => by rw [hout8 x (by bv_decide) (by bv_decide)]; first | rfl | mem_away)
                  have hK8_1 : Region mem8 res 512#64 := hown8 _ _ (by mem_region)
                  have hOut : (∀ x : BitVec 64, (Abi.Contract.framed (Tree32.contract res cvs key flags k l) 5424#64).stack + 8#64 ≤ x - fb → (∀ r ∈ (Abi.Contract.framed (Tree32.contract res cvs key flags k l) 5424#64).modifies, r.2 ≤ x - r.1) → mem8 x = m0 x) := by
                    intro x hx hmod
                    have hx' := hx
                    have hmod' := hmod
                    simp only [Tree32.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, BitVec.reduceAdd] at hx' hmod'
                    rw [hout8 x (by bv_decide) (by bv_decide)]
                    refine Eq.trans ?_ (hOut x hx hmod); first | rfl | mem_away
                  clear hout8 hown8
                  refine runs_then (a := 5) (s1 := ?_) ?_ ?_
                  case refine_2 => run_fn []; rfl
                  refine Abi.call_meets (c := Fillp.contract (fb + 4104#64) (fb + 4872#64) 1#64 64#64) (ra := 1179985#64)
                    (Abi.Meets.mono (Code_tree32.has_fillp ext) (Proof_fillp.fillp_meets (fb + 4104#64) (fb + 4872#64) 1#64 64#64)) rfl rfl ?_ ?_ ?_ ?_ ?_ ?_
                  · dsimp only; mem_fact
                  · dsimp only [Fillp.contract]; mem_subregion
                  · dsimp only
                    simp only [Fillp.contract, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, Abi.AllApart, Abi.Apart, BitVec.reduceAdd]
                    try simp only [add_sub_lit, BitVec.add_assoc, BitVec.add_zero, BitVec.reduceAdd, BitVec.reduceSub]
                    repeat' (with_reducible apply And.intro)
                    all_goals bv_decide
                  · simp only [Fillp.contract]
                    repeat' (with_reducible apply And.intro)
                    all_goals (first | assumption | bv_decide)
                  · dsimp only
                    simp only [Fillp.contract, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
                    repeat' (with_reducible apply And.intro)
                    all_goals (first | mem_auto | (apply_frame <;> mem_auto) | (apply_intro <;> first | mem_auto | (apply_frame <;> mem_auto)))
                  · intro s9 hpc9 hsp9 hbx9 hbp9 h12_9 h13_9 h14_9 h15_9 hens9 hout9 hown9
                    obtain ⟨rax_9, rcx_9, rdx_9, rbx_9, rsp_9, rbp_9, rsi_9, rdi_9, r8_9, r9_9, r12_9, r13_9, r14_9, r15_9, zf_9, cf_9, y9_0, y9_1, y9_2, y9_3, y9_4, y9_5, y9_6, y9_7, y9_8, y9_9, y9_10, y9_11, y9_12, y9_13, y9_14, y9_15, mem9, pc_9⟩ := s9
                    dsimp only at hpc9 hsp9 hbx9 hbp9 h12_9 h13_9 h14_9 h15_9 hens9 hout9 hown9
                    subst pc_9 rsp_9 rbx_9 rbp_9 r12_9 r13_9 r14_9 r15_9
                    simp only [Fillp.contract, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true] at hens9
                    split_ands hens9
                    simp only [Fillp.contract, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, add_sub_lit, BitVec.add_assoc, BitVec.add_zero, BitVec.reduceAdd, BitVec.reduceSub] at hout9
                    have hF9 : Region mem9 fb 5424#64 := hown9 fb 5424#64 (by mem_region)
                    have hS9_0 : Quad mem9 (fb + 5424#64) ra := X86.Quad.frame (by mem_fact) (fun x hx => hout9 x (by bv_decide) (by bv_decide))
                    have hS9_1 : Quad mem9 (fb + 5416#64) sv.rbx := X86.Quad.frame (by mem_fact) (fun x hx => hout9 x (by bv_decide) (by bv_decide))
                    have hS9_2 : Quad mem9 (fb + 5408#64) sv.rbp := X86.Quad.frame (by mem_fact) (fun x hx => hout9 x (by bv_decide) (by bv_decide))
                    have hS9_3 : Quad mem9 (fb + 5400#64) sv.r12 := X86.Quad.frame (by mem_fact) (fun x hx => hout9 x (by bv_decide) (by bv_decide))
                    have hS9_4 : Quad mem9 (fb + 5392#64) sv.r13 := X86.Quad.frame (by mem_fact) (fun x hx => hout9 x (by bv_decide) (by bv_decide))
                    have hS9_5 : Quad mem9 (fb + 5384#64) sv.r14 := X86.Quad.frame (by mem_fact) (fun x hx => hout9 x (by bv_decide) (by bv_decide))
                    have hK9_0 : Cv.At mem9 key k := Cv.At.frame (m := mem8) (by assumption) (fun x hx => by rw [hout9 x (by bv_decide) (by bv_decide)]; first | rfl | mem_away)
                    have hK9_1 : Cvs16.At mem9 (fb + 4872#64) (Tree32.l4 k flags l) := Cvs16.At.frame (m := mem8) (by assumption) (fun x hx => by rw [hout9 x (by bv_decide) (by bv_decide)]; first | rfl | mem_away)
                    have hK9_2 : Region mem9 res 512#64 := hown9 _ _ (by mem_region)
                    have hOut : (∀ x : BitVec 64, (Abi.Contract.framed (Tree32.contract res cvs key flags k l) 5424#64).stack + 8#64 ≤ x - fb → (∀ r ∈ (Abi.Contract.framed (Tree32.contract res cvs key flags k l) 5424#64).modifies, r.2 ≤ x - r.1) → mem9 x = m0 x) := by
                      intro x hx hmod
                      have hx' := hx
                      have hmod' := hmod
                      simp only [Tree32.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, BitVec.reduceAdd] at hx' hmod'
                      rw [hout9 x (by bv_decide) (by bv_decide)]
                      refine Eq.trans ?_ (hOut x hx hmod); first | rfl | mem_away
                    clear hout9 hown9
                    refine runs_then (a := 7) (s1 := ?_) ?_ ?_
                    case refine_2 => run_fn []; rfl
                    have_by hN10_0 := Tree32.in5 (m := mem9)
                    try norm_addr at hN10_0
                    split_ands hN10_0
                    refine Abi.call_meets (c := P16.contract (fb + 4104#64) 1#64 key 0#64 (flags ||| 1073741828#64) res k (fb + 4872#64) 1#64 flags ((Tree32.l4 k flags l).take 2)) (ra := 1180017#64)
                      (hA_parents16 (fb + 4104#64) 1#64 key 0#64 (flags ||| 1073741828#64) res k (fb + 4872#64) 1#64 flags ((Tree32.l4 k flags l).take 2)) rfl rfl ?_ ?_ ?_ ?_ ?_ ?_
                    · dsimp only; mem_fact
                    · dsimp only [P16.contract]; mem_subregion
                    · dsimp only
                      simp only [P16.contract, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, Abi.AllApart, Abi.Apart, BitVec.reduceAdd]
                      try simp only [add_sub_lit, BitVec.add_assoc, BitVec.add_zero, BitVec.reduceAdd, BitVec.reduceSub]
                      repeat' (with_reducible apply And.intro)
                      all_goals bv_decide
                    · simp only [P16.contract]
                      repeat' (with_reducible apply And.intro)
                      all_goals (first | assumption | bv_decide)
                    · dsimp only
                      simp only [P16.contract, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
                      repeat' (with_reducible apply And.intro)
                      all_goals (first | mem_auto | (apply_frame <;> mem_auto) | (apply_intro <;> first | mem_auto | (apply_frame <;> mem_auto)))
                    · intro s10 hpc10 hsp10 hbx10 hbp10 h12_10 h13_10 h14_10 h15_10 hens10 hout10 hown10
                      obtain ⟨rax_10, rcx_10, rdx_10, rbx_10, rsp_10, rbp_10, rsi_10, rdi_10, r8_10, r9_10, r12_10, r13_10, r14_10, r15_10, zf_10, cf_10, y10_0, y10_1, y10_2, y10_3, y10_4, y10_5, y10_6, y10_7, y10_8, y10_9, y10_10, y10_11, y10_12, y10_13, y10_14, y10_15, mem10, pc_10⟩ := s10
                      dsimp only at hpc10 hsp10 hbx10 hbp10 h12_10 h13_10 h14_10 h15_10 hens10 hout10 hown10
                      subst pc_10 rsp_10 rbx_10 rbp_10 r12_10 r13_10 r14_10 r15_10
                      simp only [P16.contract, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true] at hens10
                      split_ands hens10
                      simp only [P16.contract, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, add_sub_lit, BitVec.add_assoc, BitVec.add_zero, BitVec.reduceAdd, BitVec.reduceSub] at hout10
                      have hF10 : Region mem10 fb 5424#64 := hown10 fb 5424#64 (by mem_region)
                      have hS10_0 : Quad mem10 (fb + 5424#64) ra := X86.Quad.frame (by mem_fact) (fun x hx => hout10 x (by bv_decide) (by bv_decide))
                      have hS10_1 : Quad mem10 (fb + 5416#64) sv.rbx := X86.Quad.frame (by mem_fact) (fun x hx => hout10 x (by bv_decide) (by bv_decide))
                      have hS10_2 : Quad mem10 (fb + 5408#64) sv.rbp := X86.Quad.frame (by mem_fact) (fun x hx => hout10 x (by bv_decide) (by bv_decide))
                      have hS10_3 : Quad mem10 (fb + 5400#64) sv.r12 := X86.Quad.frame (by mem_fact) (fun x hx => hout10 x (by bv_decide) (by bv_decide))
                      have hS10_4 : Quad mem10 (fb + 5392#64) sv.r13 := X86.Quad.frame (by mem_fact) (fun x hx => hout10 x (by bv_decide) (by bv_decide))
                      have hS10_5 : Quad mem10 (fb + 5384#64) sv.r14 := X86.Quad.frame (by mem_fact) (fun x hx => hout10 x (by bv_decide) (by bv_decide))
                      have hOut : (∀ x : BitVec 64, (Abi.Contract.framed (Tree32.contract res cvs key flags k l) 5424#64).stack + 8#64 ≤ x - fb → (∀ r ∈ (Abi.Contract.framed (Tree32.contract res cvs key flags k l) 5424#64).modifies, r.2 ≤ x - r.1) → mem10 x = m0 x) := by
                        intro x hx hmod
                        have hx' := hx
                        have hmod' := hmod
                        simp only [Tree32.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, BitVec.reduceAdd] at hx' hmod'
                        rw [hout10 x (by bv_decide) (by bv_decide)]
                        refine Eq.trans ?_ (hOut x hx hmod); first | rfl | mem_away
                      clear hout10 hown10
                      refine runs_then (a := 7) (s1 := ?_) ?_ ?_
                      case refine_2 => run_fn []; rfl
                      refine runs_done ⟨rfl, by simp only [Tree32.contract, Abi.Contract.framed]; bv_decide, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
                      all_goals try dsimp only
                      · intro x hx hmod
                        refine Eq.trans ?_ (hOut x hx hmod)
                        have hx' := hx
                        have hmod' := hmod
                        simp only [Tree32.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, BitVec.reduceAdd] at hx' hmod'
                        first | rfl | mem_away
                      · simp only [Tree32.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
                        apply Tree32.exit <;> mem_auto

/-- **`tree32`, as assembled, meets its contract, whatever its arguments.** -/
theorem tree32_meets (ext : Nat → Option (Instr × Nat)) (hA_parents16 : ∀ x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10, Abi.Meets (Code_tree32.prog ext) 0x18000 (P16.contract x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10)) : ∀ (res cvs key flags : BitVec 64) (k : Blake3.CV) (l : List Blake3.CV),
    Abi.Meets (Code_tree32.prog ext) 0x120000 (Tree32.contract res cvs key flags k l) := by
  intro res cvs key flags k l
  refine Abi.meets_of_triple 5424#64 (by dsimp only [Tree32.contract]; decide) (by dsimp only [Tree32.contract]; decide) (fun fb ra sv m0 => ?_)
  intro s hP
  exact whole ext hA_parents16 fb res cvs key flags ra sv k l m0 s hP

#print axioms tree32_meets

end Proof_tree32
