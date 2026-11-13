import Cells
import Kernels
import AbiProof
import AbiCall
import Spec_mergesteps
import Lemmas_merge_steps
import Proof_merge
import Code_merge_steps
open X86 Cells

/-! # `merge_steps`, as assembled, meets `MergeSteps.contract`

Written by prove_fn.py from hasher.ode and the compiler's layout; not edited by hand, and not to be read
but for its last theorem's statement: Lean checks the rest. The frame: 320 bytes below the stack pointer at entry
(`fb` is its lowest address), the caller's rbx, rbp, r12, r13, r14, r15 at its top.
-/

namespace Proof_merge_steps

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option linter.unusedVariables false

/-- What holds each time the loop's head is reached: the source's `invariant` clauses, each variable where the
compiler keeps it, and the frame as the compiler keeps it. -/
def Inv (fb st key flags plat target ra : BitVec 64) (sv : Abi.Saved) (k : Blake3.CV) (cvs : List Blake3.CV) (m0 : Mem) (s : State) : Prop :=
  s.pc = 0xA0026 ∧
  s.rsp = (fb + 264#64) ∧
  s.rbx = st ∧
  s.rbp = key ∧
  s.r12 = flags ∧
  s.r13 = plat ∧
  s.r14 = target ∧
  Region s.mem fb 320#64 ∧
  Quad s.mem (fb + 320#64) ra ∧
  Quad s.mem (fb + 312#64) sv.rbx ∧
  Quad s.mem (fb + 304#64) sv.rbp ∧
  Quad s.mem (fb + 296#64) sv.r12 ∧
  Quad s.mem (fb + 288#64) sv.r13 ∧
  Quad s.mem (fb + 280#64) sv.r14 ∧
  Quad s.mem (fb + 272#64) sv.r15 ∧
  Abi.AllApart ((fb, (Abi.Contract.framed (MergeSteps.contract st key flags plat target k cvs) 320#64).stack + 8#64) :: (Abi.Contract.framed (MergeSteps.contract st key flags plat target k cvs) 320#64).regions) ∧
  (∀ x : BitVec 64, (Abi.Contract.framed (MergeSteps.contract st key flags plat target k cvs) 320#64).stack + 8#64 ≤ x - fb → (∀ r ∈ (Abi.Contract.framed (MergeSteps.contract st key flags plat target k cvs) 320#64).modifies, r.2 ≤ x - r.1) → s.mem x = m0 x) ∧
  (Abi.Contract.framed (MergeSteps.contract st key flags plat target k cvs) 320#64).accepts ∧
  (Abi.Contract.framed (MergeSteps.contract st key flags plat target k cvs) 320#64).requires m0 ∧
  ∃ (now : List Blake3.CV) , Stack.At s.mem st now ∧
    s.r15 = (Stack.count now) ∧
    (Merge.result k flags target now) = (Merge.result k flags target cvs) ∧
    Cv.At s.mem key k

theorem enter (fb st key flags plat target ra : BitVec 64) (sv : Abi.Saved) (k : Blake3.CV) (cvs : List Blake3.CV) (m0 : Mem)
    (s : State) (hP : Abi.Pre 0xA0000 (Abi.Contract.framed (MergeSteps.contract st key flags plat target k cvs) 320#64) fb ra sv m0 s) : ∃ n_ s', steps Code_merge_steps.prog n_ s = some s' ∧ Inv fb st key flags plat target ra sv k cvs m0 s' := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r12, r13, r14, r15, zf, cf, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, mem, pc⟩ := s
  obtain ⟨hpc, hsp, hargs, hbx, hbp, h12, h13, h14, h15, hmem, hF, hRa, hAp, hAcc, hReq⟩ := hP
  simp only [MergeSteps.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true] at hpc hsp hargs hbx hbp h12 h13 h14 h15 hmem hF hRa
  simp only [List.length_cons, List.length_nil, List.take, List.cons.injEq, and_true] at hargs
  obtain ⟨ha0, ha1, ha2, ha3, ha4⟩ := hargs
  subst pc rsp rdi rsi rdx rcx r8 rbx rbp r12 r13 r14 r15 mem
  have hAp0 := hAp
  simp only [MergeSteps.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, Abi.AllApart, Abi.Apart, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, BitVec.reduceAdd] at hAp
  split_ands hAp
  have hAcc0 := hAcc
  try (simp only [MergeSteps.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true] at hAcc; split_ands hAcc)
  have hReq0 := hReq
  simp only [MergeSteps.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true] at hReq
  split_ands hReq
  try (have hK0 := Stack.At.cells (m := m0) (by assumption); split_ands hK0)
  try (have hK1 := Cv.At.cells (m := m0) (by assumption); split_ands hK1)
  refine runs_then (a := 15) (s1 := ?_) ?_ ?_
  case refine_2 => run_fn []; rfl
  refine runs_done ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try dsimp only
  · mem_region
  · mem_fact
  · mem_fact
  · mem_fact
  · mem_fact
  · mem_fact
  · mem_fact
  · mem_fact
  · exact hAp0
  · intro x hx hmod
    have hx' := hx
    have hmod' := hmod
    simp only [MergeSteps.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, BitVec.reduceAdd] at hx' hmod'
    first | rfl | mem_away
  · exact hAcc0
  · exact hReq0
  · apply Exists.intro
    refine ⟨?_, ?_, ?_, ?_⟩
    · first | mem_auto | (apply Stack.At.frame <;> mem_auto)
    · first | rfl | mem_auto
    · first | rfl | mem_auto
    · first | mem_auto | (apply Cv.At.frame <;> mem_auto)

theorem turn (fb st key flags plat target ra : BitVec 64) (sv : Abi.Saved) (k : Blake3.CV) (cvs : List Blake3.CV) (m0 : Mem)
    (s : State) (hI : Inv fb st key flags plat target ra sv k cvs m0 s) (hc : target < s.r15) :
    ∃ n_ s', steps Code_merge_steps.prog n_ s = some s' ∧ (Inv fb st key flags plat target ra sv k cvs m0 s' ∧ s'.r15.toNat < s.r15.toNat) := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r12, r13, r14, len, zf, cf, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, mem, pc⟩ := s
  obtain ⟨hpc, hsp, hp0, hp1, hp2, hp3, hp4, hF, hRa, hS0, hS1, hS2, hS3, hS4, hS5, hAp, hOut, hAcc, hReq, now, hI0, hI1, hI2, hI3⟩ := hI
  simp only at hpc hsp hp0 hp1 hp2 hp3 hp4 hF hRa hS0 hS1 hS2 hS3 hS4 hS5 hAp hOut hAcc hReq hI0 hI1 hI3 hc
  subst pc rsp rbx rbp r12 r13 r14
  have hAp0 := hAp
  simp only [MergeSteps.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, Abi.AllApart, Abi.Apart, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, BitVec.reduceAdd] at hAp
  split_ands hAp
  have hAcc0 := hAcc
  try (simp only [MergeSteps.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true] at hAcc; split_ands hAcc)
  have hReq0 := hReq
  simp only [MergeSteps.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true] at hReq
  split_ands hReq
  forget_about m0 except hOut hReq0
  try (have hK0 := Stack.At.cells (m := mem) (by assumption); split_ands hK0)
  try (have hK1 := Cv.At.cells (m := mem) (by assumption); split_ands hK1)
  have c0 : (target).ult (len) = true := by bv_decide
  refine runs_then (a := 13) (s1 := ?_) ?_ ?_
  case refine_2 => run_fn [c0]; rfl
  refine Abi.call_meets (c := Merge.contract st key flags plat (len - 1#64) k now) (ra := 655439#64)
    (Abi.Meets.mono Code_merge_steps.has_merge (Proof_merge.merge_meets st key flags plat (len - 1#64) k now)) rfl rfl ?_ ?_ ?_ ?_ ?_ ?_
  · dsimp only; mem_fact
  · dsimp only [Merge.contract]; mem_subregion
  · dsimp only
    simp only [Merge.contract, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, Abi.AllApart, Abi.Apart, BitVec.reduceAdd]
    try simp only [add_sub_lit, BitVec.add_assoc, BitVec.add_zero, BitVec.reduceAdd, BitVec.reduceSub]
    repeat' (with_reducible apply And.intro)
    all_goals bv_decide
  · simp only [Merge.contract]
    repeat' (with_reducible apply And.intro)
    all_goals (first | assumption | bv_decide)
  · dsimp only
    simp only [Merge.contract, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
    repeat' (with_reducible apply And.intro)
    all_goals (first | mem_auto | (apply_frame <;> mem_auto) | (apply_intro <;> first | mem_auto | (apply_frame <;> mem_auto)))
  · intro s1 hpc1 hsp1 hbx1 hbp1 h12_1 h13_1 h14_1 h15_1 hens1 hout1 hown1
    obtain ⟨rax_1, rcx_1, rdx_1, rbx_1, rsp_1, rbp_1, rsi_1, rdi_1, r8_1, r9_1, r12_1, r13_1, r14_1, r15_1, zf_1, cf_1, y1_0, y1_1, y1_2, y1_3, y1_4, y1_5, y1_6, y1_7, y1_8, y1_9, y1_10, y1_11, y1_12, y1_13, y1_14, y1_15, mem1, pc_1⟩ := s1
    dsimp only at hpc1 hsp1 hbx1 hbp1 h12_1 h13_1 h14_1 h15_1 hens1 hout1 hown1
    subst pc_1 rsp_1 rbx_1 rbp_1 r12_1 r13_1 r14_1 r15_1
    simp only [Merge.contract, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true] at hens1
    split_ands hens1
    simp only [Merge.contract, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, add_sub_lit, BitVec.add_assoc, BitVec.add_zero, BitVec.reduceAdd, BitVec.reduceSub] at hout1
    have hF1 : Region mem1 fb 320#64 := hown1 fb 320#64 (by mem_region)
    have hS1_0 : Quad mem1 (fb + 320#64) ra := X86.Quad.frame (by mem_fact) (fun x hx => hout1 x (by bv_decide) (by bv_decide))
    have hS1_1 : Quad mem1 (fb + 312#64) sv.rbx := X86.Quad.frame (by mem_fact) (fun x hx => hout1 x (by bv_decide) (by bv_decide))
    have hS1_2 : Quad mem1 (fb + 304#64) sv.rbp := X86.Quad.frame (by mem_fact) (fun x hx => hout1 x (by bv_decide) (by bv_decide))
    have hS1_3 : Quad mem1 (fb + 296#64) sv.r12 := X86.Quad.frame (by mem_fact) (fun x hx => hout1 x (by bv_decide) (by bv_decide))
    have hS1_4 : Quad mem1 (fb + 288#64) sv.r13 := X86.Quad.frame (by mem_fact) (fun x hx => hout1 x (by bv_decide) (by bv_decide))
    have hS1_5 : Quad mem1 (fb + 280#64) sv.r14 := X86.Quad.frame (by mem_fact) (fun x hx => hout1 x (by bv_decide) (by bv_decide))
    have hS1_6 : Quad mem1 (fb + 272#64) sv.r15 := X86.Quad.frame (by mem_fact) (fun x hx => hout1 x (by bv_decide) (by bv_decide))
    have hK1_0 : Cv.At mem1 key k := Cv.At.frame (m := mem) (by assumption) (fun x hx => by rw [hout1 x (by bv_decide) (by bv_decide)]; first | rfl | mem_away)
    have hOut : (∀ x : BitVec 64, (Abi.Contract.framed (MergeSteps.contract st key flags plat target k cvs) 320#64).stack + 8#64 ≤ x - fb → (∀ r ∈ (Abi.Contract.framed (MergeSteps.contract st key flags plat target k cvs) 320#64).modifies, r.2 ≤ x - r.1) → mem1 x = m0 x) := by
      intro x hx hmod
      have hx' := hx
      have hmod' := hmod
      simp only [MergeSteps.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, BitVec.reduceAdd] at hx' hmod'
      rw [hout1 x (by bv_decide) (by bv_decide)]
      refine Eq.trans ?_ (hOut x hx hmod); first | rfl | mem_away
    clear hout1 hown1
    refine runs_then (a := 1) (s1 := ?_) ?_ ?_
    case refine_2 => run_fn [c0]; rfl
    refine runs_done ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    all_goals try dsimp only
    · mem_region
    · mem_fact
    · mem_fact
    · mem_fact
    · mem_fact
    · mem_fact
    · mem_fact
    · mem_fact
    · exact hAp0
    · intro x hx hmod
      refine Eq.trans ?_ (hOut x hx hmod)
      have hx' := hx
      have hmod' := hmod
      simp only [MergeSteps.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, BitVec.reduceAdd] at hx' hmod'
      first | rfl | mem_away
    · exact hAcc0
    · exact hReq0
    · apply Exists.intro
      refine ⟨?_, ?_, ?_, ?_⟩
      · first | mem_auto | (apply Stack.At.frame <;> mem_auto)
      · apply MergeSteps.count <;> mem_auto
      · apply MergeSteps.result <;> mem_auto
      · first | mem_auto | (apply Cv.At.frame <;> mem_auto)
    · exact BitVec.lt_def.mp (by bv_decide)

theorem leave (fb st key flags plat target ra : BitVec 64) (sv : Abi.Saved) (k : Blake3.CV) (cvs : List Blake3.CV) (m0 : Mem)
    (s : State) (hI : Inv fb st key flags plat target ra sv k cvs m0 s) (hc : ¬ target < s.r15) :
    ∃ n_ s', steps Code_merge_steps.prog n_ s = some s' ∧ Abi.Post (Abi.Contract.framed (MergeSteps.contract st key flags plat target k cvs) 320#64) fb ra sv m0 s' := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r12, r13, r14, len, zf, cf, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, mem, pc⟩ := s
  obtain ⟨hpc, hsp, hp0, hp1, hp2, hp3, hp4, hF, hRa, hS0, hS1, hS2, hS3, hS4, hS5, hAp, hOut, hAcc, hReq, now, hI0, hI1, hI2, hI3⟩ := hI
  simp only at hpc hsp hp0 hp1 hp2 hp3 hp4 hF hRa hS0 hS1 hS2 hS3 hS4 hS5 hAp hOut hAcc hReq hI0 hI1 hI3 hc
  subst pc rsp rbx rbp r12 r13 r14
  have hAp0 := hAp
  simp only [MergeSteps.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, Abi.AllApart, Abi.Apart, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, BitVec.reduceAdd] at hAp
  split_ands hAp
  have hAcc0 := hAcc
  try (simp only [MergeSteps.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true] at hAcc; split_ands hAcc)
  have hReq0 := hReq
  simp only [MergeSteps.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true] at hReq
  split_ands hReq
  forget_about m0 except hOut hReq0
  try (have hK0 := Stack.At.cells (m := mem) (by assumption); split_ands hK0)
  try (have hK1 := Cv.At.cells (m := mem) (by assumption); split_ands hK1)
  have c0 : (target).ult (len) = false := by bv_decide
  refine runs_then (a := 13) (s1 := ?_) ?_ ?_
  case refine_2 => run_fn [c0]; rfl
  refine runs_done ⟨rfl, by simp only [MergeSteps.contract, Abi.Contract.framed]; bv_decide, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  all_goals try dsimp only
  · intro x hx hmod
    refine Eq.trans ?_ (hOut x hx hmod)
    have hx' := hx
    have hmod' := hmod
    simp only [MergeSteps.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, BitVec.reduceAdd] at hx' hmod'
    first | rfl | mem_away
  · simp only [MergeSteps.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
    apply Merge.exit <;> mem_auto

/-- **`merge_steps`, as assembled, meets its contract, whatever its arguments.** -/
theorem merge_steps_meets : ∀ (st key flags plat target : BitVec 64) (k : Blake3.CV) (cvs : List Blake3.CV),
    Abi.Meets Code_merge_steps.prog 0xA0000 (MergeSteps.contract st key flags plat target k cvs) := by
  intro st key flags plat target k cvs
  refine Abi.meets_of_triple 320#64 (by dsimp only [MergeSteps.contract]; decide) (by dsimp only [MergeSteps.contract]; decide) (fun fb ra sv m0 => ?_)
  refine Hoare.seq (Q := Inv fb st key flags plat target ra sv k cvs m0) ?_ ?_
  · intro s hP
    exact enter fb st key flags plat target ra sv k cvs m0 s hP
  · refine Hoare.loop (fun s => s.r15.toNat) (fun s hI => ?_)
    by_cases hc : target < s.r15
    · obtain ⟨n_, s', h, hi, hm⟩ := turn fb st key flags plat target ra sv k cvs m0 s hI hc
      exact ⟨n_, s', h, Or.inl ⟨hi, hm⟩⟩
    · obtain ⟨n_, s', h, hq⟩ := leave fb st key flags plat target ra sv k cvs m0 s hI hc
      exact ⟨n_, s', h, Or.inr hq⟩

#print axioms merge_steps_meets

end Proof_merge_steps
