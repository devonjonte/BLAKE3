import Cells
import Kernels
import AbiProof
import Spec_fillp
import Lemmas_fillp
import Code_fillp
open X86 Cells

/-! # `fillp`, as assembled, meets `Fillp.contract`

Written by prove_fn.py from levels.ode and the compiler's layout; not edited by hand, and not to be read
but for its last theorem's statement: Lean checks the rest. The frame: 56 bytes below the stack pointer at entry
(`fb` is its lowest address), the caller's rbx, rbp, r12, r13, r14, r15 at its top.
-/

namespace Proof_fillp

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option linter.unusedVariables false

/-- What holds each time the loop's head is reached: the source's `invariant` clauses, each variable where the
compiler keeps it, and the frame as the compiler keeps it. -/
def Inv (fb ptrs base n stride ra : BitVec 64) (sv : Abi.Saved)  (m0 : Mem) (s : State) : Prop :=
  s.pc = 0x11002A ∧
  s.rsp = fb ∧
  s.rbx = ptrs ∧
  s.rbp = base ∧
  s.r12 = n ∧
  s.r13 = stride ∧
  Region s.mem fb 56#64 ∧
  Quad s.mem (fb + 56#64) ra ∧
  Quad s.mem (fb + 48#64) sv.rbx ∧
  Quad s.mem (fb + 40#64) sv.rbp ∧
  Quad s.mem (fb + 32#64) sv.r12 ∧
  Quad s.mem (fb + 24#64) sv.r13 ∧
  Quad s.mem (fb + 16#64) sv.r14 ∧
  Quad s.mem (fb + 8#64) sv.r15 ∧
  Abi.AllApart ((fb, (Abi.Contract.framed (Fillp.contract ptrs base n stride) 56#64).stack + 8#64) :: (Abi.Contract.framed (Fillp.contract ptrs base n stride) 56#64).regions) ∧
  (∀ x : BitVec 64, (Abi.Contract.framed (Fillp.contract ptrs base n stride) 56#64).stack + 8#64 ≤ x - fb → (∀ r ∈ (Abi.Contract.framed (Fillp.contract ptrs base n stride) 56#64).modifies, r.2 ≤ x - r.1) → s.mem x = m0 x) ∧
  (Abi.Contract.framed (Fillp.contract ptrs base n stride) 56#64).accepts ∧
  (Abi.Contract.framed (Fillp.contract ptrs base n stride) 56#64).requires m0 ∧
  Ptrs.Mid s.mem ptrs base n stride s.r14 s.r15

theorem enter (fb ptrs base n stride ra : BitVec 64) (sv : Abi.Saved)  (m0 : Mem)
    (s : State) (hP : Abi.Pre 0x110000 (Abi.Contract.framed (Fillp.contract ptrs base n stride) 56#64) fb ra sv m0 s) : ∃ n_ s', steps Code_fillp.prog n_ s = some s' ∧ Inv fb ptrs base n stride ra sv m0 s' := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r12, r13, r14, r15, zf, cf, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, mem, pc⟩ := s
  obtain ⟨hpc, hsp, hargs, hbx, hbp, h12, h13, h14, h15, hmem, hF, hRa, hAp, hAcc, hReq⟩ := hP
  simp only [Fillp.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true] at hpc hsp hargs hbx hbp h12 h13 h14 h15 hmem hF hRa
  simp only [List.length_cons, List.length_nil, List.take, List.cons.injEq, and_true] at hargs
  obtain ⟨ha0, ha1, ha2, ha3⟩ := hargs
  subst pc rsp rdi rsi rdx rcx rbx rbp r12 r13 r14 r15 mem
  have hAp0 := hAp
  simp only [Fillp.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, Abi.AllApart, Abi.Apart, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, BitVec.reduceAdd] at hAp
  split_ands hAp
  have hAcc0 := hAcc
  try (simp only [Fillp.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true] at hAcc; split_ands hAcc)
  have hReq0 := hReq
  simp only [Fillp.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true] at hReq
  split_ands hReq
  try (have hK0 := Ptrs.Mid.cells (m := m0) (by assumption); split_ands hK0)
  refine runs_then (a := 15) (s1 := ?_) ?_ ?_
  case refine_2 => run_fn []; rfl
  refine runs_done ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
    simp only [Fillp.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, BitVec.reduceAdd] at hx' hmod'
    first | rfl | mem_away
  · exact hAcc0
  · exact hReq0
  · skip
    · apply Ptrs.Mid.start <;> mem_auto

theorem turn (fb ptrs base n stride ra : BitVec 64) (sv : Abi.Saved)  (m0 : Mem)
    (s : State) (hI : Inv fb ptrs base n stride ra sv m0 s) (hc : s.r14 < 32#64) :
    ∃ n_ s', steps Code_fillp.prog n_ s = some s' ∧ (Inv fb ptrs base n stride ra sv m0 s' ∧ ((32#64 - s'.r14)).toNat < ((32#64 - s.r14)).toNat) := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r12, r13, i, cur, zf, cf, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, mem, pc⟩ := s
  obtain ⟨hpc, hsp, hp0, hp1, hp2, hp3, hF, hRa, hS0, hS1, hS2, hS3, hS4, hS5, hAp, hOut, hAcc, hReq, hI0⟩ := hI
  simp only at hpc hsp hp0 hp1 hp2 hp3 hF hRa hS0 hS1 hS2 hS3 hS4 hS5 hOut hI0 hc
  subst pc rsp rbx rbp r12 r13
  have hAp0 := hAp
  simp only [Fillp.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, Abi.AllApart, Abi.Apart, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, BitVec.reduceAdd] at hAp
  split_ands hAp
  have hAcc0 := hAcc
  try (simp only [Fillp.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true] at hAcc; split_ands hAcc)
  have hReq0 := hReq
  simp only [Fillp.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true] at hReq
  split_ands hReq
  forget_about m0 except hOut hReq0
  try (have hK0 := Ptrs.Mid.cells (m := mem) (by assumption); split_ands hK0)
  by_cases hs1 : i < n
  · have c0 : (i).ult (32#64) = true := by bv_decide
    have c1 : (i).ult (n) = true := by bv_decide
    refine runs_then (a := 22) (s1 := ?_) ?_ ?_
    case refine_2 => run_fn [c0, c1]; rfl
    refine runs_done ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
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
      simp only [Fillp.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, BitVec.reduceAdd] at hx' hmod'
      first | rfl | mem_away
    · exact hAcc0
    · exact hReq0
    · skip
      · first | (apply Ptrs.Mid.real <;> mem_auto) | (apply Ptrs.Mid.dup <;> mem_auto)
    · exact BitVec.lt_def.mp (by bv_decide)
  · have c0 : (i).ult (32#64) = true := by bv_decide
    have c1 : (i).ult (n) = false := by bv_decide
    refine runs_then (a := 21) (s1 := ?_) ?_ ?_
    case refine_2 => run_fn [c0, c1]; rfl
    refine runs_done ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
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
      simp only [Fillp.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, BitVec.reduceAdd] at hx' hmod'
      first | rfl | mem_away
    · exact hAcc0
    · exact hReq0
    · skip
      · first | (apply Ptrs.Mid.real <;> mem_auto) | (apply Ptrs.Mid.dup <;> mem_auto)
    · exact BitVec.lt_def.mp (by bv_decide)

theorem leave (fb ptrs base n stride ra : BitVec 64) (sv : Abi.Saved)  (m0 : Mem)
    (s : State) (hI : Inv fb ptrs base n stride ra sv m0 s) (hc : ¬ s.r14 < 32#64) :
    ∃ n_ s', steps Code_fillp.prog n_ s = some s' ∧ Abi.Post (Abi.Contract.framed (Fillp.contract ptrs base n stride) 56#64) fb ra sv m0 s' := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r12, r13, i, cur, zf, cf, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, mem, pc⟩ := s
  obtain ⟨hpc, hsp, hp0, hp1, hp2, hp3, hF, hRa, hS0, hS1, hS2, hS3, hS4, hS5, hAp, hOut, hAcc, hReq, hI0⟩ := hI
  simp only at hpc hsp hp0 hp1 hp2 hp3 hF hRa hS0 hS1 hS2 hS3 hS4 hS5 hOut hI0 hc
  subst pc rsp rbx rbp r12 r13
  have hAp0 := hAp
  simp only [Fillp.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, Abi.AllApart, Abi.Apart, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, BitVec.reduceAdd] at hAp
  split_ands hAp
  have hAcc0 := hAcc
  try (simp only [Fillp.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true] at hAcc; split_ands hAcc)
  have hReq0 := hReq
  simp only [Fillp.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true] at hReq
  split_ands hReq
  forget_about m0 except hOut hReq0
  try (have hK0 := Ptrs.Mid.cells (m := mem) (by assumption); split_ands hK0)
  have c0 : (i).ult (32#64) = false := by bv_decide
  refine runs_then (a := 12) (s1 := ?_) ?_ ?_
  case refine_2 => run_fn [c0]; rfl
  refine runs_done ⟨rfl, by simp only [Fillp.contract, Abi.Contract.framed]; bv_decide, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  all_goals try dsimp only
  · intro x hx hmod
    refine Eq.trans ?_ (hOut x hx hmod)
    have hx' := hx
    have hmod' := hmod
    simp only [Fillp.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, BitVec.reduceAdd] at hx' hmod'
    first | rfl | mem_away
  · simp only [Fillp.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
    apply Fillp.exit <;> mem_auto

/-- **`fillp`, as assembled, meets its contract, whatever its arguments.** -/
theorem fillp_meets : ∀ (ptrs base n stride : BitVec 64) ,
    Abi.Meets Code_fillp.prog 0x110000 (Fillp.contract ptrs base n stride) := by
  intro ptrs base n stride
  refine Abi.meets_of_triple 56#64 (by dsimp only [Fillp.contract]; decide) (by dsimp only [Fillp.contract]; decide) (fun fb ra sv m0 => ?_)
  refine Hoare.seq (Q := Inv fb ptrs base n stride ra sv m0) ?_ ?_
  · intro s hP
    exact enter fb ptrs base n stride ra sv m0 s hP
  · refine Hoare.loop (fun s => ((32#64 - s.r14)).toNat) (fun s hI => ?_)
    by_cases hc : s.r14 < 32#64
    · obtain ⟨n_, s', h, hi, hm⟩ := turn fb ptrs base n stride ra sv m0 s hI hc
      exact ⟨n_, s', h, Or.inl ⟨hi, hm⟩⟩
    · obtain ⟨n_, s', h, hq⟩ := leave fb ptrs base n stride ra sv m0 s hI hc
      exact ⟨n_, s', h, Or.inr hq⟩

#print axioms fillp_meets

end Proof_fillp
