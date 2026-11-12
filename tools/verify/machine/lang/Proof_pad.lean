import Cells
import Kernels
import AbiProof
import Spec_pad
import Lemmas_pad
import Code_pad
open X86 Cells

/-! # `pad`, as assembled, meets `Pad.contract`

Written by prove_fn.py from levels.ode and the compiler's layout; not edited by hand, and not to be read
but for its last theorem's statement: Lean checks the rest. The frame: 40 bytes below the stack pointer at entry
(`fb` is its lowest address), the caller's rbx, rbp, r12, r13 at its top.
-/

namespace Proof_pad

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option linter.unusedVariables false

/-- What holds each time the loop's head is reached: the source's `invariant` clauses, each variable where the
compiler keeps it, and the frame as the compiler keeps it. -/
def Inv (fb block src n ra : BitVec 64) (sv : Abi.Saved) (bytes : List (BitVec 8)) (m0 : Mem) (s : State) : Prop :=
  s.pc = 0xE001D ∧
  s.rsp = fb ∧
  s.rbx = block ∧
  s.rbp = src ∧
  s.r12 = n ∧
  s.r14 = sv.r14 ∧
  s.r15 = sv.r15 ∧
  Region s.mem fb 40#64 ∧
  Quad s.mem (fb + 40#64) ra ∧
  Quad s.mem (fb + 32#64) sv.rbx ∧
  Quad s.mem (fb + 24#64) sv.rbp ∧
  Quad s.mem (fb + 16#64) sv.r12 ∧
  Quad s.mem (fb + 8#64) sv.r13 ∧
  Abi.AllApart ((fb, (Abi.Contract.framed (Pad.contract block src n bytes) 40#64).stack + 8#64) :: (Abi.Contract.framed (Pad.contract block src n bytes) 40#64).regions) ∧
  (∀ x : BitVec 64, (Abi.Contract.framed (Pad.contract block src n bytes) 40#64).stack + 8#64 ≤ x - fb → (∀ r ∈ (Abi.Contract.framed (Pad.contract block src n bytes) 40#64).modifies, r.2 ≤ x - r.1) → s.mem x = m0 x) ∧
  (Abi.Contract.framed (Pad.contract block src n bytes) 40#64).accepts ∧
  (Abi.Contract.framed (Pad.contract block src n bytes) 40#64).requires m0 ∧
  Pad.Mid s.mem block src bytes n s.r13

theorem enter (fb block src n ra : BitVec 64) (sv : Abi.Saved) (bytes : List (BitVec 8)) (m0 : Mem)
    (s : State) (hP : Abi.Pre 0xE0000 (Abi.Contract.framed (Pad.contract block src n bytes) 40#64) fb ra sv m0 s) : ∃ n_ s', steps Code_pad.prog n_ s = some s' ∧ Inv fb block src n ra sv bytes m0 s' := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r12, r13, r14, r15, zf, cf, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, mem, pc⟩ := s
  obtain ⟨hpc, hsp, hargs, hbx, hbp, h12, h13, h14, h15, hmem, hF, hRa, hAp, hAcc, hReq⟩ := hP
  simp only [Pad.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true] at hpc hsp hargs hbx hbp h12 h13 h14 h15 hmem hF hRa
  simp only [List.length_cons, List.length_nil, List.take, List.cons.injEq, and_true] at hargs
  obtain ⟨ha0, ha1, ha2⟩ := hargs
  subst pc rsp rdi rsi rdx rbx rbp r12 r13 r14 r15 mem
  have hAp0 := hAp
  simp only [Pad.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, Abi.AllApart, Abi.Apart, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, BitVec.reduceAdd] at hAp
  split_ands hAp
  have hAcc0 := hAcc
  try (simp only [Pad.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true] at hAcc; split_ands hAcc)
  have hReq0 := hReq
  simp only [Pad.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true] at hReq
  split_ands hReq
  try (have hK0 := Pad.Mid.cells (m := m0) (by assumption); split_ands hK0)
  refine runs_then (a := 10) (s1 := ?_) ?_ ?_
  case refine_2 => run_fn []; rfl
  refine runs_done ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try dsimp only
  · mem_region
  · mem_fact
  · mem_fact
  · mem_fact
  · mem_fact
  · mem_fact
  · exact hAp0
  · intro x hx hmod
    have hx' := hx
    have hmod' := hmod
    simp only [Pad.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, BitVec.reduceAdd] at hx' hmod'
    first | rfl | mem_away
  · exact hAcc0
  · exact hReq0
  · skip
    · apply Pad.Mid.start <;> mem_auto

theorem turn (fb block src n ra : BitVec 64) (sv : Abi.Saved) (bytes : List (BitVec 8)) (m0 : Mem)
    (s : State) (hI : Inv fb block src n ra sv bytes m0 s) (hc : 0#64 < s.r13) :
    ∃ n_ s', steps Code_pad.prog n_ s = some s' ∧ (Inv fb block src n ra sv bytes m0 s' ∧ s'.r13.toNat < s.r13.toNat) := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r12, i, r14, r15, zf, cf, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, mem, pc⟩ := s
  obtain ⟨hpc, hsp, hp0, hp1, hp2, hu0, hu1, hF, hRa, hS0, hS1, hS2, hS3, hAp, hOut, hAcc, hReq, hI0⟩ := hI
  simp only at hpc hsp hp0 hp1 hp2 hu0 hu1 hF hRa hS0 hS1 hS2 hS3 hOut hI0 hc
  subst pc rsp rbx rbp r12 r14 r15
  have hAp0 := hAp
  simp only [Pad.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, Abi.AllApart, Abi.Apart, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, BitVec.reduceAdd] at hAp
  split_ands hAp
  have hAcc0 := hAcc
  try (simp only [Pad.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true] at hAcc; split_ands hAcc)
  have hReq0 := hReq
  simp only [Pad.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true] at hReq
  split_ands hReq
  forget_about m0 except hOut hReq0
  try (have hK0 := Pad.Mid.cells (m := mem) (by assumption); split_ands hK0)
  by_cases hs1 : (i - 1#64) < n
  · have_by hO0 := Pad.Mid.next (m := mem)
    obtain ⟨b, hO0⟩ := hO0
    try norm_addr at hO0
    split_ands hO0
    have c0 : (0#64).ult (i) = true := by bv_decide
    have c1 : ((i - 1#64)).ult (n) = true := by bv_decide
    refine runs_then (a := 19) (s1 := ?_) ?_ ?_
    case refine_2 => run_fn [c0, c1]; rfl
    refine runs_done ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    all_goals try dsimp only
    · mem_region
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
      simp only [Pad.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, BitVec.reduceAdd] at hx' hmod'
      first | rfl | mem_away
    · exact hAcc0
    · exact hReq0
    · skip
      · first | (apply Pad.Mid.copy <;> mem_auto) | (apply Pad.Mid.zero <;> mem_auto)
    · exact BitVec.lt_def.mp (by bv_decide)
  · have c0 : (0#64).ult (i) = true := by bv_decide
    have c1 : ((i - 1#64)).ult (n) = false := by bv_decide
    refine runs_then (a := 16) (s1 := ?_) ?_ ?_
    case refine_2 => run_fn [c0, c1]; rfl
    refine runs_done ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    all_goals try dsimp only
    · mem_region
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
      simp only [Pad.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, BitVec.reduceAdd] at hx' hmod'
      first | rfl | mem_away
    · exact hAcc0
    · exact hReq0
    · skip
      · first | (apply Pad.Mid.copy <;> mem_auto) | (apply Pad.Mid.zero <;> mem_auto)
    · exact BitVec.lt_def.mp (by bv_decide)

theorem leave (fb block src n ra : BitVec 64) (sv : Abi.Saved) (bytes : List (BitVec 8)) (m0 : Mem)
    (s : State) (hI : Inv fb block src n ra sv bytes m0 s) (hc : ¬ 0#64 < s.r13) :
    ∃ n_ s', steps Code_pad.prog n_ s = some s' ∧ Abi.Post (Abi.Contract.framed (Pad.contract block src n bytes) 40#64) fb ra sv m0 s' := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r12, i, r14, r15, zf, cf, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, mem, pc⟩ := s
  obtain ⟨hpc, hsp, hp0, hp1, hp2, hu0, hu1, hF, hRa, hS0, hS1, hS2, hS3, hAp, hOut, hAcc, hReq, hI0⟩ := hI
  simp only at hpc hsp hp0 hp1 hp2 hu0 hu1 hF hRa hS0 hS1 hS2 hS3 hOut hI0 hc
  subst pc rsp rbx rbp r12 r14 r15
  have hAp0 := hAp
  simp only [Pad.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, Abi.AllApart, Abi.Apart, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, BitVec.reduceAdd] at hAp
  split_ands hAp
  have hAcc0 := hAcc
  try (simp only [Pad.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true] at hAcc; split_ands hAcc)
  have hReq0 := hReq
  simp only [Pad.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true] at hReq
  split_ands hReq
  forget_about m0 except hOut hReq0
  try (have hK0 := Pad.Mid.cells (m := mem) (by assumption); split_ands hK0)
  have c0 : (0#64).ult (i) = false := by bv_decide
  refine runs_then (a := 10) (s1 := ?_) ?_ ?_
  case refine_2 => run_fn [c0]; rfl
  refine runs_done ⟨rfl, by simp only [Pad.contract, Abi.Contract.framed]; bv_decide, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  all_goals try dsimp only
  · intro x hx hmod
    refine Eq.trans ?_ (hOut x hx hmod)
    have hx' := hx
    have hmod' := hmod
    simp only [Pad.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, BitVec.reduceAdd] at hx' hmod'
    first | rfl | mem_away
  · simp only [Pad.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
    apply Pad.exit <;> mem_auto

/-- **`pad`, as assembled, meets its contract, whatever its arguments.** -/
theorem pad_meets : ∀ (block src n : BitVec 64) (bytes : List (BitVec 8)),
    Abi.Meets Code_pad.prog 0xE0000 (Pad.contract block src n bytes) := by
  intro block src n bytes
  refine Abi.meets_of_triple 40#64 (by dsimp only [Pad.contract]; decide) (by dsimp only [Pad.contract]; decide) (fun fb ra sv m0 => ?_)
  refine Hoare.seq (Q := Inv fb block src n ra sv bytes m0) ?_ ?_
  · intro s hP
    exact enter fb block src n ra sv bytes m0 s hP
  · refine Hoare.loop (fun s => s.r13.toNat) (fun s hI => ?_)
    by_cases hc : 0#64 < s.r13
    · obtain ⟨n_, s', h, hi, hm⟩ := turn fb block src n ra sv bytes m0 s hI hc
      exact ⟨n_, s', h, Or.inl ⟨hi, hm⟩⟩
    · obtain ⟨n_, s', h, hq⟩ := leave fb block src n ra sv bytes m0 s hI hc
      exact ⟨n_, s', h, Or.inr hq⟩

#print axioms pad_meets

end Proof_pad
