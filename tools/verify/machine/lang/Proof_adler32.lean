import Cells
import Kernels
import AbiProof
import Spec_adler32
import Lemmas_adler32
import Code_adler32
open X86 Cells

/-! # `adler32`, as assembled, meets `Adler32.contract`

Written by prove_fn.py from adler32.ode and the compiler's layout; not edited by hand, and not to be read
but for its last theorem's statement: Lean checks the rest. The frame: 40 bytes below the stack pointer at entry
(`fb` is its lowest address), the caller's rbx, rbp, r12, r13, r14 at its top.
-/

namespace Proof_adler32

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option linter.unusedVariables false

/-- What holds each time the loop's head is reached: the source's `invariant` clauses, each variable where the
compiler keeps it, and the frame as the compiler keeps it. -/
def Inv (fb input n ra : BitVec 64) (sv : Abi.Saved) (bytes : List (BitVec 8)) (m0 : Mem) (s : State) : Prop :=
  s.pc = 0x10002C ∧
  s.rsp = fb ∧
  s.rbx = input ∧
  s.rbp = n ∧
  s.r15 = sv.r15 ∧
  Region s.mem fb 40#64 ∧
  Quad s.mem (fb + 40#64) ra ∧
  Quad s.mem (fb + 32#64) sv.rbx ∧
  Quad s.mem (fb + 24#64) sv.rbp ∧
  Quad s.mem (fb + 16#64) sv.r12 ∧
  Quad s.mem (fb + 8#64) sv.r13 ∧
  Quad s.mem fb sv.r14 ∧
  Abi.AllApart ((fb, (Abi.Contract.framed (Adler32.contract input n bytes) 40#64).stack + 8#64) :: (Abi.Contract.framed (Adler32.contract input n bytes) 40#64).regions) ∧
  (∀ x : BitVec 64, (Abi.Contract.framed (Adler32.contract input n bytes) 40#64).stack + 8#64 ≤ x - fb → (∀ r ∈ (Abi.Contract.framed (Adler32.contract input n bytes) 40#64).modifies, r.2 ≤ x - r.1) → s.mem x = m0 x) ∧
  (Abi.Contract.framed (Adler32.contract input n bytes) 40#64).accepts ∧
  (Abi.Contract.framed (Adler32.contract input n bytes) 40#64).requires m0 ∧
  Adler32.Mid s.mem input n bytes s.r14 s.r12 s.r13

theorem enter (fb input n ra : BitVec 64) (sv : Abi.Saved) (bytes : List (BitVec 8)) (m0 : Mem)
    (s : State) (hP : Abi.Pre 0x100000 (Abi.Contract.framed (Adler32.contract input n bytes) 40#64) fb ra sv m0 s) : ∃ n_ s', steps Code_adler32.prog n_ s = some s' ∧ Inv fb input n ra sv bytes m0 s' := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r12, r13, r14, r15, zf, cf, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, mem, pc⟩ := s
  obtain ⟨hpc, hsp, hargs, hbx, hbp, h12, h13, h14, h15, hmem, hF, hRa, hAp, hAcc, hReq⟩ := hP
  simp only [Adler32.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true] at hpc hsp hargs hbx hbp h12 h13 h14 h15 hmem hF hRa
  simp only [List.length_cons, List.length_nil, List.take, List.cons.injEq, and_true] at hargs
  obtain ⟨ha0, ha1⟩ := hargs
  subst pc rsp rdi rsi rbx rbp r12 r13 r14 r15 mem
  have hAp0 := hAp
  simp only [Adler32.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, Abi.AllApart, Abi.Apart, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, BitVec.reduceAdd] at hAp
  split_ands hAp
  have hAcc0 := hAcc
  try (simp only [Adler32.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true] at hAcc; split_ands hAcc)
  have hReq0 := hReq
  simp only [Adler32.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true] at hReq
  split_ands hReq
  try (have hK0 := Adler32.Mid.cells (m := m0) (by assumption); split_ands hK0)
  refine runs_then (a := 13) (s1 := ?_) ?_ ?_
  case refine_2 => run_fn []; rfl
  refine runs_done ⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try dsimp only
  · mem_region
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
    simp only [Adler32.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, BitVec.reduceAdd] at hx' hmod'
    first | rfl | mem_away
  · exact hAcc0
  · exact hReq0
  · skip
    · apply Adler32.Mid.start <;> mem_auto

theorem turn (fb input n ra : BitVec 64) (sv : Abi.Saved) (bytes : List (BitVec 8)) (m0 : Mem)
    (s : State) (hI : Inv fb input n ra sv bytes m0 s) (hc : s.r14 < n) :
    ∃ n_ s', steps Code_adler32.prog n_ s = some s' ∧ (Inv fb input n ra sv bytes m0 s' ∧ ((n - s'.r14)).toNat < ((n - s.r14)).toNat) := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, a, b, i, r15, zf, cf, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, mem, pc⟩ := s
  obtain ⟨hpc, hsp, hp0, hp1, hu0, hF, hRa, hS0, hS1, hS2, hS3, hS4, hAp, hOut, hAcc, hReq, hI0⟩ := hI
  simp only at hpc hsp hp0 hp1 hu0 hF hRa hS0 hS1 hS2 hS3 hS4 hOut hI0 hc
  subst pc rsp rbx rbp r15
  have hAp0 := hAp
  simp only [Adler32.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, Abi.AllApart, Abi.Apart, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, BitVec.reduceAdd] at hAp
  split_ands hAp
  have hAcc0 := hAcc
  try (simp only [Adler32.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true] at hAcc; split_ands hAcc)
  have hReq0 := hReq
  simp only [Adler32.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true] at hReq
  split_ands hReq
  forget_about m0 except hOut hReq0
  try (have hK0 := Adler32.Mid.cells (m := mem) (by assumption); split_ands hK0)
  have_by hO0 := Adler32.Mid.next (m := mem)
  obtain ⟨v, hO0⟩ := hO0
  try norm_addr at hO0
  split_ands hO0
  by_cases hs1 : (a + ((mem.read (input + i) 8).getD 0#64)) < 65521#64
  · by_cases hs2 : (b + (a + ((mem.read (input + i) 8).getD 0#64))) < 65521#64
    · have c0 : (i).ult (n) = true := by bv_decide
      try simp (disch := mem_auto) only [read8_cell, Option.getD_some, add_sub_lit, BitVec.add_assoc] at c0
      have c1 : ((a + ((mem.read (input + i) 8).getD 0#64))).ult (65521#64) = true := by bv_decide
      try simp (disch := mem_auto) only [read8_cell, Option.getD_some, add_sub_lit, BitVec.add_assoc] at c1
      have c2 : ((b + (a + ((mem.read (input + i) 8).getD 0#64)))).ult (65521#64) = true := by bv_decide
      try simp (disch := mem_auto) only [read8_cell, Option.getD_some, add_sub_lit, BitVec.add_assoc] at c2
      refine runs_then (a := 27) (s1 := ?_) ?_ ?_
      case refine_2 => run_fn [c0, c1, c2]; rfl
      refine runs_done ⟨⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      all_goals try dsimp only
      · mem_region
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
        simp only [Adler32.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, BitVec.reduceAdd] at hx' hmod'
        first | rfl | mem_away
      · exact hAcc0
      · exact hReq0
      · skip
        · first | (apply Adler32.Mid.small_small <;> mem_auto) | (apply Adler32.Mid.small_large <;> mem_auto) | (apply Adler32.Mid.large_small <;> mem_auto) | (apply Adler32.Mid.large_large <;> mem_auto)
      · exact BitVec.lt_def.mp (by bv_decide)
    · have c0 : (i).ult (n) = true := by bv_decide
      try simp (disch := mem_auto) only [read8_cell, Option.getD_some, add_sub_lit, BitVec.add_assoc] at c0
      have c1 : ((a + ((mem.read (input + i) 8).getD 0#64))).ult (65521#64) = true := by bv_decide
      try simp (disch := mem_auto) only [read8_cell, Option.getD_some, add_sub_lit, BitVec.add_assoc] at c1
      have c2 : ((b + (a + ((mem.read (input + i) 8).getD 0#64)))).ult (65521#64) = false := by bv_decide
      try simp (disch := mem_auto) only [read8_cell, Option.getD_some, add_sub_lit, BitVec.add_assoc] at c2
      refine runs_then (a := 29) (s1 := ?_) ?_ ?_
      case refine_2 => run_fn [c0, c1, c2]; rfl
      refine runs_done ⟨⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      all_goals try dsimp only
      · mem_region
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
        simp only [Adler32.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, BitVec.reduceAdd] at hx' hmod'
        first | rfl | mem_away
      · exact hAcc0
      · exact hReq0
      · skip
        · first | (apply Adler32.Mid.small_small <;> mem_auto) | (apply Adler32.Mid.small_large <;> mem_auto) | (apply Adler32.Mid.large_small <;> mem_auto) | (apply Adler32.Mid.large_large <;> mem_auto)
      · exact BitVec.lt_def.mp (by bv_decide)
  · by_cases hs2 : (b + ((a + ((mem.read (input + i) 8).getD 0#64)) - 65521#64)) < 65521#64
    · have c0 : (i).ult (n) = true := by bv_decide
      try simp (disch := mem_auto) only [read8_cell, Option.getD_some, add_sub_lit, BitVec.add_assoc] at c0
      have c1 : ((a + ((mem.read (input + i) 8).getD 0#64))).ult (65521#64) = false := by bv_decide
      try simp (disch := mem_auto) only [read8_cell, Option.getD_some, add_sub_lit, BitVec.add_assoc] at c1
      have c2 : ((b + ((a + ((mem.read (input + i) 8).getD 0#64)) - 65521#64))).ult (65521#64) = true := by bv_decide
      try simp (disch := mem_auto) only [read8_cell, Option.getD_some, add_sub_lit, BitVec.add_assoc] at c2
      refine runs_then (a := 29) (s1 := ?_) ?_ ?_
      case refine_2 => run_fn [c0, c1, c2]; rfl
      refine runs_done ⟨⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      all_goals try dsimp only
      · mem_region
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
        simp only [Adler32.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, BitVec.reduceAdd] at hx' hmod'
        first | rfl | mem_away
      · exact hAcc0
      · exact hReq0
      · skip
        · first | (apply Adler32.Mid.small_small <;> mem_auto) | (apply Adler32.Mid.small_large <;> mem_auto) | (apply Adler32.Mid.large_small <;> mem_auto) | (apply Adler32.Mid.large_large <;> mem_auto)
      · exact BitVec.lt_def.mp (by bv_decide)
    · have c0 : (i).ult (n) = true := by bv_decide
      try simp (disch := mem_auto) only [read8_cell, Option.getD_some, add_sub_lit, BitVec.add_assoc] at c0
      have c1 : ((a + ((mem.read (input + i) 8).getD 0#64))).ult (65521#64) = false := by bv_decide
      try simp (disch := mem_auto) only [read8_cell, Option.getD_some, add_sub_lit, BitVec.add_assoc] at c1
      have c2 : ((b + ((a + ((mem.read (input + i) 8).getD 0#64)) - 65521#64))).ult (65521#64) = false := by bv_decide
      try simp (disch := mem_auto) only [read8_cell, Option.getD_some, add_sub_lit, BitVec.add_assoc] at c2
      refine runs_then (a := 31) (s1 := ?_) ?_ ?_
      case refine_2 => run_fn [c0, c1, c2]; rfl
      refine runs_done ⟨⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      all_goals try dsimp only
      · mem_region
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
        simp only [Adler32.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, BitVec.reduceAdd] at hx' hmod'
        first | rfl | mem_away
      · exact hAcc0
      · exact hReq0
      · skip
        · first | (apply Adler32.Mid.small_small <;> mem_auto) | (apply Adler32.Mid.small_large <;> mem_auto) | (apply Adler32.Mid.large_small <;> mem_auto) | (apply Adler32.Mid.large_large <;> mem_auto)
      · exact BitVec.lt_def.mp (by bv_decide)

theorem leave (fb input n ra : BitVec 64) (sv : Abi.Saved) (bytes : List (BitVec 8)) (m0 : Mem)
    (s : State) (hI : Inv fb input n ra sv bytes m0 s) (hc : ¬ s.r14 < n) :
    ∃ n_ s', steps Code_adler32.prog n_ s = some s' ∧ Abi.Post (Abi.Contract.framed (Adler32.contract input n bytes) 40#64) fb ra sv m0 s' := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, a, b, i, r15, zf, cf, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, mem, pc⟩ := s
  obtain ⟨hpc, hsp, hp0, hp1, hu0, hF, hRa, hS0, hS1, hS2, hS3, hS4, hAp, hOut, hAcc, hReq, hI0⟩ := hI
  simp only at hpc hsp hp0 hp1 hu0 hF hRa hS0 hS1 hS2 hS3 hS4 hOut hI0 hc
  subst pc rsp rbx rbp r15
  have hAp0 := hAp
  simp only [Adler32.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, Abi.AllApart, Abi.Apart, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, BitVec.reduceAdd] at hAp
  split_ands hAp
  have hAcc0 := hAcc
  try (simp only [Adler32.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true] at hAcc; split_ands hAcc)
  have hReq0 := hReq
  simp only [Adler32.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true] at hReq
  split_ands hReq
  forget_about m0 except hOut hReq0
  try (have hK0 := Adler32.Mid.cells (m := mem) (by assumption); split_ands hK0)
  have c0 : (i).ult (n) = false := by bv_decide
  try simp (disch := mem_auto) only [read8_cell, Option.getD_some, add_sub_lit, BitVec.add_assoc] at c0
  refine runs_then (a := 13) (s1 := ?_) ?_ ?_
  case refine_2 => run_fn [c0]; rfl
  refine runs_done ⟨rfl, by simp only [Adler32.contract, Abi.Contract.framed]; bv_decide, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  all_goals try dsimp only
  · intro x hx hmod
    refine Eq.trans ?_ (hOut x hx hmod)
    have hx' := hx
    have hmod' := hmod
    simp only [Adler32.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, BitVec.reduceAdd] at hx' hmod'
    first | rfl | mem_away
  · simp only [Adler32.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
    apply Adler32.exit <;> mem_auto

/-- **`adler32`, as assembled, meets its contract, whatever its arguments.** -/
theorem adler32_meets : ∀ (input n : BitVec 64) (bytes : List (BitVec 8)),
    Abi.Meets Code_adler32.prog 0x100000 (Adler32.contract input n bytes) := by
  intro input n bytes
  refine Abi.meets_of_triple 40#64 (by dsimp only [Adler32.contract]; decide) (by dsimp only [Adler32.contract]; decide) (fun fb ra sv m0 => ?_)
  refine Hoare.seq (Q := Inv fb input n ra sv bytes m0) ?_ ?_
  · intro s hP
    exact enter fb input n ra sv bytes m0 s hP
  · refine Hoare.loop (fun s => ((n - s.r14)).toNat) (fun s hI => ?_)
    by_cases hc : s.r14 < n
    · obtain ⟨n_, s', h, hi, hm⟩ := turn fb input n ra sv bytes m0 s hI hc
      exact ⟨n_, s', h, Or.inl ⟨hi, hm⟩⟩
    · obtain ⟨n_, s', h, hq⟩ := leave fb input n ra sv bytes m0 s hI hc
      exact ⟨n_, s', h, Or.inr hq⟩

#print axioms adler32_meets

end Proof_adler32
