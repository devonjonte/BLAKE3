import Cells
import Kernels
import AbiProof
import Spec_ladd
import Lemmas_ladd
import Code_ladd
open X86 Cells

/-! # `ladd`, as assembled, meets `Ladd.contract`

Written by prove_fn.py from levels.ode and the compiler's layout; not edited by hand, and not to be read
but for its last theorem's statement: Lean checks the rest. The frame: 96 bytes below the stack pointer at entry
(`fb` is its lowest address), the caller's rbx, rbp, r12, r13, r14, r15 at its top.
-/

namespace Proof_ladd

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option linter.unusedVariables false

/-- What holds each time the loop's head is reached: the source's `invariant` clauses, each variable where the
compiler keeps it, and the frame as the compiler keeps it. -/
def Inv (fb lv key flags plat cv ra : BitVec 64) (sv : Abi.Saved) (k : Blake3.CV) (chunks : Array Blake3.Node) (new : Blake3.Node) (m0 : Mem) (s : State) : Prop :=
  s.pc = 0xB005A ∧
  s.rsp = (fb + 8#64) ∧
  s.r12 = lv ∧
  s.r13 = key ∧
  s.r14 = plat ∧
  Region s.mem fb 96#64 ∧
  Quad s.mem (fb + 96#64) ra ∧
  Quad s.mem (fb + 88#64) sv.rbx ∧
  Quad s.mem (fb + 80#64) sv.rbp ∧
  Quad s.mem (fb + 72#64) sv.r12 ∧
  Quad s.mem (fb + 64#64) sv.r13 ∧
  Quad s.mem (fb + 56#64) sv.r14 ∧
  Quad s.mem (fb + 48#64) sv.r15 ∧
  Quad s.mem (fb + 8#64) flags ∧
  Quad s.mem (fb + 16#64) cv ∧
  Abi.AllApart ((fb, (Abi.Contract.framed (Ladd.contract lv key flags plat cv k chunks new) 96#64).stack + 8#64) :: (Abi.Contract.framed (Ladd.contract lv key flags plat cv k chunks new) 96#64).regions) ∧
  (∀ x : BitVec 64, (Abi.Contract.framed (Ladd.contract lv key flags plat cv k chunks new) 96#64).stack + 8#64 ≤ x - fb → (∀ r ∈ (Abi.Contract.framed (Ladd.contract lv key flags plat cv k chunks new) 96#64).modifies, r.2 ≤ x - r.1) → s.mem x = m0 x) ∧
  (Abi.Contract.framed (Ladd.contract lv key flags plat cv k chunks new) 96#64).accepts ∧
  (Abi.Contract.framed (Ladd.contract lv key flags plat cv k chunks new) 96#64).requires m0 ∧
  Quad s.mem (fb + 24#64) (flags ||| 4#64) ∧
    Quad s.mem (fb + 32#64) (Levels.count chunks) ∧
    Levels.Mid s.mem lv k flags chunks s.rbp s.rbx ∧
    Cv.At s.mem key k ∧
    Ladd.New s.mem cv new

theorem enter (fb lv key flags plat cv ra : BitVec 64) (sv : Abi.Saved) (k : Blake3.CV) (chunks : Array Blake3.Node) (new : Blake3.Node) (m0 : Mem)
    (s : State) (hP : Abi.Pre 0xB0000 (Abi.Contract.framed (Ladd.contract lv key flags plat cv k chunks new) 96#64) fb ra sv m0 s) : ∃ n_ s', steps Code_ladd.prog n_ s = some s' ∧ Inv fb lv key flags plat cv ra sv k chunks new m0 s' := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r12, r13, r14, r15, zf, cf, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, mem, pc⟩ := s
  obtain ⟨hpc, hsp, hargs, hbx, hbp, h12, h13, h14, h15, hmem, hF, hRa, hAp, hAcc, hReq⟩ := hP
  simp only [Ladd.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true] at hpc hsp hargs hbx hbp h12 h13 h14 h15 hmem hF hRa
  simp only [List.length_cons, List.length_nil, List.take, List.cons.injEq, and_true] at hargs
  obtain ⟨ha0, ha1, ha2, ha3, ha4⟩ := hargs
  subst pc rsp rdi rsi rdx rcx r8 rbx rbp r12 r13 r14 r15 mem
  have hAp0 := hAp
  simp only [Ladd.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, Abi.AllApart, Abi.Apart, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, BitVec.reduceAdd] at hAp
  split_ands hAp
  have hAcc0 := hAcc
  try (simp only [Ladd.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true] at hAcc; split_ands hAcc)
  have hReq0 := hReq
  simp only [Ladd.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true] at hReq
  split_ands hReq
  try (have hK0 := Levels.Mid.cells (m := m0) (by assumption); split_ands hK0)
  try (have hK1 := Cv.At.cells (m := m0) (by assumption); split_ands hK1)
  try (have hK2 := Ladd.New.cells (m := m0) (by assumption); split_ands hK2)
  have_by hE0 := Levels.At.start (m := m0)
  try norm_addr at hE0
  split_ands hE0
  have_by hE1 := Ladd.New.intro (m := m0)
  try norm_addr at hE1
  split_ands hE1
  refine runs_then (a := 27) (s1 := ?_) ?_ ?_
  case refine_2 => run_fn []; rfl
  refine runs_done ⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try dsimp only
  · mem_region
  · mem_fact
  · mem_fact
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
    simp only [Ladd.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, BitVec.reduceAdd] at hx' hmod'
    first | rfl | mem_away
  · exact hAcc0
  · exact hReq0
  · skip
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · mem_fact
    · mem_fact
    · first | mem_auto | (apply Levels.Mid.frame <;> mem_auto)
    · first | mem_auto | (apply Cv.At.frame <;> mem_auto)
    · first | mem_auto | (apply Ladd.New.frame <;> mem_auto)

theorem turn (fb lv key flags plat cv ra : BitVec 64) (sv : Abi.Saved) (k : Blake3.CV) (chunks : Array Blake3.Node) (new : Blake3.Node) (m0 : Mem)
    (s : State) (hI : Inv fb lv key flags plat cv ra sv k chunks new m0 s) (hc : (s.rbx &&& 1#64) = 0#64) :
    ∃ n_ s', steps Code_ladd.prog n_ s = some s' ∧ (Inv fb lv key flags plat cv ra sv k chunks new m0 s' ∧ s'.rbx.toNat < s.rbx.toNat) := by
  obtain ⟨rax, rcx, rdx, x, rsp, src, rsi, rdi, r8, r9, r12, r13, r14, r15, zf, cf, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, mem, pc⟩ := s
  obtain ⟨hpc, hsp, hp0, hp1, hp2, hF, hRa, hS0, hS1, hS2, hS3, hS4, hS5, hPs0, hPs1, hAp, hOut, hAcc, hReq, hZ0, hZ1, hI0, hI1, hI2⟩ := hI
  simp only at hpc hsp hp0 hp1 hp2 hF hRa hS0 hS1 hS2 hS3 hS4 hS5 hPs0 hPs1 hOut hZ0 hZ1 hI0 hI1 hI2 hc
  subst pc rsp r12 r13 r14
  have hAp0 := hAp
  simp only [Ladd.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, Abi.AllApart, Abi.Apart, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, BitVec.reduceAdd] at hAp
  split_ands hAp
  have hAcc0 := hAcc
  try (simp only [Ladd.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true] at hAcc; split_ands hAcc)
  have hReq0 := hReq
  simp only [Ladd.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true] at hReq
  split_ands hReq
  forget_about m0 except hOut hReq0
  try (have hK0 := Levels.Mid.cells (m := mem) (by assumption); split_ands hK0)
  try (have hK1 := Cv.At.cells (m := mem) (by assumption); split_ands hK1)
  try (have hK2 := Ladd.New.cells (m := mem) (by assumption); split_ands hK2)
  have_by hO0 := Levels.Mid.full (m := mem)
  obtain ⟨l0, l1, r0, r1, hO0⟩ := hO0
  try norm_addr at hO0
  split_ands hO0
  have_by hO1 := Cv.At.vectors (m := mem)
  obtain ⟨k0, k1, hO1⟩ := hO1
  try norm_addr at hO1
  split_ands hO1
  by_cases hs1 : plat = 5#64
  · have c0 : ((x &&& 1#64) - 0#64 == 0#64) = true := by bv_decide
    have c1 : (plat - 5#64 == 0#64) = true := by bv_decide
    refine runs_then (a := 32) (s1 := ?_) ?_ ?_
    case refine_2 => run_fn [c0, c1]; rfl
    refine Kernels.call_avx_runs Code_ladd.has_kernels (by mem_auto) (by mem_auto) (by mem_auto) (by mem_auto) (by mem_auto) (by mem_auto) (by mem_auto) (by mem_auto) ?_
    intro rax' rcx' rdx' rsi' rdi' r8' r9' zf' cf' y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15
    refine runs_then (a := 5) (s1 := ?_) ?_ ?_
    case refine_2 => run_fn [c0, c1]; rfl
    refine runs_done ⟨⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    all_goals try dsimp only
    · mem_region
    · mem_fact
    · mem_fact
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
      simp only [Ladd.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, BitVec.reduceAdd] at hx' hmod'
      first | rfl | mem_away
    · exact hAcc0
    · exact hReq0
    · skip
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · mem_fact
      · mem_fact
      · apply Levels.Mid.carry <;> mem_auto
      · first | mem_auto | (apply Cv.At.frame <;> mem_auto)
      · first | mem_auto | (apply Ladd.New.frame <;> mem_auto)
    · exact BitVec.lt_def.mp (by bv_decide)
  · have c0 : ((x &&& 1#64) - 0#64 == 0#64) = true := by bv_decide
    have c1 : (plat - 5#64 == 0#64) = false := by bv_decide
    refine runs_then (a := 32) (s1 := ?_) ?_ ?_
    case refine_2 => run_fn [c0, c1]; rfl
    refine Kernels.call_sse_runs Code_ladd.has_kernels (by mem_auto) (by mem_auto) (by mem_auto) (by mem_auto) (by mem_auto) (by mem_auto) (by mem_auto) (by mem_auto) (by mem_auto) (by mem_auto) ?_
    intro rax' rcx' rdx' rsi' rdi' r8' r9' zf' cf' y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15
    refine runs_then (a := 4) (s1 := ?_) ?_ ?_
    case refine_2 => run_fn [c0, c1]; rfl
    refine runs_done ⟨⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    all_goals try dsimp only
    · mem_region
    · mem_fact
    · mem_fact
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
      simp only [Ladd.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, BitVec.reduceAdd] at hx' hmod'
      first | rfl | mem_away
    · exact hAcc0
    · exact hReq0
    · skip
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · mem_fact
      · mem_fact
      · apply Levels.Mid.carry <;> mem_auto
      · first | mem_auto | (apply Cv.At.frame <;> mem_auto)
      · first | mem_auto | (apply Ladd.New.frame <;> mem_auto)
    · exact BitVec.lt_def.mp (by bv_decide)

theorem leave (fb lv key flags plat cv ra : BitVec 64) (sv : Abi.Saved) (k : Blake3.CV) (chunks : Array Blake3.Node) (new : Blake3.Node) (m0 : Mem)
    (s : State) (hI : Inv fb lv key flags plat cv ra sv k chunks new m0 s) (hc : ¬ (s.rbx &&& 1#64) = 0#64) :
    ∃ n_ s', steps Code_ladd.prog n_ s = some s' ∧ Abi.Post (Abi.Contract.framed (Ladd.contract lv key flags plat cv k chunks new) 96#64) fb ra sv m0 s' := by
  obtain ⟨rax, rcx, rdx, x, rsp, src, rsi, rdi, r8, r9, r12, r13, r14, r15, zf, cf, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, mem, pc⟩ := s
  obtain ⟨hpc, hsp, hp0, hp1, hp2, hF, hRa, hS0, hS1, hS2, hS3, hS4, hS5, hPs0, hPs1, hAp, hOut, hAcc, hReq, hZ0, hZ1, hI0, hI1, hI2⟩ := hI
  simp only at hpc hsp hp0 hp1 hp2 hF hRa hS0 hS1 hS2 hS3 hS4 hS5 hPs0 hPs1 hOut hZ0 hZ1 hI0 hI1 hI2 hc
  subst pc rsp r12 r13 r14
  have hAp0 := hAp
  simp only [Ladd.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, Abi.AllApart, Abi.Apart, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, BitVec.reduceAdd] at hAp
  split_ands hAp
  have hAcc0 := hAcc
  try (simp only [Ladd.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true] at hAcc; split_ands hAcc)
  have hReq0 := hReq
  simp only [Ladd.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true] at hReq
  split_ands hReq
  forget_about m0 except hOut hReq0
  try (have hK0 := Levels.Mid.cells (m := mem) (by assumption); split_ands hK0)
  try (have hK1 := Cv.At.cells (m := mem) (by assumption); split_ands hK1)
  try (have hK2 := Ladd.New.cells (m := mem) (by assumption); split_ands hK2)
  have_by hO0 := Ladd.New.vectors (m := mem)
  obtain ⟨t0, t1, hO0⟩ := hO0
  try norm_addr at hO0
  split_ands hO0
  have c0 : ((x &&& 1#64) - 0#64 == 0#64) = false := by bv_decide
  refine runs_then (a := 30) (s1 := ?_) ?_ ?_
  case refine_2 => run_fn [c0]; rfl
  refine runs_done ⟨rfl, by simp only [Ladd.contract, Abi.Contract.framed]; bv_decide, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  all_goals try dsimp only
  · intro x hx hmod
    refine Eq.trans ?_ (hOut x hx hmod)
    have hx' := hx
    have hmod' := hmod
    simp only [Ladd.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, BitVec.reduceAdd] at hx' hmod'
    first | rfl | mem_away
  · simp only [Ladd.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
    apply Ladd.exit <;> mem_auto

/-- **`ladd`, as assembled, meets its contract, whatever its arguments.** -/
theorem ladd_meets : ∀ (lv key flags plat cv : BitVec 64) (k : Blake3.CV) (chunks : Array Blake3.Node) (new : Blake3.Node),
    Abi.Meets Code_ladd.prog 0xB0000 (Ladd.contract lv key flags plat cv k chunks new) := by
  intro lv key flags plat cv k chunks new
  refine Abi.meets_of_triple 96#64 (by dsimp only [Ladd.contract]; decide) (by dsimp only [Ladd.contract]; decide) (fun fb ra sv m0 => ?_)
  refine Hoare.seq (Q := Inv fb lv key flags plat cv ra sv k chunks new m0) ?_ ?_
  · intro s hP
    exact enter fb lv key flags plat cv ra sv k chunks new m0 s hP
  · refine Hoare.loop (fun s => s.rbx.toNat) (fun s hI => ?_)
    by_cases hc : (s.rbx &&& 1#64) = 0#64
    · obtain ⟨n_, s', h, hi, hm⟩ := turn fb lv key flags plat cv ra sv k chunks new m0 s hI hc
      exact ⟨n_, s', h, Or.inl ⟨hi, hm⟩⟩
    · obtain ⟨n_, s', h, hq⟩ := leave fb lv key flags plat cv ra sv k chunks new m0 s hI hc
      exact ⟨n_, s', h, Or.inr hq⟩

#print axioms ladd_meets

end Proof_ladd
