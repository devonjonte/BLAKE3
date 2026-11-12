import Cells
import Kernels
import AbiProof
import Spec_lroot
import Lemmas_lroot
import Code_lroot
open X86 Cells

/-! # `lroot`, as assembled, meets `Lroot.contract`

Written by prove_fn.py from levels.ode and the compiler's layout; not edited by hand, and not to be read
but for its last theorem's statement: Lean checks the rest. The frame: 176 bytes below the stack pointer at entry
(`fb` is its lowest address), the caller's rbx, rbp, r12, r13, r14, r15 at its top.
-/

namespace Proof_lroot

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option linter.unusedVariables false

/-- What holds each time the loop's head is reached: the source's `invariant` clauses, each variable where the
compiler keeps it, and the frame as the compiler keeps it. -/
def Inv (fb out lv key flags plat ra : BitVec 64) (sv : Abi.Saved) (k : Blake3.CV) (chunks : Array Blake3.Node) (m0 : Mem) (s : State) : Prop :=
  s.pc = 0xC006A ∧
  s.rsp = (fb + 8#64) ∧
  s.r13 = lv ∧
  s.r14 = key ∧
  s.r15 = plat ∧
  Region s.mem fb 176#64 ∧
  Quad s.mem (fb + 176#64) ra ∧
  Quad s.mem (fb + 168#64) sv.rbx ∧
  Quad s.mem (fb + 160#64) sv.rbp ∧
  Quad s.mem (fb + 152#64) sv.r12 ∧
  Quad s.mem (fb + 144#64) sv.r13 ∧
  Quad s.mem (fb + 136#64) sv.r14 ∧
  Quad s.mem (fb + 128#64) sv.r15 ∧
  Quad s.mem (fb + 104#64) out ∧
  Quad s.mem (fb + 112#64) flags ∧
  Abi.AllApart ((fb, (Abi.Contract.framed (Lroot.contract out lv key flags plat k chunks) 176#64).stack + 8#64) :: (Abi.Contract.framed (Lroot.contract out lv key flags plat k chunks) 176#64).regions) ∧
  (∀ x : BitVec 64, (Abi.Contract.framed (Lroot.contract out lv key flags plat k chunks) 176#64).stack + 8#64 ≤ x - fb → (∀ r ∈ (Abi.Contract.framed (Lroot.contract out lv key flags plat k chunks) 176#64).modifies, r.2 ≤ x - r.1) → s.mem x = m0 x) ∧
  (Abi.Contract.framed (Lroot.contract out lv key flags plat k chunks) 176#64).accepts ∧
  (Abi.Contract.framed (Lroot.contract out lv key flags plat k chunks) 176#64).requires m0 ∧
  Quad s.mem (fb + 120#64) (flags ||| 4#64) ∧
    Levels.Fold s.mem lv k flags chunks s.rbp s.rbx (fb + 72#64) ∧
    Cv.At s.mem key k ∧
    Region s.mem out 32#64

theorem enter (fb out lv key flags plat ra : BitVec 64) (sv : Abi.Saved) (k : Blake3.CV) (chunks : Array Blake3.Node) (m0 : Mem)
    (s : State) (hP : Abi.Pre 0xC0000 (Abi.Contract.framed (Lroot.contract out lv key flags plat k chunks) 176#64) fb ra sv m0 s) : ∃ n_ s', steps Code_lroot.prog n_ s = some s' ∧ Inv fb out lv key flags plat ra sv k chunks m0 s' := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r12, r13, r14, r15, zf, cf, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, mem, pc⟩ := s
  obtain ⟨hpc, hsp, hargs, hbx, hbp, h12, h13, h14, h15, hmem, hF, hRa, hAp, hAcc, hReq⟩ := hP
  simp only [Lroot.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true] at hpc hsp hargs hbx hbp h12 h13 h14 h15 hmem hF hRa
  simp only [List.length_cons, List.length_nil, List.take, List.cons.injEq, and_true] at hargs
  obtain ⟨ha0, ha1, ha2, ha3, ha4⟩ := hargs
  subst pc rsp rdi rsi rdx rcx r8 rbx rbp r12 r13 r14 r15 mem
  have hAp0 := hAp
  simp only [Lroot.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, Abi.AllApart, Abi.Apart, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, BitVec.reduceAdd] at hAp
  split_ands hAp
  have hAcc0 := hAcc
  try (simp only [Lroot.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true] at hAcc; split_ands hAcc)
  have hReq0 := hReq
  simp only [Lroot.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true] at hReq
  split_ands hReq
  try (have hK0 := Levels.Fold.cells (m := m0) (by assumption); split_ands hK0)
  try (have hK1 := Cv.At.cells (m := m0) (by assumption); split_ands hK1)
  try (have hK2 := Region.cells (m := m0) (by assumption); split_ands hK2)
  have_by hE0 := Levels.At.cell (m := m0)
  try norm_addr at hE0
  split_ands hE0
  have_by hO0 := Levels.At.newest (m := m0)
  obtain ⟨n0, n1, hO0⟩ := hO0
  try norm_addr at hO0
  split_ands hO0
  refine runs_then (a := 32) (s1 := ?_) ?_ ?_
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
    simp only [Lroot.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, BitVec.reduceAdd] at hx' hmod'
    first | rfl | mem_away
  · exact hAcc0
  · exact hReq0
  · skip
    refine ⟨?_, ?_, ?_, ?_⟩
    · mem_fact
    · apply Levels.Fold.start <;> mem_auto
    · first | mem_auto | (apply Cv.At.frame <;> mem_auto)
    · first | mem_auto | (apply Region.frame <;> mem_auto)

theorem turn (fb out lv key flags plat ra : BitVec 64) (sv : Abi.Saved) (k : Blake3.CV) (chunks : Array Blake3.Node) (m0 : Mem)
    (s : State) (hI : Inv fb out lv key flags plat ra sv k chunks m0 s) (hc : 0#64 < s.rbx) :
    ∃ n_ s', steps Code_lroot.prog n_ s = some s' ∧ (Inv fb out lv key flags plat ra sv k chunks m0 s' ∧ s'.rbx.toNat < s.rbx.toNat) := by
  obtain ⟨rax, rcx, rdx, e, rsp, base, rsi, rdi, r8, r9, f, r13, r14, r15, zf, cf, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, mem, pc⟩ := s
  obtain ⟨hpc, hsp, hp0, hp1, hp2, hF, hRa, hS0, hS1, hS2, hS3, hS4, hS5, hPs0, hPs1, hAp, hOut, hAcc, hReq, hZ0, hI0, hI1, hI2⟩ := hI
  simp only at hpc hsp hp0 hp1 hp2 hF hRa hS0 hS1 hS2 hS3 hS4 hS5 hPs0 hPs1 hOut hZ0 hI0 hI1 hI2 hc
  subst pc rsp r13 r14 r15
  have hAp0 := hAp
  simp only [Lroot.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, Abi.AllApart, Abi.Apart, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, BitVec.reduceAdd] at hAp
  split_ands hAp
  have hAcc0 := hAcc
  try (simp only [Lroot.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true] at hAcc; split_ands hAcc)
  have hReq0 := hReq
  simp only [Lroot.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true] at hReq
  split_ands hReq
  forget_about m0 except hOut hReq0
  try (have hK0 := Levels.Fold.cells (m := mem) (by assumption); split_ands hK0)
  try (have hK1 := Cv.At.cells (m := mem) (by assumption); split_ands hK1)
  try (have hK2 := Region.cells (m := mem) (by assumption); split_ands hK2)
  have_by hO0 := Cv.At.vectors (m := mem)
  obtain ⟨k0, k1, hO0⟩ := hO0
  try norm_addr at hO0
  split_ands hO0
  have_by hO1 := Levels.Fold.acc (m := mem)
  obtain ⟨a0, a1, hO1⟩ := hO1
  try norm_addr at hO1
  split_ands hO1
  by_cases hs1 : (e &&& 1#64) = 1#64
  · by_cases hs2 : e = 1#64
    · by_cases hs3 : plat = 5#64
      · have_by hO2 := Levels.Fold.level (m := mem)
        obtain ⟨l0, l1, hO2⟩ := hO2
        try norm_addr at hO2
        split_ands hO2
        have c0 : (0#64).ult (e) = true := by bv_decide
        have c1 : ((e &&& 1#64) - 1#64 == 0#64) = true := by bv_decide
        have c2 : (e - 1#64 == 0#64) = true := by bv_decide
        have c3 : (plat - 5#64 == 0#64) = true := by bv_decide
        refine runs_then (a := 47) (s1 := ?_) ?_ ?_
        case refine_2 => run_fn [c0, c1, c2, c3]; rfl
        refine Kernels.call_avx_runs Code_lroot.has_kernels (by mem_auto) (by mem_auto) (by mem_auto) (by mem_auto) (by mem_auto) (by mem_auto) (by mem_auto) (by mem_auto) ?_
        intro rax' rcx' rdx' rsi' rdi' r8' r9' zf' cf' y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15
        refine runs_then (a := 8) (s1 := ?_) ?_ ?_
        case refine_2 => run_fn [c0, c1, c2, c3]; rfl
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
          simp only [Lroot.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, BitVec.reduceAdd] at hx' hmod'
          first | rfl | mem_away
        · exact hAcc0
        · exact hReq0
        · skip
          refine ⟨?_, ?_, ?_, ?_⟩
          · mem_fact
          · first | (apply Levels.Fold.root <;> mem_auto) | (apply Levels.Fold.parent <;> mem_auto) | (apply Levels.Fold.skip <;> mem_auto)
          · first | mem_auto | (apply Cv.At.frame <;> mem_auto)
          · first | mem_auto | (apply Region.frame <;> mem_auto)
        · exact BitVec.lt_def.mp (by bv_decide)
      · have_by hO2 := Levels.Fold.level (m := mem)
        obtain ⟨l0, l1, hO2⟩ := hO2
        try norm_addr at hO2
        split_ands hO2
        have c0 : (0#64).ult (e) = true := by bv_decide
        have c1 : ((e &&& 1#64) - 1#64 == 0#64) = true := by bv_decide
        have c2 : (e - 1#64 == 0#64) = true := by bv_decide
        have c3 : (plat - 5#64 == 0#64) = false := by bv_decide
        refine runs_then (a := 47) (s1 := ?_) ?_ ?_
        case refine_2 => run_fn [c0, c1, c2, c3]; rfl
        refine Kernels.call_sse_runs Code_lroot.has_kernels (by mem_auto) (by mem_auto) (by mem_auto) (by mem_auto) (by mem_auto) (by mem_auto) (by mem_auto) (by mem_auto) (by mem_auto) (by mem_auto) ?_
        intro rax' rcx' rdx' rsi' rdi' r8' r9' zf' cf' y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15
        refine runs_then (a := 7) (s1 := ?_) ?_ ?_
        case refine_2 => run_fn [c0, c1, c2, c3]; rfl
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
          simp only [Lroot.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, BitVec.reduceAdd] at hx' hmod'
          first | rfl | mem_away
        · exact hAcc0
        · exact hReq0
        · skip
          refine ⟨?_, ?_, ?_, ?_⟩
          · mem_fact
          · first | (apply Levels.Fold.root <;> mem_auto) | (apply Levels.Fold.parent <;> mem_auto) | (apply Levels.Fold.skip <;> mem_auto)
          · first | mem_auto | (apply Cv.At.frame <;> mem_auto)
          · first | mem_auto | (apply Region.frame <;> mem_auto)
        · exact BitVec.lt_def.mp (by bv_decide)
    · by_cases hs3 : plat = 5#64
      · have_by hO2 := Levels.Fold.level (m := mem)
        obtain ⟨l0, l1, hO2⟩ := hO2
        try norm_addr at hO2
        split_ands hO2
        have c0 : (0#64).ult (e) = true := by bv_decide
        have c1 : ((e &&& 1#64) - 1#64 == 0#64) = true := by bv_decide
        have c2 : (e - 1#64 == 0#64) = false := by bv_decide
        have c3 : (plat - 5#64 == 0#64) = true := by bv_decide
        refine runs_then (a := 44) (s1 := ?_) ?_ ?_
        case refine_2 => run_fn [c0, c1, c2, c3]; rfl
        refine Kernels.call_avx_runs Code_lroot.has_kernels (by mem_auto) (by mem_auto) (by mem_auto) (by mem_auto) (by mem_auto) (by mem_auto) (by mem_auto) (by mem_auto) ?_
        intro rax' rcx' rdx' rsi' rdi' r8' r9' zf' cf' y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15
        refine runs_then (a := 8) (s1 := ?_) ?_ ?_
        case refine_2 => run_fn [c0, c1, c2, c3]; rfl
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
          simp only [Lroot.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, BitVec.reduceAdd] at hx' hmod'
          first | rfl | mem_away
        · exact hAcc0
        · exact hReq0
        · skip
          refine ⟨?_, ?_, ?_, ?_⟩
          · mem_fact
          · first | (apply Levels.Fold.root <;> mem_auto) | (apply Levels.Fold.parent <;> mem_auto) | (apply Levels.Fold.skip <;> mem_auto)
          · first | mem_auto | (apply Cv.At.frame <;> mem_auto)
          · first | mem_auto | (apply Region.frame <;> mem_auto)
        · exact BitVec.lt_def.mp (by bv_decide)
      · have_by hO2 := Levels.Fold.level (m := mem)
        obtain ⟨l0, l1, hO2⟩ := hO2
        try norm_addr at hO2
        split_ands hO2
        have c0 : (0#64).ult (e) = true := by bv_decide
        have c1 : ((e &&& 1#64) - 1#64 == 0#64) = true := by bv_decide
        have c2 : (e - 1#64 == 0#64) = false := by bv_decide
        have c3 : (plat - 5#64 == 0#64) = false := by bv_decide
        refine runs_then (a := 44) (s1 := ?_) ?_ ?_
        case refine_2 => run_fn [c0, c1, c2, c3]; rfl
        refine Kernels.call_sse_runs Code_lroot.has_kernels (by mem_auto) (by mem_auto) (by mem_auto) (by mem_auto) (by mem_auto) (by mem_auto) (by mem_auto) (by mem_auto) (by mem_auto) (by mem_auto) ?_
        intro rax' rcx' rdx' rsi' rdi' r8' r9' zf' cf' y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15
        refine runs_then (a := 7) (s1 := ?_) ?_ ?_
        case refine_2 => run_fn [c0, c1, c2, c3]; rfl
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
          simp only [Lroot.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, BitVec.reduceAdd] at hx' hmod'
          first | rfl | mem_away
        · exact hAcc0
        · exact hReq0
        · skip
          refine ⟨?_, ?_, ?_, ?_⟩
          · mem_fact
          · first | (apply Levels.Fold.root <;> mem_auto) | (apply Levels.Fold.parent <;> mem_auto) | (apply Levels.Fold.skip <;> mem_auto)
          · first | mem_auto | (apply Cv.At.frame <;> mem_auto)
          · first | mem_auto | (apply Region.frame <;> mem_auto)
        · exact BitVec.lt_def.mp (by bv_decide)
  · have c0 : (0#64).ult (e) = true := by bv_decide
    have c1 : ((e &&& 1#64) - 1#64 == 0#64) = false := by bv_decide
    refine runs_then (a := 16) (s1 := ?_) ?_ ?_
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
      simp only [Lroot.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, BitVec.reduceAdd] at hx' hmod'
      first | rfl | mem_away
    · exact hAcc0
    · exact hReq0
    · skip
      refine ⟨?_, ?_, ?_, ?_⟩
      · mem_fact
      · first | (apply Levels.Fold.root <;> mem_auto) | (apply Levels.Fold.parent <;> mem_auto) | (apply Levels.Fold.skip <;> mem_auto)
      · first | mem_auto | (apply Cv.At.frame <;> mem_auto)
      · first | mem_auto | (apply Region.frame <;> mem_auto)
    · exact BitVec.lt_def.mp (by bv_decide)

theorem leave (fb out lv key flags plat ra : BitVec 64) (sv : Abi.Saved) (k : Blake3.CV) (chunks : Array Blake3.Node) (m0 : Mem)
    (s : State) (hI : Inv fb out lv key flags plat ra sv k chunks m0 s) (hc : ¬ 0#64 < s.rbx) :
    ∃ n_ s', steps Code_lroot.prog n_ s = some s' ∧ Abi.Post (Abi.Contract.framed (Lroot.contract out lv key flags plat k chunks) 176#64) fb ra sv m0 s' := by
  obtain ⟨rax, rcx, rdx, e, rsp, base, rsi, rdi, r8, r9, f, r13, r14, r15, zf, cf, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, mem, pc⟩ := s
  obtain ⟨hpc, hsp, hp0, hp1, hp2, hF, hRa, hS0, hS1, hS2, hS3, hS4, hS5, hPs0, hPs1, hAp, hOut, hAcc, hReq, hZ0, hI0, hI1, hI2⟩ := hI
  simp only at hpc hsp hp0 hp1 hp2 hF hRa hS0 hS1 hS2 hS3 hS4 hS5 hPs0 hPs1 hOut hZ0 hI0 hI1 hI2 hc
  subst pc rsp r13 r14 r15
  have hAp0 := hAp
  simp only [Lroot.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, Abi.AllApart, Abi.Apart, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, BitVec.reduceAdd] at hAp
  split_ands hAp
  have hAcc0 := hAcc
  try (simp only [Lroot.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true] at hAcc; split_ands hAcc)
  have hReq0 := hReq
  simp only [Lroot.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true] at hReq
  split_ands hReq
  forget_about m0 except hOut hReq0
  try (have hK0 := Levels.Fold.cells (m := mem) (by assumption); split_ands hK0)
  try (have hK1 := Cv.At.cells (m := mem) (by assumption); split_ands hK1)
  try (have hK2 := Region.cells (m := mem) (by assumption); split_ands hK2)
  have_by hO0 := Levels.Fold.done (m := mem)
  obtain ⟨r0, r1, hO0⟩ := hO0
  try norm_addr at hO0
  split_ands hO0
  have c0 : (0#64).ult (e) = false := by bv_decide
  refine runs_then (a := 18) (s1 := ?_) ?_ ?_
  case refine_2 => run_fn [c0]; rfl
  refine runs_done ⟨rfl, by simp only [Lroot.contract, Abi.Contract.framed]; bv_decide, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  all_goals try dsimp only
  · intro x hx hmod
    refine Eq.trans ?_ (hOut x hx hmod)
    have hx' := hx
    have hmod' := hmod
    simp only [Lroot.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, BitVec.reduceAdd] at hx' hmod'
    first | rfl | mem_away
  · simp only [Lroot.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
    apply Lroot.exit <;> mem_auto

/-- **`lroot`, as assembled, meets its contract, whatever its arguments.** -/
theorem lroot_meets : ∀ (out lv key flags plat : BitVec 64) (k : Blake3.CV) (chunks : Array Blake3.Node),
    Abi.Meets Code_lroot.prog 0xC0000 (Lroot.contract out lv key flags plat k chunks) := by
  intro out lv key flags plat k chunks
  refine Abi.meets_of_triple 176#64 (by dsimp only [Lroot.contract]; decide) (by dsimp only [Lroot.contract]; decide) (fun fb ra sv m0 => ?_)
  refine Hoare.seq (Q := Inv fb out lv key flags plat ra sv k chunks m0) ?_ ?_
  · intro s hP
    exact enter fb out lv key flags plat ra sv k chunks m0 s hP
  · refine Hoare.loop (fun s => s.rbx.toNat) (fun s hI => ?_)
    by_cases hc : 0#64 < s.rbx
    · obtain ⟨n_, s', h, hi, hm⟩ := turn fb out lv key flags plat ra sv k chunks m0 s hI hc
      exact ⟨n_, s', h, Or.inl ⟨hi, hm⟩⟩
    · obtain ⟨n_, s', h, hq⟩ := leave fb out lv key flags plat ra sv k chunks m0 s hI hc
      exact ⟨n_, s', h, Or.inr hq⟩

#print axioms lroot_meets

end Proof_lroot
