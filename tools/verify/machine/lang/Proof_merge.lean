import Cells
import Kernels
import AbiProof
import Spec_merge
import StackBridge
import Code_merge
open X86 Cells

/-! # `merge`, as assembled, meets its statement `Merge.statement`

Written by prove_fn.py from hasher.ode and the compiler's layout; not edited by hand, and not to be read:
Lean checks that it proves the statement. The frame: 176 bytes below the stack pointer at entry (`fb` is its
lowest address), the caller's rbx, rbp, r12, r13, r14, r15 at its top.
-/

namespace Proof_merge

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option linter.unusedVariables false

/-- What holds each time the loop's head is reached: the source's `invariant` clauses, each variable where the
compiler keeps it, and the frame as the compiler keeps it. -/
def Inv (fb st key flags plat target ra : BitVec 64) (sv : Abi.Saved) (k : Blake3.CV) (cvs : List Blake3.CV) (m0 : Mem) (s : State) : Prop :=
  s.pc = 0x60032 ∧
  s.rsp = (fb + 8#64) ∧
  s.rbx = st ∧
  s.rbp = key ∧
  s.r12 = flags ∧
  s.r13 = plat ∧
  s.r14 = target ∧
  Region s.mem fb 176#64 ∧
  Quad s.mem (fb + 176#64) ra ∧
  Quad s.mem (fb + 168#64) sv.rbx ∧
  Quad s.mem (fb + 160#64) sv.rbp ∧
  Quad s.mem (fb + 152#64) sv.r12 ∧
  Quad s.mem (fb + 144#64) sv.r13 ∧
  Quad s.mem (fb + 136#64) sv.r14 ∧
  Quad s.mem (fb + 128#64) sv.r15 ∧
  Abi.AllApart ((fb, (Merge.contract st key flags plat target k cvs).stack + 8#64) :: (Merge.contract st key flags plat target k cvs).regions) ∧
  (∀ x : BitVec 64, (Merge.contract st key flags plat target k cvs).stack + 8#64 ≤ x - fb → (∀ r ∈ (Merge.contract st key flags plat target k cvs).modifies, r.2 ≤ x - r.1) → s.mem x = m0 x) ∧
  ∃ (es : Stack.Cvs) (es0 : Stack.Cvs) (k0 : V) (k1 : V) , Quad s.mem (fb + 104#64) (flags ||| 4#64) ∧
    1#64 ≤ target ∧
    flags < 256#64 ∧
    Stack.holds s.mem st s.r15 es ∧
    (Stack.merged k0 k1 (BitVec.setWidth 8 (flags ||| 4#64)) target es) = (Stack.merged k0 k1 (BitVec.setWidth 8 (flags ||| 4#64)) target es0) ∧
    Stack.Views es0 cvs ∧
    Cv.Is k0 k1 k ∧
    Vec s.mem key k0 ∧
    Vec s.mem (key + 16#64) k1

theorem enter (fb st key flags plat target ra : BitVec 64) (sv : Abi.Saved) (k : Blake3.CV) (cvs : List Blake3.CV) (m0 : Mem)
    (s : State) (hP : Abi.Pre 0x60000 (Merge.contract st key flags plat target k cvs) fb ra sv m0 s) : ∃ n_ s', steps Code_merge.prog n_ s = some s' ∧ Inv fb st key flags plat target ra sv k cvs m0 s' := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r12, r13, r14, r15, zf, cf, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, mem, pc⟩ := s
  obtain ⟨hpc, hsp, hargs, hbx, hbp, h12, h13, h14, h15, hmem, hF, hRa, hAp, hReq⟩ := hP
  simp only [Merge.contract] at hpc hsp hargs hbx hbp h12 h13 h14 h15 hmem hF hRa hReq
  simp only [List.length_cons, List.length_nil, List.take, List.cons.injEq, and_true] at hargs
  obtain ⟨ha0, ha1, ha2, ha3, ha4⟩ := hargs
  subst pc rsp rdi rsi rdx rcx r8 rbx rbp r12 r13 r14 r15 mem
  split_ands hReq
  obtain ⟨len0, es0, hE0⟩ := Stack.holds_of_at (by assumption)
  split_ands hE0
  obtain ⟨k0, k1, hE1⟩ := Cv.vectors (by assumption)
  split_ands hE1
  have hAp0 := hAp
  simp only [Merge.contract, Abi.AllApart, Abi.Apart, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, BitVec.reduceAdd] at hAp
  split_ands hAp
  have hK0 := Stack.cells (by assumption)
  split_ands hK0
  refine runs_then (a := 18) (s1 := ?_) ?_ ?_
  case refine_2 => run_fn []; rfl
  refine runs_done ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
    simp only [Merge.contract, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, BitVec.reduceAdd] at hx' hmod'
    first | rfl | mem_away
  · apply Exists.intro; apply Exists.intro; apply Exists.intro; apply Exists.intro
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · mem_fact
    · first | rfl | mem_auto | (apply Stack.frame <;> mem_auto)
    · first | rfl | mem_auto | (apply Stack.frame <;> mem_auto)
    · first | rfl | mem_auto | (apply Stack.frame <;> mem_auto)
    · first | rfl | mem_auto | (apply Stack.frame <;> mem_auto)
    · first | rfl | mem_auto | (apply Stack.frame <;> mem_auto)
    · first | rfl | mem_auto | (apply Stack.frame <;> mem_auto)
    · first | rfl | mem_auto | (apply Stack.frame <;> mem_auto)
    · first | rfl | mem_auto | (apply Stack.frame <;> mem_auto)

theorem turn (fb st key flags plat target ra : BitVec 64) (sv : Abi.Saved) (k : Blake3.CV) (cvs : List Blake3.CV) (m0 : Mem)
    (s : State) (hI : Inv fb st key flags plat target ra sv k cvs m0 s) (hc : target < s.r15) :
    ∃ n_ s', steps Code_merge.prog n_ s = some s' ∧ (Inv fb st key flags plat target ra sv k cvs m0 s' ∧ s'.r15.toNat < s.r15.toNat) := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r12, r13, r14, len, zf, cf, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, mem, pc⟩ := s
  obtain ⟨hpc, hsp, hp0, hp1, hp2, hp3, hp4, hF, hRa, hS0, hS1, hS2, hS3, hS4, hS5, hAp, hOut, es, es0, k0, k1, hZ0, hI0, hI1, hI2, hI3, hI4, hI5, hI6, hI7⟩ := hI
  simp only at hpc hsp hp0 hp1 hp2 hp3 hp4 hF hRa hS0 hS1 hS2 hS3 hS4 hS5 hOut hZ0 hI2 hI6 hI7 hc
  subst pc rsp rbx rbp r12 r13 r14
  have hAp0 := hAp
  simp only [Merge.contract, Abi.AllApart, Abi.Apart, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, BitVec.reduceAdd] at hAp
  split_ands hAp
  have hK0 := Stack.cells (by assumption)
  split_ands hK0
  obtain ⟨r0, r1, l0, l1, rest, hEq, hO⟩ := Stack.open2 (by assumption) (by bv_decide)
  subst hEq
  norm_addr at hO
  split_ands hO
  have as0 : (BitVec.setWidth 32 (flags ||| 4#64)) = (BitVec.setWidth 32 (BitVec.setWidth 8 (flags ||| 4#64))) := by bv_decide
  by_cases hs2 : plat = 5#64
  · have c0 : (target).ult (len) = true := by bv_decide
    have c1 : (len).ult (2#64) = false := by bv_decide
    have c2 : (plat - 5#64 == 0#64) = true := by bv_decide
    refine runs_then (a := 45) (s1 := ?_) ?_ ?_
    case refine_2 => run_fn [c0, c1, c2, as0]; rfl
    refine Kernels.call_avx_runs Code_merge.has_kernels (by mem_auto) (by mem_auto) (by mem_auto) (by mem_auto) (by mem_auto) (by mem_auto) (by mem_auto) (by mem_auto) ?_
    intro rax' rcx' rdx' rsi' rdi' r8' r9' zf' cf' y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15
    refine runs_then (a := 14) (s1 := ?_) ?_ ?_
    case refine_2 => run_fn [c0, c1, c2, as0]; rfl
    refine runs_done ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
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
      simp only [Merge.contract, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, BitVec.reduceAdd] at hx' hmod'
      first | rfl | mem_away
    · apply Exists.intro; apply Exists.intro; apply Exists.intro; apply Exists.intro
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · mem_fact
      · first | rfl | mem_auto | (apply Stack.frame <;> mem_auto)
      · first | rfl | mem_auto | (apply Stack.frame <;> mem_auto)
      · apply Stack.close_merge <;> mem_auto
      · apply Stack.merged_turn <;> mem_auto
      · first | rfl | mem_auto | (apply Stack.frame <;> mem_auto)
      · first | rfl | mem_auto | (apply Stack.frame <;> mem_auto)
      · first | rfl | mem_auto | (apply Stack.frame <;> mem_auto)
      · first | rfl | mem_auto | (apply Stack.frame <;> mem_auto)
    · exact BitVec.lt_def.mp (by bv_decide)
  · have c0 : (target).ult (len) = true := by bv_decide
    have c1 : (len).ult (2#64) = false := by bv_decide
    have c2 : (plat - 5#64 == 0#64) = false := by bv_decide
    refine runs_then (a := 45) (s1 := ?_) ?_ ?_
    case refine_2 => run_fn [c0, c1, c2, as0]; rfl
    refine Kernels.call_sse_runs Code_merge.has_kernels (by mem_auto) (by mem_auto) (by mem_auto) (by mem_auto) (by mem_auto) (by mem_auto) (by mem_auto) (by mem_auto) (by mem_auto) ?_
    intro rax' rcx' rdx' rsi' rdi' r8' r9' zf' cf' y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15
    refine runs_then (a := 13) (s1 := ?_) ?_ ?_
    case refine_2 => run_fn [c0, c1, c2, as0]; rfl
    refine runs_done ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
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
      simp only [Merge.contract, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, BitVec.reduceAdd] at hx' hmod'
      first | rfl | mem_away
    · apply Exists.intro; apply Exists.intro; apply Exists.intro; apply Exists.intro
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · mem_fact
      · first | rfl | mem_auto | (apply Stack.frame <;> mem_auto)
      · first | rfl | mem_auto | (apply Stack.frame <;> mem_auto)
      · apply Stack.close_merge <;> mem_auto
      · apply Stack.merged_turn <;> mem_auto
      · first | rfl | mem_auto | (apply Stack.frame <;> mem_auto)
      · first | rfl | mem_auto | (apply Stack.frame <;> mem_auto)
      · first | rfl | mem_auto | (apply Stack.frame <;> mem_auto)
      · first | rfl | mem_auto | (apply Stack.frame <;> mem_auto)
    · exact BitVec.lt_def.mp (by bv_decide)

theorem leave (fb st key flags plat target ra : BitVec 64) (sv : Abi.Saved) (k : Blake3.CV) (cvs : List Blake3.CV) (m0 : Mem)
    (s : State) (hI : Inv fb st key flags plat target ra sv k cvs m0 s) (hc : ¬ target < s.r15) :
    ∃ n_ s', steps Code_merge.prog n_ s = some s' ∧ Abi.Post (Merge.contract st key flags plat target k cvs) fb ra sv m0 s' := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r12, r13, r14, len, zf, cf, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, mem, pc⟩ := s
  obtain ⟨hpc, hsp, hp0, hp1, hp2, hp3, hp4, hF, hRa, hS0, hS1, hS2, hS3, hS4, hS5, hAp, hOut, es, es0, k0, k1, hZ0, hI0, hI1, hI2, hI3, hI4, hI5, hI6, hI7⟩ := hI
  simp only at hpc hsp hp0 hp1 hp2 hp3 hp4 hF hRa hS0 hS1 hS2 hS3 hS4 hS5 hOut hZ0 hI2 hI6 hI7 hc
  subst pc rsp rbx rbp r12 r13 r14
  have hAp0 := hAp
  simp only [Merge.contract, Abi.AllApart, Abi.Apart, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, BitVec.reduceAdd] at hAp
  split_ands hAp
  have hK0 := Stack.cells (by assumption)
  split_ands hK0
  have c0 : (target).ult (len) = false := by bv_decide
  refine runs_then (a := 13) (s1 := ?_) ?_ ?_
  case refine_2 => run_fn [c0]; rfl
  refine runs_done ⟨rfl, by dsimp only [Merge.contract]; bv_decide, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  all_goals try dsimp only
  · intro x hx hmod
    refine Eq.trans ?_ (hOut x hx hmod)
    have hx' := hx
    have hmod' := hmod
    simp only [Merge.contract, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, BitVec.reduceAdd] at hx' hmod'
    first | rfl | mem_away
  · dsimp only [Merge.contract]
    apply Merge.exit <;> mem_auto

/-- **`merge`, as assembled, meets its statement.** -/
theorem merge_meets : Merge.statement := by
  intro st key flags plat target k cvs
  refine Abi.meets_of_triple (fun fb ra sv m0 => ?_)
  refine Hoare.seq (Q := Inv fb st key flags plat target ra sv k cvs m0) ?_ ?_
  · intro s hP
    exact enter fb st key flags plat target ra sv k cvs m0 s hP
  · refine Hoare.loop (fun s => s.r15.toNat) (fun s hI => ?_)
    by_cases hc : target < s.r15
    · obtain ⟨n_, s', h, hi, hm⟩ := turn fb st key flags plat target ra sv k cvs m0 s hI hc
      exact ⟨n_, s', h, Or.inl ⟨hi, hm⟩⟩
    · obtain ⟨n_, s', h, hq⟩ := leave fb st key flags plat target ra sv k cvs m0 s hI hc
      exact ⟨n_, s', h, Or.inr hq⟩

#print axioms merge_meets

end Proof_merge
