import Cells
import Kernels
import StackSpec
import Code_merge
open X86 Cells

/-! # `merge`, as assembled, meets the contract its source states

Written by prove_fn.py from the clauses in hasher.ode and the compiler's layout; not edited by hand.
The frame: 176 bytes below the stack pointer at entry (`fb` is its lowest address), the caller's rbx, rbp, r12, r13, r14, r15 at its top.
-/

namespace Proof_merge

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option linter.unusedVariables false

/-- What a caller owes: the `requires` clauses about memory, and the machine at the function's first instruction. -/
def Pre (fb st key flags plat target ra sv_rbx sv_rbp sv_r12 sv_r13 sv_r14 sv_r15 : BitVec 64) (es0 : Stack.Cvs) (k0 : V) (k1 : V) (len0 : BitVec 64) (m0 : Mem) (s : State) : Prop :=
  s.pc = 0x60000 ∧
  s.rsp = fb + 176#64 ∧
  s.rdi = st ∧
  s.rsi = key ∧
  s.rdx = flags ∧
  s.rcx = plat ∧
  s.r8 = target ∧
  s.rbx = sv_rbx ∧
  s.rbp = sv_rbp ∧
  s.r12 = sv_r12 ∧
  s.r13 = sv_r13 ∧
  s.r14 = sv_r14 ∧
  s.r15 = sv_r15 ∧
  s.mem = m0 ∧
  Region m0 fb 176#64 ∧
  Quad m0 (fb + 176#64) ra ∧
  Stack.holds m0 st len0 es0 ∧
  Vec m0 key k0 ∧
  Vec m0 (key + 16#64) k1

/-- What holds each time the loop's head is reached: the `invariant` clauses, each variable where the
compiler keeps it, and the frame as the compiler keeps it. -/
def Inv (fb st key flags plat target ra sv_rbx sv_rbp sv_r12 sv_r13 sv_r14 sv_r15 : BitVec 64) (es0 : Stack.Cvs) (k0 : V) (k1 : V) (len0 : BitVec 64) (m0 : Mem) (s : State) : Prop :=
  s.pc = 0x60032 ∧
  s.rsp = (fb + 8#64) ∧
  s.rbx = st ∧
  s.rbp = key ∧
  s.r12 = flags ∧
  s.r13 = plat ∧
  s.r14 = target ∧
  Region s.mem fb 176#64 ∧
  Quad s.mem (fb + 176#64) ra ∧
  Quad s.mem (fb + 168#64) sv_rbx ∧
  Quad s.mem (fb + 160#64) sv_rbp ∧
  Quad s.mem (fb + 152#64) sv_r12 ∧
  Quad s.mem (fb + 144#64) sv_r13 ∧
  Quad s.mem (fb + 136#64) sv_r14 ∧
  Quad s.mem (fb + 128#64) sv_r15 ∧
  (∀ x : BitVec 64, 184#64 ≤ x - fb → 1792#64 ≤ x - st → s.mem x = m0 x) ∧
  ∃ (es : Stack.Cvs) , Quad s.mem (fb + 104#64) (flags ||| 4#64) ∧
    Stack.holds s.mem st s.r15 es ∧
    (Stack.merged k0 k1 (BitVec.setWidth 8 (flags ||| 4#64)) target es) = (Stack.merged k0 k1 (BitVec.setWidth 8 (flags ||| 4#64)) target es0) ∧
    Vec s.mem key k0 ∧
    Vec s.mem (key + 16#64) k1

/-- What the caller gets: the `ensures` clauses, its registers and stack pointer back, and no byte changed
outside the frame and what the function may modify. -/
def Post (fb st key flags plat target ra sv_rbx sv_rbp sv_r12 sv_r13 sv_r14 sv_r15 : BitVec 64) (es0 : Stack.Cvs) (k0 : V) (k1 : V) (len0 : BitVec 64) (m0 : Mem) (s : State) : Prop :=
  s.pc = ra.toNat ∧
  s.rsp = fb + 184#64 ∧
  s.rbx = sv_rbx ∧
  s.rbp = sv_rbp ∧
  s.r12 = sv_r12 ∧
  s.r13 = sv_r13 ∧
  s.r14 = sv_r14 ∧
  s.r15 = sv_r15 ∧
  (∀ x : BitVec 64, 184#64 ≤ x - fb → 1792#64 ≤ x - st → s.mem x = m0 x) ∧
  Stack.holds s.mem st s.rax (Stack.merged k0 k1 (BitVec.setWidth 8 (flags ||| 4#64)) target es0)

theorem enter (fb st key flags plat target ra sv_rbx sv_rbp sv_r12 sv_r13 sv_r14 sv_r15 : BitVec 64) (es0 : Stack.Cvs) (k0 : V) (k1 : V) (len0 : BitVec 64) (m0 : Mem) (hq0 : 1#64 ≤ target) (hq1 : flags < 256#64) (ap_fb_st : 184#64 ≤ st - fb ∧ 1792#64 ≤ fb - st) (ap_fb_key : 184#64 ≤ key - fb ∧ 32#64 ≤ fb - key) (ap_st_key : 1792#64 ≤ key - st ∧ 32#64 ≤ st - key)
    (s : State) (hP : Pre fb st key flags plat target ra sv_rbx sv_rbp sv_r12 sv_r13 sv_r14 sv_r15 es0 k0 k1 len0 m0 s) : ∃ k s', steps Code_merge.prog k s = some s' ∧ Inv fb st key flags plat target ra sv_rbx sv_rbp sv_r12 sv_r13 sv_r14 sv_r15 es0 k0 k1 len0 m0 s' := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r12, r13, r14, r15, zf, cf, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, mem, pc⟩ := s
  obtain ⟨hpc, hsp, ha0, ha1, ha2, ha3, ha4, hv0, hv1, hv2, hv3, hv4, hv5, hmem, hF, hRa, hR0, hR1, hR2⟩ := hP
  simp only at hpc hsp ha0 ha1 ha2 ha3 ha4 hv0 hv1 hv2 hv3 hv4 hv5 hmem
  subst pc rsp rdi rsi rdx rcx r8 rbx rbp r12 r13 r14 r15 mem
  have hR0c := Stack.cells hR0
  split_ands hR0c
  refine runs_then (a := 18) (s1 := ?_) ?_ ?_
  case refine_2 => run_fn []; rfl
  refine runs_done ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals dsimp only
  · mem_region
  · mem_fact
  · mem_fact
  · mem_fact
  · mem_fact
  · mem_fact
  · mem_fact
  · mem_fact
  · intro x hx0 hx1
    mem_away
  · apply Exists.intro
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · mem_fact
    · first | rfl | mem_auto | (apply Stack.frame <;> mem_auto)
    · first | rfl | mem_auto | (apply Stack.frame <;> mem_auto)
    · first | rfl | mem_auto | (apply Stack.frame <;> mem_auto)
    · first | rfl | mem_auto | (apply Stack.frame <;> mem_auto)

theorem turn (fb st key flags plat target ra sv_rbx sv_rbp sv_r12 sv_r13 sv_r14 sv_r15 : BitVec 64) (es0 : Stack.Cvs) (k0 : V) (k1 : V) (len0 : BitVec 64) (m0 : Mem) (hq0 : 1#64 ≤ target) (hq1 : flags < 256#64) (ap_fb_st : 184#64 ≤ st - fb ∧ 1792#64 ≤ fb - st) (ap_fb_key : 184#64 ≤ key - fb ∧ 32#64 ≤ fb - key) (ap_st_key : 1792#64 ≤ key - st ∧ 32#64 ≤ st - key)
    (s : State) (hI : Inv fb st key flags plat target ra sv_rbx sv_rbp sv_r12 sv_r13 sv_r14 sv_r15 es0 k0 k1 len0 m0 s) (hc : target < s.r15) :
    ∃ k s', steps Code_merge.prog k s = some s' ∧ (Inv fb st key flags plat target ra sv_rbx sv_rbp sv_r12 sv_r13 sv_r14 sv_r15 es0 k0 k1 len0 m0 s' ∧ s'.r15.toNat < s.r15.toNat) := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r12, r13, r14, len, zf, cf, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, mem, pc⟩ := s
  obtain ⟨hpc, hsp, hp0, hp1, hp2, hp3, hp4, hF, hRa, hS0, hS1, hS2, hS3, hS4, hS5, hOut, es, hZ0, hI0, hI1, hI2, hI3⟩ := hI
  simp only at hpc hsp hp0 hp1 hp2 hp3 hp4 hF hRa hS0 hS1 hS2 hS3 hS4 hS5 hOut hZ0 hI0 hI1 hI2 hI3 hc
  subst pc rsp rbx rbp r12 r13 r14
  have hI0c := Stack.cells hI0
  split_ands hI0c
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
    refine runs_done ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    all_goals dsimp only
    · mem_region
    · mem_fact
    · mem_fact
    · mem_fact
    · mem_fact
    · mem_fact
    · mem_fact
    · mem_fact
    · intro x hx0 hx1
      refine Eq.trans ?_ (hOut x hx0 hx1)
      mem_away
    · apply Exists.intro
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · mem_fact
      · apply Stack.close_merge <;> mem_auto
      · apply Stack.merged_turn <;> mem_auto
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
    refine runs_done ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    all_goals dsimp only
    · mem_region
    · mem_fact
    · mem_fact
    · mem_fact
    · mem_fact
    · mem_fact
    · mem_fact
    · mem_fact
    · intro x hx0 hx1
      refine Eq.trans ?_ (hOut x hx0 hx1)
      mem_away
    · apply Exists.intro
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · mem_fact
      · apply Stack.close_merge <;> mem_auto
      · apply Stack.merged_turn <;> mem_auto
      · first | rfl | mem_auto | (apply Stack.frame <;> mem_auto)
      · first | rfl | mem_auto | (apply Stack.frame <;> mem_auto)
    · exact BitVec.lt_def.mp (by bv_decide)

theorem leave (fb st key flags plat target ra sv_rbx sv_rbp sv_r12 sv_r13 sv_r14 sv_r15 : BitVec 64) (es0 : Stack.Cvs) (k0 : V) (k1 : V) (len0 : BitVec 64) (m0 : Mem) (hq0 : 1#64 ≤ target) (hq1 : flags < 256#64) (ap_fb_st : 184#64 ≤ st - fb ∧ 1792#64 ≤ fb - st) (ap_fb_key : 184#64 ≤ key - fb ∧ 32#64 ≤ fb - key) (ap_st_key : 1792#64 ≤ key - st ∧ 32#64 ≤ st - key)
    (s : State) (hI : Inv fb st key flags plat target ra sv_rbx sv_rbp sv_r12 sv_r13 sv_r14 sv_r15 es0 k0 k1 len0 m0 s) (hc : ¬ target < s.r15) :
    ∃ k s', steps Code_merge.prog k s = some s' ∧ Post fb st key flags plat target ra sv_rbx sv_rbp sv_r12 sv_r13 sv_r14 sv_r15 es0 k0 k1 len0 m0 s' := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r12, r13, r14, len, zf, cf, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, mem, pc⟩ := s
  obtain ⟨hpc, hsp, hp0, hp1, hp2, hp3, hp4, hF, hRa, hS0, hS1, hS2, hS3, hS4, hS5, hOut, es, hZ0, hI0, hI1, hI2, hI3⟩ := hI
  simp only at hpc hsp hp0 hp1 hp2 hp3 hp4 hF hRa hS0 hS1 hS2 hS3 hS4 hS5 hOut hZ0 hI0 hI1 hI2 hI3 hc
  subst pc rsp rbx rbp r12 r13 r14
  have hI0c := Stack.cells hI0
  split_ands hI0c
  have c0 : (target).ult (len) = false := by bv_decide
  refine runs_then (a := 13) (s1 := ?_) ?_ ?_
  case refine_2 => run_fn [c0]; rfl
  refine runs_done ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  all_goals dsimp only
  · intro x hx0 hx1
    refine Eq.trans ?_ (hOut x hx0 hx1)
    first | rfl | mem_away
  · apply Stack.merged_exit <;> mem_auto

/-- **`merge`, as assembled, meets its contract.** From any state at its first instruction where the `requires`
clauses hold (and the frame's 176 bytes are owned and apart from the regions the contract names), the
93 instructions run without a fault, through however many turns of the loop, to the caller's return
address, where the `ensures` clauses hold. -/
theorem merge_meets_its_contract (fb st key flags plat target ra sv_rbx sv_rbp sv_r12 sv_r13 sv_r14 sv_r15 : BitVec 64) (es0 : Stack.Cvs) (k0 : V) (k1 : V) (len0 : BitVec 64) (m0 : Mem) (hq0 : 1#64 ≤ target) (hq1 : flags < 256#64) (ap_fb_st : 184#64 ≤ st - fb ∧ 1792#64 ≤ fb - st) (ap_fb_key : 184#64 ≤ key - fb ∧ 32#64 ≤ fb - key) (ap_st_key : 1792#64 ≤ key - st ∧ 32#64 ≤ st - key) :
    Hoare.Triple Code_merge.prog (Pre fb st key flags plat target ra sv_rbx sv_rbp sv_r12 sv_r13 sv_r14 sv_r15 es0 k0 k1 len0 m0) (Post fb st key flags plat target ra sv_rbx sv_rbp sv_r12 sv_r13 sv_r14 sv_r15 es0 k0 k1 len0 m0) := by
  refine Hoare.seq (Q := Inv fb st key flags plat target ra sv_rbx sv_rbp sv_r12 sv_r13 sv_r14 sv_r15 es0 k0 k1 len0 m0) ?_ ?_
  · intro s hP
    exact enter fb st key flags plat target ra sv_rbx sv_rbp sv_r12 sv_r13 sv_r14 sv_r15 es0 k0 k1 len0 m0 hq0 hq1 ap_fb_st ap_fb_key ap_st_key s hP
  · refine Hoare.loop (fun s => s.r15.toNat) (fun s hI => ?_)
    by_cases hc : target < s.r15
    · obtain ⟨k, s', h, hi, hm⟩ := turn fb st key flags plat target ra sv_rbx sv_rbp sv_r12 sv_r13 sv_r14 sv_r15 es0 k0 k1 len0 m0 hq0 hq1 ap_fb_st ap_fb_key ap_st_key s hI hc
      exact ⟨k, s', h, Or.inl ⟨hi, hm⟩⟩
    · obtain ⟨k, s', h, hq⟩ := leave fb st key flags plat target ra sv_rbx sv_rbp sv_r12 sv_r13 sv_r14 sv_r15 es0 k0 k1 len0 m0 hq0 hq1 ap_fb_st ap_fb_key ap_st_key s hI hc
      exact ⟨k, s', h, Or.inr hq⟩

#print axioms merge_meets_its_contract

end Proof_merge
