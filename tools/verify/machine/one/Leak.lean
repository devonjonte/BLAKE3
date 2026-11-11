import Machine
import MemLemmas
import Code
import Run
open X86

/-! # What the one-block kernels show: the trace, on the same model

`Machine.lean` has no observer. Here one is added without changing the machine: `stepL` is the model's
own `step` with what it shows recorded beside it (the addresses the instruction reads or writes, and
where a jump, a call or a return goes), and `stepsL_core` says the recorded run is the model's run. So a
theorem about the trace is about the same executions as the theorems about the result. -/

/-- What an observer of time and cache may learn from one instruction. -/
inductive Obs
  | addr (a : BitVec 64)
  | pc (n : Nat)

def opObs (s : State) : Opnd → List Obs
  | .mem b d => [.addr (s.get b + d)]
  | _ => []

def srcObs (s : State) : Src → List Obs
  | .m b d => [.addr (s.get b + d)]
  | _ => []

/-- The addresses an instruction reads or writes, from the state before it. -/
def touched (s : State) : Instr → List Obs
  | .movv _ _ x | .paddd _ x | .pxor _ x | .por _ x | .pshufb _ x | .pshufd _ x _ | .shufps _ x _ | .pblendw _ x _
  | .punpcklqdq _ x | .punpckldq _ x | .punpckhdq _ x | .vpaddd _ _ x | .vpxor _ _ x | .vprord _ x _
  | .vshufps _ _ x _ | .vpblendd _ _ x _ | .vpunpcklqdq _ _ x | .vpunpckldq _ _ x | .vpunpckhdq _ _ x => srcObs s x
  | .storev _ b d _ => [.addr (s.get b + d)]
  | .movvi _ _ b i d => [.addr (s.get b + s.get i + d)]
  | .mov _ d x | .or _ d x | .add _ d x | .sub _ d x | .cmp _ d x | .and _ d x | .xor _ d x => opObs s d ++ opObs s x
  | .movzx8 _ x => opObs s x
  | .push _ | .call _ => [.addr (s.rsp - 8)]
  | .pop _ | .ret => [.addr s.rsp]
  | _ => []

/-- Instructions that choose where to go next: where they went is observed. -/
def branches : Instr → Bool
  | .je _ | .jne _ | .jbe _ | .jae _ | .jmp _ | .call _ | .ret => true
  | _ => false

/-- A state of the machine and what it has shown so far, newest first. -/
structure LState where
  core : State
  leak : List Obs

/-- The model's step, with what it shows recorded. -/
def stepL (i : Instr) (next : Nat) (s : LState) : Option LState :=
  (step i next s.core).map fun c => ⟨c, (if branches i then [Obs.pc c.pc] else []) ++ touched s.core i ++ s.leak⟩

def stepsL (prog : Nat → Option (Instr × Nat)) : Nat → LState → Option LState
  | 0, s => some s
  | k + 1, s =>
    match prog s.core.pc with
    | none => none
    | some (i, next) => (stepL i next s).bind (stepsL prog k)

/-- **The recorded run is the model's run.** -/
theorem stepsL_core (prog : Nat → Option (Instr × Nat)) : ∀ (k : Nat) (s : LState),
    (stepsL prog k s).map (·.core) = steps prog k s.core := by
  intro k
  induction k with
  | zero => intro s; rfl
  | succ k ih =>
    intro s
    simp only [stepsL, steps]
    cases prog s.core.pc with
    | none => rfl
    | some x =>
      obtain ⟨i, next⟩ := x
      simp only [stepL]
      cases step i next s.core with
      | none => rfl
      | some c => simp only [Option.map_some, Option.bind_some]; exact ih _

/-- What was seen before a run stays under what the run shows. -/
theorem stepsL_seen (prog : Nat → Option (Instr × Nat)) : ∀ (k : Nat) (c : State) (l seen : List Obs),
    stepsL prog k ⟨c, l ++ seen⟩ = (stepsL prog k ⟨c, l⟩).map fun S => ⟨S.core, S.leak ++ seen⟩ := by
  intro k
  induction k with
  | zero => intro c l seen; rfl
  | succ k ih =>
    intro c l seen
    simp only [stepsL]
    cases prog c.pc with
    | none => rfl
    | some x =>
      obtain ⟨i, next⟩ := x
      simp only [stepL]
      cases step i next c with
      | none => rfl
      | some c' =>
        simp only [Option.map_some, Option.bind_some]
        rw [← List.append_assoc, ih]

theorem stepsL_mk (prog : Nat → Option (Instr × Nat)) (k : Nat) (rax rcx rdx rbx rsp rbp rsi rdi r8 r9 r12 r13 r14 r15 : BitVec 64) (zf cf : Option Bool)
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : V) (mem : Mem) (pc : Nat) (leak : List Obs) :
    stepsL prog (k + 1) ⟨⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r12, r13, r14, r15, zf, cf, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, mem, pc⟩, leak⟩ =
      match prog pc with
      | none => none
      | some (i, next) => (stepL i next ⟨⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r12, r13, r14, r15, zf, cf, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, mem, pc⟩, leak⟩).bind (stepsL prog k) := rfl

theorem stepsL_zero (prog : Nat → Option (Instr × Nat)) (s : LState) : stepsL prog 0 s = some s := rfl

set_option maxRecDepth 100000 in
/-- Run the kernels' instructions with the observer, on a state that is written out. -/
macro "run_leak" "[" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic|
  simp (config := {maxSteps := 100000000, implicitDefEqProofs := false}) only [stepsL_mk, stepsL_zero, stepL, touched, srcObs, opObs, branches,
    step, src, X86.read, write, State.get, State.set, State.xmm, State.setx, trunc, al_of,
    Code.at_20000, Code.at_20003, Code.at_20007, Code.at_2000E, Code.at_20012, Code.at_20015, Code.at_2001A, Code.at_2001F, Code.at_20023, Code.at_20026, Code.at_2002A, Code.at_2002E, Code.at_20032, Code.at_20037, Code.at_2003B, Code.at_2003F, Code.at_20043, Code.at_20047, Code.at_2004B, Code.at_20050, Code.at_20055, Code.at_2005B, Code.at_20063, Code.at_2006B, Code.at_2006D, Code.at_20071, Code.at_20075, Code.at_20079, Code.at_2007F, Code.at_20083, Code.at_20087, Code.at_2008C, Code.at_20091, Code.at_20097, Code.at_2009C, Code.at_200A0, Code.at_200A4, Code.at_200A8, Code.at_200AE, Code.at_200B2, Code.at_200B6, Code.at_200BB, Code.at_200C0, Code.at_200C6, Code.at_200CB, Code.at_200D0, Code.at_200D5, Code.at_200DA, Code.at_200DE, Code.at_200E2, Code.at_200E6, Code.at_200EC, Code.at_200F0, Code.at_200F4, Code.at_200F9, Code.at_200FE, Code.at_20104, Code.at_20109, Code.at_2010D, Code.at_20111, Code.at_20115, Code.at_2011B, Code.at_2011F, Code.at_20123, Code.at_20128, Code.at_2012D, Code.at_20133, Code.at_20138, Code.at_2013D, Code.at_20142, Code.at_20147, Code.at_20149, Code.at_2014B, Code.at_20150, Code.at_20155, Code.at_2015B, Code.at_20161, Code.at_20166, Code.at_2016B, Code.at_20172, Code.at_20177, Code.at_2017C, Code.at_20183, Code.at_20189, Code.at_2018D, Code.at_20191, Code.at_20196, Code.at_2019B, Code.at_201A0, Code.at_201A5, Code.at_201A9, Code.at_201AD, Code.at_201B0, Code.at_201B4, Code.at_30000, Code.at_30004, Code.at_30009, Code.at_3000D, Code.at_30010, Code.at_30014, Code.at_30017, Code.at_3001C, Code.at_30021, Code.at_30025, Code.at_3002D, Code.at_30031, Code.at_30036, Code.at_3003C, Code.at_30042, Code.at_30047, Code.at_3004C, Code.at_30052, Code.at_30058, Code.at_3005D, Code.at_30062, Code.at_30064, Code.at_30068, Code.at_3006C, Code.at_30072, Code.at_30079, Code.at_3007D, Code.at_30083, Code.at_3008A, Code.at_3008E, Code.at_30092, Code.at_30098, Code.at_3009F, Code.at_300A3, Code.at_300A9, Code.at_300B0, Code.at_300B5, Code.at_300BA, Code.at_300BF, Code.at_300C3, Code.at_300C7, Code.at_300CD, Code.at_300D4, Code.at_300D8, Code.at_300DE, Code.at_300E5, Code.at_300E9, Code.at_300ED, Code.at_300F3, Code.at_300FA, Code.at_300FE, Code.at_30104, Code.at_3010B, Code.at_30110, Code.at_30115, Code.at_3011A, Code.at_3011C, Code.at_3011E, Code.at_30123, Code.at_30128, Code.at_3012E, Code.at_30133, Code.at_30139, Code.at_3013D, Code.at_30143, Code.at_30149, Code.at_3014D, Code.at_30151, Code.at_30156, Code.at_3015A, Code.at_3015E, Code.at_30163, Code.at_30167, Code.at_3016B, Code.at_3016F, Code.at_30174,
    Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.map_some, bind_pure_comp, Option.isSome_some,
    List.nil_append, List.cons_append, List.append_nil,
    Nat.reduceEqDiff, ↓reduceIte, reduceCtorEq, BitVec.reduceAdd, BitVec.reduceSub, BitVec.reduceEq, BitVec.reduceBEq,
    BitVec.reduceAnd, BitVec.reduceSetWidth, Bool.false_eq_true, Bool.true_eq_false, Bool.false_and, Bool.true_and,
    Bool.not_true, Bool.not_false, $hs,*])

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- **The SSE4.1 one-block kernel is constant-time.** There is a trace `L`, fixed by the three addresses the kernel is given (the chaining
value's, the block's, the stack pointer) and the address it returns to, such that every run of the kernel, whatever the chaining value,
the block, the counter, the length and the flags are, shows an observer exactly `L`: the addresses it
reads and writes and the way each jump goes. -/
theorem sse41_kernel_shows_only_addresses (rdi rsi rsp ra : BitVec 64) : ∃ L : List Obs, ∀ (s : State) (cv0 cv1 b0 b1 b2 b3 : V),
    s.pc = 0x20000 → s.rdi = rdi → s.rsi = rsi → s.rsp = rsp →
    Vec s.mem (s.rdi + 0) cv0 → Vec s.mem (s.rdi + 16) cv1 →
    Vec s.mem (s.rsi + 0) b0 → Vec s.mem (s.rsi + 16) b1 → Vec s.mem (s.rsi + 32) b2 → Vec s.mem (s.rsi + 48) b3 →
    s.mem.read s.rsp 64 = some ra → (∀ x, (x - s.rsp).toNat < 8 → 32 ≤ (x - s.rdi).toNat) →
    ∃ S, stepsL Code.prog 467 ⟨s, []⟩ = some S ∧ S.leak = L := by
  refine ⟨?L, ?_⟩
  rotate_left
  intro s cv0 cv1 b0 b1 b2 b3 hpc hdi hsi hsp hc0 hc1 hb0 hb1 hb2 hb3 hret hapart
  obtain ⟨rax, rcx, rdx, rbx, rsp_, rbp, rsi_, rdi_, r8, r9, r12, r13, r14, r15, zf, cf, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, mem, pc⟩ := s
  simp only at hpc hdi hsi hsp hc0 hc1 hb0 hb1 hb2 hb3 hret hapart
  subst pc rdi_ rsi_ rsp_
  have r0 := read_vec hc0
  have r1 := read_vec hc1
  have r2 := read_vec hb0
  have r3 := read_vec hb1
  have r4 := read_vec hb2
  have r5 := read_vec hb3
  have w0 : ∀ v : V, mem.write128 (rdi + 0) v = some (mem.put128 (rdi + 0) v) := fun v => write_vec (vec_owned hc0) v
  have w1 : ∀ v w : V, (mem.put128 (rdi + 0) v).write128 (rdi + 16) w = some ((mem.put128 (rdi + 0) v).put128 (rdi + 16) w) :=
    fun v w => write_vec (owned16_put128 _ _ _ _ (vec_owned hc1)) w
  have rr : ∀ v w : V, ((mem.put128 (rdi + 0) v).put128 (rdi + 16) w).read rsp 64 = some ra := by
    intro v w
    rw [read_congr (m := mem) _ (fun x hx => by
      have := hapart x hx
      rw [put128_other _ _ _ _ (by bv_omega), put128_other _ _ _ _ (by bv_omega)])]
    exact hret
  run_leak [r0, r1, r2, r3, r4, r5, w0, w1, rr]
  refine ⟨_, rfl, ?_⟩
  simp only []
  rfl


set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- **The AVX-512 one-block kernel is constant-time.** There is a trace `L`, fixed by the three addresses the kernel is given (the chaining
value's, the block's, the stack pointer) and the address it returns to, such that every run of the kernel, whatever the chaining value,
the block, the counter, the length and the flags are, shows an observer exactly `L`: the addresses it
reads and writes and the way each jump goes. -/
theorem avx512_kernel_shows_only_addresses (rdi rsi rsp ra : BitVec 64) : ∃ L : List Obs, ∀ (s : State) (cv0 cv1 b0 b1 b2 b3 : V),
    s.pc = 0x30000 → s.rdi = rdi → s.rsi = rsi → s.rsp = rsp →
    Vec s.mem (s.rdi + 0) cv0 → Vec s.mem (s.rdi + 16) cv1 →
    Vec s.mem (s.rsi + 0) b0 → Vec s.mem (s.rsi + 16) b1 → Vec s.mem (s.rsi + 32) b2 → Vec s.mem (s.rsi + 48) b3 →
    s.mem.read s.rsp 64 = some ra → (∀ x, (x - s.rsp).toNat < 8 → 32 ≤ (x - s.rdi).toNat) →
    ∃ S, stepsL Code.prog 362 ⟨s, []⟩ = some S ∧ S.leak = L := by
  refine ⟨?L, ?_⟩
  rotate_left
  intro s cv0 cv1 b0 b1 b2 b3 hpc hdi hsi hsp hc0 hc1 hb0 hb1 hb2 hb3 hret hapart
  obtain ⟨rax, rcx, rdx, rbx, rsp_, rbp, rsi_, rdi_, r8, r9, r12, r13, r14, r15, zf, cf, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, mem, pc⟩ := s
  simp only at hpc hdi hsi hsp hc0 hc1 hb0 hb1 hb2 hb3 hret hapart
  subst pc rdi_ rsi_ rsp_
  have r0 := read_vec hc0
  have r1 := read_vec hc1
  have r2 := read_vec hb0
  have r3 := read_vec hb1
  have r4 := read_vec hb2
  have r5 := read_vec hb3
  have w0 : ∀ v : V, mem.write128 (rdi + 0) v = some (mem.put128 (rdi + 0) v) := fun v => write_vec (vec_owned hc0) v
  have w1 : ∀ v w : V, (mem.put128 (rdi + 0) v).write128 (rdi + 16) w = some ((mem.put128 (rdi + 0) v).put128 (rdi + 16) w) :=
    fun v w => write_vec (owned16_put128 _ _ _ _ (vec_owned hc1)) w
  have rr : ∀ v w : V, ((mem.put128 (rdi + 0) v).put128 (rdi + 16) w).read rsp 64 = some ra := by
    intro v w
    rw [read_congr (m := mem) _ (fun x hx => by
      have := hapart x hx
      rw [put128_other _ _ _ _ (by bv_omega), put128_other _ _ _ _ (by bv_omega)])]
    exact hret
  run_leak [r0, r1, r2, r3, r4, r5, w0, w1, rr]
  refine ⟨_, rfl, ?_⟩
  simp only []
  rfl

#print axioms sse41_kernel_shows_only_addresses
#print axioms avx512_kernel_shows_only_addresses
