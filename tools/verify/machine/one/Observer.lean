import Machine
open X86

/-! # An observer beside the machine

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
  | .pand _ x | .paddb _ x | .pcmpgtb _ x | .punpcklbw _ x | .punpckhbw _ x
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

