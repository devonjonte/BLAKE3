import X86
import MemX
import Attr
open X86

/-! Running the x86-64 model on a state that is written out: every program's proofs use this. -/

theorem steps_mk (prog : Nat → Option (Instr × Nat)) (k : Nat) (rax rcx rdx rbx rsp rbp rsi rdi r8 r9 : BitVec 64)
    (zf cf : Option Bool) (mem : Mem) (pc : Nat) (leak : List Obs) :
    steps prog (k + 1) ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, zf, cf, mem, pc, leak⟩ =
      match prog pc with
      | none => none
      | some (i, next) => (step i next ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, zf, cf, mem, pc, leak⟩).bind (steps prog k) := rfl

theorem steps_zero (prog : Nat → Option (Instr × Nat)) (s : State) : steps prog 0 s = some s := rfl

theorem steps_add (prog : Nat → Option (Instr × Nat)) (a b : Nat) (s : State) :
    steps prog (a + b) s = (steps prog a s).bind (steps prog b) := by
  induction a generalizing s with
  | zero => simp [steps]
  | succ a ih =>
    rw [Nat.add_right_comm]
    simp only [steps]
    cases prog s.pc with
    | none => rfl
    | some x =>
      obtain ⟨i, next⟩ := x
      simp only []
      cases step i next s with
      | none => rfl
      | some s1 => simp only [Option.bind_some, ih]

/-- Run the instructions of a state that is written out. -/
macro "run_code" "[" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic|
  simp (config := {maxSteps := 10000000, implicitDefEqProofs := false}) only [steps_mk, steps_zero, step,
    X86.read, write, addr, State.get, State.set, trunc, logic, holds, done, touched, seen,
    List.nil_append, List.cons_append, List.append_nil, code_at,
    Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.map_some, bind_pure_comp,
    Nat.reduceEqDiff, ↓reduceIte, reduceCtorEq, $hs,*])
