import Simd
import Code
open Simd

/-! Running the kernel on unknown inputs. -/

namespace Simd

theorem steps_mk (prog : Nat → Option (Instr × Nat)) (k : Nat) (rax rcx rdx rsi rdi r8 rsp : BitVec 64) (zf : Option Bool)
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : V) (mem : BitVec 64 → Option V) (ra pc : Nat) :
    steps prog (k + 1) ⟨rax, rcx, rdx, rsi, rdi, r8, rsp, zf, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, mem, ra, pc⟩ =
      match prog pc with
      | none => none
      | some (i, next) => (step i next ⟨rax, rcx, rdx, rsi, rdi, r8, rsp, zf, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, mem, ra, pc⟩).bind (steps prog k) := rfl

theorem steps_zero (prog : Nat → Option (Instr × Nat)) (s : State) : steps prog 0 s = some s := rfl

/-- AL after a byte is put in it. -/
theorem al_of (x : BitVec 64) (v : BitVec 8) : BitVec.setWidth 8 (x &&& ~~~(255 : BitVec 64) ||| BitVec.setWidth 64 v) = v := by
  bv_decide

/-- Run the instructions of a state that is written out; the vector operations stay as they are named. -/
macro "run_kernel" : tactic => `(tactic|
  simp (config := {maxSteps := 100000000, implicitDefEqProofs := false}) only [steps_mk, steps_zero, step, src,
    State.get, State.set, State.xmm, State.setx, al_of,
    Code.at_3700, Code.at_3704, Code.at_3709, Code.at_370D, Code.at_3710, Code.at_3714, Code.at_3717, Code.at_371C, Code.at_3721, Code.at_3725, Code.at_372D, Code.at_3731, Code.at_3736, Code.at_373C, Code.at_3742, Code.at_3747, Code.at_374C, Code.at_3752, Code.at_3758, Code.at_375D, Code.at_3762, Code.at_3764, Code.at_3768, Code.at_376C, Code.at_3772, Code.at_3779, Code.at_377D, Code.at_3783, Code.at_378A, Code.at_378E, Code.at_3792, Code.at_3798, Code.at_379F, Code.at_37A3, Code.at_37A9, Code.at_37B0, Code.at_37B5, Code.at_37BA, Code.at_37BF, Code.at_37C3, Code.at_37C7, Code.at_37CD, Code.at_37D4, Code.at_37D8, Code.at_37DE, Code.at_37E5, Code.at_37E9, Code.at_37ED, Code.at_37F3, Code.at_37FA, Code.at_37FE, Code.at_3804, Code.at_380B, Code.at_3810, Code.at_3815, Code.at_381A, Code.at_381C, Code.at_381E, Code.at_3823, Code.at_3828, Code.at_382E, Code.at_3833, Code.at_3839, Code.at_383D, Code.at_3843, Code.at_3849, Code.at_384D, Code.at_3851, Code.at_3856, Code.at_385A, Code.at_385E, Code.at_3863, Code.at_3867, Code.at_386B, Code.at_386F, Code.at_3874,
    Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.map_some, bind_pure_comp, Option.isSome_some,
    Nat.reduceEqDiff, ↓reduceIte, reduceCtorEq, BitVec.reduceAdd, BitVec.reduceSub, BitVec.reduceEq, BitVec.reduceBEq,
    Bool.false_eq_true, Bool.true_eq_false])

/-- The same, with facts about this state. -/
macro "run_kernel_with" "[" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic|
  simp (config := {maxSteps := 100000000, implicitDefEqProofs := false}) only [steps_mk, steps_zero, step, src,
    State.get, State.set, State.xmm, State.setx, al_of,
    Code.at_3700, Code.at_3704, Code.at_3709, Code.at_370D, Code.at_3710, Code.at_3714, Code.at_3717, Code.at_371C, Code.at_3721, Code.at_3725, Code.at_372D, Code.at_3731, Code.at_3736, Code.at_373C, Code.at_3742, Code.at_3747, Code.at_374C, Code.at_3752, Code.at_3758, Code.at_375D, Code.at_3762, Code.at_3764, Code.at_3768, Code.at_376C, Code.at_3772, Code.at_3779, Code.at_377D, Code.at_3783, Code.at_378A, Code.at_378E, Code.at_3792, Code.at_3798, Code.at_379F, Code.at_37A3, Code.at_37A9, Code.at_37B0, Code.at_37B5, Code.at_37BA, Code.at_37BF, Code.at_37C3, Code.at_37C7, Code.at_37CD, Code.at_37D4, Code.at_37D8, Code.at_37DE, Code.at_37E5, Code.at_37E9, Code.at_37ED, Code.at_37F3, Code.at_37FA, Code.at_37FE, Code.at_3804, Code.at_380B, Code.at_3810, Code.at_3815, Code.at_381A, Code.at_381C, Code.at_381E, Code.at_3823, Code.at_3828, Code.at_382E, Code.at_3833, Code.at_3839, Code.at_383D, Code.at_3843, Code.at_3849, Code.at_384D, Code.at_3851, Code.at_3856, Code.at_385A, Code.at_385E, Code.at_3863, Code.at_3867, Code.at_386B, Code.at_386F, Code.at_3874,
    Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.map_some, bind_pure_comp, Option.isSome_some,
    Nat.reduceEqDiff, ↓reduceIte, reduceCtorEq, BitVec.reduceAdd, BitVec.reduceSub, BitVec.reduceEq, BitVec.reduceBEq,
    Bool.false_eq_true, Bool.true_eq_false, $hs,*])

end Simd
