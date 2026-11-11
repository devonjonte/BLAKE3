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
    Code.at_25C0, Code.at_25C3, Code.at_25C7, Code.at_25CE, Code.at_25D2, Code.at_25D5, Code.at_25DA, Code.at_25DF, Code.at_25E3, Code.at_25E6, Code.at_25EA, Code.at_25EE, Code.at_25F2, Code.at_25F7, Code.at_25FB, Code.at_25FF, Code.at_2603, Code.at_2607, Code.at_260B, Code.at_2610, Code.at_2615, Code.at_261B, Code.at_2623, Code.at_262B, Code.at_262D, Code.at_2631, Code.at_2635, Code.at_2639, Code.at_263F, Code.at_2643, Code.at_2647, Code.at_264C, Code.at_2651, Code.at_2657, Code.at_265C, Code.at_2660, Code.at_2664, Code.at_2668, Code.at_266E, Code.at_2672, Code.at_2676, Code.at_267B, Code.at_2680, Code.at_2686, Code.at_268B, Code.at_2690, Code.at_2695, Code.at_269A, Code.at_269E, Code.at_26A2, Code.at_26A6, Code.at_26AC, Code.at_26B0, Code.at_26B4, Code.at_26B9, Code.at_26BE, Code.at_26C4, Code.at_26C9, Code.at_26CD, Code.at_26D1, Code.at_26D5, Code.at_26DB, Code.at_26DF, Code.at_26E3, Code.at_26E8, Code.at_26ED, Code.at_26F3, Code.at_26F8, Code.at_26FD, Code.at_2702, Code.at_2707, Code.at_2709, Code.at_270B, Code.at_2710, Code.at_2715, Code.at_271B, Code.at_2721, Code.at_2726, Code.at_272B, Code.at_2732, Code.at_2737, Code.at_273C, Code.at_2743, Code.at_2749, Code.at_274D, Code.at_2751, Code.at_2756, Code.at_275B, Code.at_2760, Code.at_2765, Code.at_2769, Code.at_276D, Code.at_2770, Code.at_2774,
    Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.map_some, bind_pure_comp, Option.isSome_some,
    Nat.reduceEqDiff, ↓reduceIte, reduceCtorEq, BitVec.reduceAdd, BitVec.reduceSub, BitVec.reduceEq, BitVec.reduceBEq,
    Bool.false_eq_true, Bool.true_eq_false])

/-- The same, with facts about this state. -/
macro "run_kernel_with" "[" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic|
  simp (config := {maxSteps := 100000000, implicitDefEqProofs := false}) only [steps_mk, steps_zero, step, src,
    State.get, State.set, State.xmm, State.setx, al_of,
    Code.at_25C0, Code.at_25C3, Code.at_25C7, Code.at_25CE, Code.at_25D2, Code.at_25D5, Code.at_25DA, Code.at_25DF, Code.at_25E3, Code.at_25E6, Code.at_25EA, Code.at_25EE, Code.at_25F2, Code.at_25F7, Code.at_25FB, Code.at_25FF, Code.at_2603, Code.at_2607, Code.at_260B, Code.at_2610, Code.at_2615, Code.at_261B, Code.at_2623, Code.at_262B, Code.at_262D, Code.at_2631, Code.at_2635, Code.at_2639, Code.at_263F, Code.at_2643, Code.at_2647, Code.at_264C, Code.at_2651, Code.at_2657, Code.at_265C, Code.at_2660, Code.at_2664, Code.at_2668, Code.at_266E, Code.at_2672, Code.at_2676, Code.at_267B, Code.at_2680, Code.at_2686, Code.at_268B, Code.at_2690, Code.at_2695, Code.at_269A, Code.at_269E, Code.at_26A2, Code.at_26A6, Code.at_26AC, Code.at_26B0, Code.at_26B4, Code.at_26B9, Code.at_26BE, Code.at_26C4, Code.at_26C9, Code.at_26CD, Code.at_26D1, Code.at_26D5, Code.at_26DB, Code.at_26DF, Code.at_26E3, Code.at_26E8, Code.at_26ED, Code.at_26F3, Code.at_26F8, Code.at_26FD, Code.at_2702, Code.at_2707, Code.at_2709, Code.at_270B, Code.at_2710, Code.at_2715, Code.at_271B, Code.at_2721, Code.at_2726, Code.at_272B, Code.at_2732, Code.at_2737, Code.at_273C, Code.at_2743, Code.at_2749, Code.at_274D, Code.at_2751, Code.at_2756, Code.at_275B, Code.at_2760, Code.at_2765, Code.at_2769, Code.at_276D, Code.at_2770, Code.at_2774,
    Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.map_some, bind_pure_comp, Option.isSome_some,
    Nat.reduceEqDiff, ↓reduceIte, reduceCtorEq, BitVec.reduceAdd, BitVec.reduceSub, BitVec.reduceEq, BitVec.reduceBEq,
    Bool.false_eq_true, Bool.true_eq_false, $hs,*])

end Simd
