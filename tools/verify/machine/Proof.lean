import X86
import Spec
import Code
import Sym
import Defs

open X86

/-- Run the program on the unknown state as far as it goes: every instruction whose address is
known, both ways at a branch. -/
macro "run_code" : tactic => `(tactic|
  simp (config := {maxSteps := 10000000, implicitDefEqProofs := false}) only [entry, Sym.run_mk, Sym.run_zero, step,
    X86.read, write, State.get, State.set, trunc, store, load, byteAt, byte, done, logic, holds, cpuidOf,
    code_at,
    Sym.join64, Sym.sub_lit, Sym.add_add, Sym.eq_add_add, Sym.eq_self_add, Sym.eq_add_self, Sym.run_ite, Sym.run_bite,
    Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.map_some, bind_pure_comp, List.lookup_cons, List.lookup_nil,
    Nat.reduceEqDiff, Nat.reduceMul, ↓reduceIte, BitVec.reduceAdd, BitVec.reduceNeg, BitVec.reduceEq, BitVec.reduceBEq,
    BitVec.reduceAnd, BitVec.reduceHShiftRight, BitVec.reduceSetWidth, BitVec.ofNat_eq_ofNat, BitVec.reduceHShiftLeft,
    BitVec.reduceOr, BitVec.reduceToNat, reduceCtorEq, beq_self_eq_true, Bool.not_false, Sym.map_ite,
    BitVec.xor_self, true_and, and_true, and_self])

/-- The two sides of the theorem, as bit-vector facts. -/
macro "to_bits" : tactic => `(tactic|
  simp only [seen, words, Detect.features, Detect.sse41, Detect.avx2, Detect.avx512, Detect.wide, Detect.osSavesAvx,
    Detect.family, Detect.bit, Option.map_some, Option.some.injEq, Prod.mk.injEq])

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **The compiled `read_x86_features` gives the rule's answer on every CPU.** From any registers,
the 84 instructions rustc and LLVM made of it (and of `read_cpu_words` and `_xgetbv`, which it
calls) run to their return within 100 steps without a fault: no read of memory they did not
write, no XGETBV the OS has not enabled, no CPUID leaf but 0, 1 and 7. They return in AL the
specification's byte for this CPU, with the stack pointer popped and RBX and RBP as they were. -/
theorem read_x86_features_is_the_rule (cpu : Cpu) (rax rcx rdx rbx rsp rbp rsi rdi : BitVec 64) :
    (run Code.prog cpu 100 (entry rax rcx rdx rbx rsp rbp rsi rdi)).map seen
      = some (Detect.features (words cpu), rsp + 8, rbx, rbp) := by
  run_code
  split
  · -- XSAVE, OSXSAVE or AVX is missing: neither function reads further.
    split
    · to_bits; bv_decide
    · split <;> (to_bits; bv_decide)
  · -- All three are there, so XGETBV is allowed: OSXSAVE is one of them.
    have osxsave : cpu.leaf1.ecx.getLsbD 27 = true := by bv_decide
    simp only [osxsave, ↓reduceIte]
    run_code
    split
    · to_bits; bv_decide
    · split <;> (to_bits; bv_decide)

#print axioms read_x86_features_is_the_rule
