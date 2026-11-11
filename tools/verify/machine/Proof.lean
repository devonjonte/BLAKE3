import X86
import Spec
import Code
import Sym

open X86

/-- What the library reads of a CPU, in the specification's terms. -/
def words (cpu : Cpu) : Detect.Cpu where
  leaf1_eax := cpu.leaf1.eax
  leaf1_ecx := cpu.leaf1.ecx
  xcr0 := cpu.xcr0.setWidth 32
  leaf7_ebx := cpu.leaf7.ebx
  -- "AuthenticAMD", as leaf 0 spells it over EBX, EDX, ECX.
  amd := cpu.leaf0.ebx == 0x68747541 && cpu.leaf0.edx == 0x69746E65 && cpu.leaf0.ecx == 0x444D4163

/-- A call of `read_x86_features`: any registers, the return address on the stack. -/
def entry (rax rcx rdx rbx rsp rbp rsi rdi : BitVec 64) : State :=
  { rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, zf := none, cf := none, mem := store [] rsp 0 64, pc := 0x1000 }

-- The model runs: an EPYC 9255 (Zen 5), a Xeon 6330 (Ice Lake), an EPYC 7443 (Zen 3), a Core 2.
def amd (l1a l1c l7b : BitVec 32) (x : BitVec 64) : Cpu :=
  ⟨⟨0, 0x68747541, 0x444D4163, 0x69746E65⟩, ⟨l1a, 0, l1c, 0⟩, ⟨0, l7b, 0, 0⟩, x⟩
def intel (l1a l1c l7b : BitVec 32) (x : BitVec 64) : Cpu :=
  ⟨⟨0, 0x756E6547, 0x6C65746E, 0x49656E69⟩, ⟨l1a, 0, l1c, 0⟩, ⟨0, l7b, 0, 0⟩, x⟩
def result (cpu : Cpu) : Option (BitVec 8 × BitVec 8) :=
  (run Code.prog cpu 100 (entry 1 2 3 4 0x7FFF0000 6 7 8)).map fun s => (s.rax.setWidth 8, Detect.features (words cpu))
#eval result (amd 0x00B00F21 0x7EDA320B 0xF1BF97A9 0xE7)
#eval result (intel 0x000606A6 0x7FFEFBFF 0xF3BFB7EF 0xE7)
#eval result (amd 0x00A00F11 0x7EDA320B 0x219C97A9 0x7)
#eval result (intel 0x000106A5 0x0098E3BD 0 0)

/-- What a caller sees when the function returns: AL, the stack pointer, and the registers the
calling convention says a function keeps. -/
def seen (s : State) : BitVec 8 × BitVec 64 × BitVec 64 × BitVec 64 := (s.rax.setWidth 8, s.rsp, s.rbx, s.rbp)

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
