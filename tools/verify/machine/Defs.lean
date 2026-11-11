import X86
import Spec
import Code
import Sym

open X86

/-! What the theorem is stated with: a CPU in the specification's terms, a call of the function, what a
caller sees. Apart from the proof, so that a CPU the prover names as a counterexample can be run on
the model (`witness.py`). -/

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

/-- On this CPU, from one fixed set of registers: does the code return what the theorem says? Runs the
model; used to confirm a counterexample the prover names, not in any proof. -/
def agrees (cpu : Cpu) : Bool :=
  (run Code.prog cpu 100 (entry 1 2 3 4 0x7FFF0000 6 7 8)).map seen
    == some (Detect.features (words cpu), 0x7FFF0000 + 8, 4, 6)
