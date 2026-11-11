import Std.Tactic.BVDecide

/-! # Which BLAKE3-Servil kernels an x86-64 CPU may run: the rule

What the CPU reports, and the four answers the library takes from it. This file is the
specification: it is meant to be read against Intel's and AMD's manuals by someone who has
never seen the Rust. -/

namespace Detect

/-- What CPUID and XCR0 report, as the library reads them. -/
structure Cpu where
  /-- CPUID leaf 1, EAX: family, model, stepping. -/
  leaf1_eax : BitVec 32
  /-- CPUID leaf 1, ECX: feature bits. -/
  leaf1_ecx : BitVec 32
  /-- XCR0, low half: the register sets the operating system saves. -/
  xcr0 : BitVec 32
  /-- CPUID leaf 7 (subleaf 0), EBX: more feature bits. -/
  leaf7_ebx : BitVec 32
  /-- The vendor string is "AuthenticAMD". -/
  amd : Bool

/-- Bit `n` of a word. -/
abbrev bit (w : BitVec 32) (n : Nat) : Bool := w.getLsbD n

/-- The display family: the base family (EAX bits 8-11), plus the extended family (bits 20-27)
where the base is 15. (Intel SDM vol. 2A, CPUID; AMD CPUID specification.) -/
def family (c : Cpu) : BitVec 32 :=
  let base := (c.leaf1_eax >>> 8) &&& 0xF
  if base = 0xF then base + ((c.leaf1_eax >>> 20) &&& 0xFF) else base

/-- SSE4.1: leaf 1, ECX bit 19. -/
def sse41 (c : Cpu) : Bool := bit c.leaf1_ecx 19

/-- The CPU has XSAVE (26) and AVX (28), and the OS has enabled XGETBV (OSXSAVE, 27). -/
def osSavesAvx (c : Cpu) : Bool := bit c.leaf1_ecx 26 && bit c.leaf1_ecx 27 && bit c.leaf1_ecx 28

/-- AVX2: the OS saves XMM (XCR0 bit 1) and YMM (bit 2), and leaf 7 EBX bit 5. -/
def avx2 (c : Cpu) : Bool := osSavesAvx c && bit c.xcr0 1 && bit c.xcr0 2 && bit c.leaf7_ebx 5

/-- AVX-512 F and VL: the OS also saves the opmask registers (XCR0 bit 5) and both halves of
the ZMM state (6, 7); leaf 7 EBX bit 16 (F) and bit 31 (VL). -/
def avx512 (c : Cpu) : Bool :=
  osSavesAvx c && bit c.xcr0 1 && bit c.xcr0 2 && bit c.xcr0 5 && bit c.xcr0 6 && bit c.xcr0 7
    && bit c.leaf7_ebx 16 && bit c.leaf7_ebx 31

/-- The 32-lane kernels: AVX-512 on AMD from family 0x1A (Zen 5), where they were measured to pay. -/
def wide (c : Cpu) : Bool := avx512 c && c.amd && family c ≥ 0x1A

/-- The library's byte of answers: READ (128) always, SSE41 (2), AVX2 (4), AVX512 (8), WIDE (16). -/
def features (c : Cpu) : BitVec 8 :=
  128#8 ||| (if sse41 c then 2#8 else 0) ||| (if avx2 c then 4#8 else 0)
    ||| (if avx512 c then 8#8 else 0) ||| (if wide c then 16#8 else 0)

end Detect
