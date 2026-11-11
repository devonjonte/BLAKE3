import A64

/-! `scan` of fold.rs as rustc 1.99.1 compiled it for AArch64 (opt-level s): its nine words, and what
the decoder makes of each. The listing in the comments is llvm-objdump's and is a hint: Lean checks each line. -/

namespace Code
open A64

def base : Nat := 0x1000

def image : List Nat := [0xB40000E1, 0xD37EF428, 0xB9400009, 0x4AC26D22, 0xB8004402, 0xF1001108, 0x54FFFF81, 0xAA0203E0, 0xD65F03C0]

def prog : Nat → Option Instr := at_ base image

theorem at_1000 : prog 0x1000 = some (.cbz .x1 0x101C) := by decide  -- b40000e1  cbz x1, +0x1c
theorem at_1004 : prog 0x1004 = some (.lsl .x8 .x1 2) := by decide  -- d37ef428  lsl x8, x1, #2
theorem at_1008 : prog 0x1008 = some (.ldr32 .x9 .x0 0) := by decide  -- b9400009  ldr w9, [x0]
theorem at_100C : prog 0x100C = some (.eor32ror .x2 .x9 .x2 27) := by decide  -- 4ac26d22  eor w2, w9, w2, ror #27
theorem at_1010 : prog 0x1010 = some (.str32post .x2 .x0 4) := by decide  -- b8004402  str w2, [x0], #0x4
theorem at_1014 : prog 0x1014 = some (.subs .x8 .x8 4) := by decide  -- f1001108  subs x8, x8, #0x4
theorem at_1018 : prog 0x1018 = some (.bne 0x1008) := by decide  -- 54ffff81  b.ne -0x10
theorem at_101C : prog 0x101C = some (.mov .x0 .x2) := by decide  -- aa0203e0  mov x0, x2
theorem at_1020 : prog 0x1020 = some (.ret) := by decide  -- d65f03c0  ret

end Code
