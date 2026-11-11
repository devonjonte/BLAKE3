import Machine

/-! `blake3_servil_core::hasher::parent_output::<blake3_servil_core::platform::Platform>`, as llvm-objdump reads it, placed at 0x10000. Written by lift_one.py. -/

set_option maxRecDepth 100000
namespace ParentOutput
open X86

def entry : Nat := 0x10000

def table : List (Nat × Instr × Nat) := [
  (0x10000, .mov 64 (.reg .rax) (.reg .rdi), 0x10003),  -- 48 89 f8                   mov rax, rdi
  (0x10003, .movv false 0 (.m .rsi 0x0), 0x10006),  -- 0f 10 06                   movups xmm0, xmmword ptr [rsi]
  (0x10006, .movv false 1 (.m .rsi 0x10), 0x1000A),  -- 0f 10 4e 10                movups xmm1, xmmword ptr [rsi + 0x10]
  (0x1000A, .storev true .rsp 0xFFFFFFFFFFFFFFC8 1, 0x1000F),  -- 0f 29 4c 24 c8             movaps xmmword ptr [rsp - 0x38], xmm1
  (0x1000F, .storev true .rsp 0xFFFFFFFFFFFFFFB8 0, 0x10014),  -- 0f 29 44 24 b8             movaps xmmword ptr [rsp - 0x48], xmm0
  (0x10014, .movv false 2 (.m .rdx 0x0), 0x10017),  -- 0f 10 12                   movups xmm2, xmmword ptr [rdx]
  (0x10017, .movv false 3 (.m .rdx 0x10), 0x1001B),  -- 0f 10 5a 10                movups xmm3, xmmword ptr [rdx + 0x10]
  (0x1001B, .storev true .rsp 0xFFFFFFFFFFFFFFD8 2, 0x10020),  -- 0f 29 54 24 d8             movaps xmmword ptr [rsp - 0x28], xmm2
  (0x10020, .storev true .rsp 0xFFFFFFFFFFFFFFE8 3, 0x10025),  -- 0f 29 5c 24 e8             movaps xmmword ptr [rsp - 0x18], xmm3
  (0x10025, .storev true .rdi 0x30 3, 0x10029),  -- 0f 29 5f 30                movaps xmmword ptr [rdi + 0x30], xmm3
  (0x10029, .storev true .rdi 0x20 2, 0x1002D),  -- 0f 29 57 20                movaps xmmword ptr [rdi + 0x20], xmm2
  (0x1002D, .storev true .rdi 0x10 1, 0x10031),  -- 0f 29 4f 10                movaps xmmword ptr [rdi + 0x10], xmm1
  (0x10031, .storev true .rdi 0x0 0, 0x10034),  -- 0f 29 07                   movaps xmmword ptr [rdi], xmm0
  (0x10034, .or 8 (.reg .r8) (.imm 0x4), 0x10038),  -- 41 80 c8 04                or r8b, 0x4
  (0x10038, .movv false 0 (.m .rcx 0x0), 0x1003B),  -- 0f 10 01                   movups xmm0, xmmword ptr [rcx]
  (0x1003B, .movv false 1 (.m .rcx 0x10), 0x1003F),  -- 0f 10 49 10                movups xmm1, xmmword ptr [rcx + 0x10]
  (0x1003F, .storev true .rdi 0x40 0, 0x10043),  -- 0f 29 47 40                movaps xmmword ptr [rdi + 0x40], xmm0
  (0x10043, .storev true .rdi 0x50 1, 0x10047),  -- 0f 29 4f 50                movaps xmmword ptr [rdi + 0x50], xmm1
  (0x10047, .mov 8 (.mem .rdi 0x60) (.imm 0x40), 0x1004B),  -- c6 47 60 40                mov byte ptr [rdi + 0x60], 0x40
  (0x1004B, .mov 64 (.mem .rdi 0x68) (.imm 0x0), 0x10053),  -- 48 c7 47 68 00 00 00 00    mov qword ptr [rdi + 0x68], 0x0
  (0x10053, .mov 8 (.mem .rdi 0x70) (.reg .r8), 0x10057),  -- 44 88 47 70                mov byte ptr [rdi + 0x70], r8b
  (0x10057, .mov 8 (.mem .rdi 0x71) (.reg .r9), 0x1005B),  -- 44 88 4f 71                mov byte ptr [rdi + 0x71], r9b
  (0x1005B, .ret, 0x1005C)  -- c3                         ret 
]

end ParentOutput
