import Machine

/-! `merge`, as llvm-objdump reads it, placed at 0x40000. Written by lift_one.py. -/

set_option maxRecDepth 100000
namespace Merge
open X86

def entry : Nat := 0x40000

def table : List (Nat × Instr × Nat) := [
  (0x40000, .push .rbp, 0x40001),  -- 55                         push rbp
  (0x40001, .mov 64 (.reg .rbp) (.reg .rsp), 0x40004),  -- 48 89 e5                   mov rbp, rsp
  (0x40004, .push .r15, 0x40006),  -- 41 57                      push r15
  (0x40006, .push .r14, 0x40008),  -- 41 56                      push r14
  (0x40008, .push .r13, 0x4000A),  -- 41 55                      push r13
  (0x4000A, .push .r12, 0x4000C),  -- 41 54                      push r12
  (0x4000C, .push .rbx, 0x4000D),  -- 53                         push rbx
  (0x4000D, .and 64 (.reg .rsp) (.imm 0xFFFFFFFFFFFFFFC0), 0x40011),  -- 48 83 e4 c0                and rsp, -0x40
  (0x40011, .sub 64 (.reg .rsp) (.imm 0x180), 0x40018),  -- 48 81 ec 80 01 00 00       sub rsp, 0x180
  (0x40018, .mov 64 (.reg .rax) (.mem .rdi 0x0), 0x4001B),  -- 48 8b 07                   mov rax, qword ptr [rdi]
  (0x4001B, .mov 64 (.reg .r15) (.reg .rax), 0x4001E),  -- 49 89 c7                   mov r15, rax
  (0x4001E, .sub 64 (.reg .r15) (.reg .rdx), 0x40021),  -- 49 29 d7                   sub r15, rdx
  (0x40021, .jbe 0x401AB, 0x40027),  -- 0f 86 84 01 00 00          jbe 0x1ab <merge+0x1ab>
  (0x40027, .mov 64 (.reg .rbx) (.reg .rdi), 0x4002A),  -- 48 89 fb                   mov rbx, rdi
  (0x4002A, .lea .r12 .rdi 0x9, 0x4002E),  -- 4c 8d 67 09                lea r12, [rdi + 0x9]
  (0x4002E, .mov 64 (.reg .r14) (.mem .rsi 0x0), 0x40031),  -- 4c 8b 36                   mov r14, qword ptr [rsi]
  (0x40031, .movzx8 .rcx (.mem .rsi 0x28), 0x40035),  -- 0f b6 4e 28                movzx ecx, byte ptr [rsi + 0x28]
  (0x40035, .movzx8 .rdx (.mem .rsi 0x29), 0x40039),  -- 0f b6 56 29                movzx edx, byte ptr [rsi + 0x29]
  (0x40039, .mov 8 (.mem .rsp 0x3A) (.reg .rdx), 0x4003D),  -- 88 54 24 3a                mov byte ptr [rsp + 0x3a], dl
  (0x4003D, .or 8 (.reg .rcx) (.imm 0x4), 0x40040),  -- 80 c9 04                   or cl, 0x4
  (0x40040, .mov 8 (.mem .rsp 0x3B) (.reg .rcx), 0x40044),  -- 88 4c 24 3b                mov byte ptr [rsp + 0x3b], cl
  (0x40044, .movzx8 .rcx (.reg .rcx), 0x40047),  -- 0f b6 c9                   movzx ecx, cl
  (0x40047, .mov 32 (.mem .rsp 0x3C) (.reg .rcx), 0x4004B),  -- 89 4c 24 3c                mov dword ptr [rsp + 0x3c], ecx
  (0x4004B, .jmp 0x40094, 0x4004D),  -- eb 47                      jmp 0x94 <merge+0x94>
  (0x4004D, .nop, 0x40050),  -- 0f 1f 00                   nop dword ptr [rax]
  (0x40050, .mov 32 (.reg .r8) (.mem .rsp 0x3C), 0x40055),  -- 44 8b 44 24 3c             mov r8d, dword ptr [rsp + 0x3c]
  (0x40055, .call 0x30000, 0x4005B),  -- ff 15 00 00 00 00          call qword ptr [rip]
  (0x4005B, .add 64 (.reg .r13) (.reg .r12), 0x4005E),  -- 4d 01 e5                   add r13, r12
  (0x4005E, .movv true 0 (.m .rsp 0x40), 0x40063),  -- 0f 28 44 24 40             movaps xmm0, xmmword ptr [rsp + 0x40]
  (0x40063, .movv true 1 (.m .rsp 0x50), 0x40068),  -- 0f 28 4c 24 50             movaps xmm1, xmmword ptr [rsp + 0x50]
  (0x40068, .storev true .rsp 0x130 1, 0x40070),  -- 0f 29 8c 24 30 01 00 00    movaps xmmword ptr [rsp + 0x130], xmm1
  (0x40070, .storev true .rsp 0x120 0, 0x40078),  -- 0f 29 84 24 20 01 00 00    movaps xmmword ptr [rsp + 0x120], xmm0
  (0x40078, .storev false .r13 0x10 1, 0x4007D),  -- 41 0f 11 4d 10             movups xmmword ptr [r13 + 0x10], xmm1
  (0x4007D, .storev false .r13 0x0 0, 0x40082),  -- 41 0f 11 45 00             movups xmmword ptr [r13], xmm0
  (0x40082, .mov 64 (.reg .rax) (.mem .rbx 0x0), 0x40085),  -- 48 8b 03                   mov rax, qword ptr [rbx]
  (0x40085, .dec64 .rax, 0x40088),  -- 48 ff c8                   dec rax
  (0x40088, .mov 64 (.mem .rbx 0x0) (.reg .rax), 0x4008B),  -- 48 89 03                   mov qword ptr [rbx], rax
  (0x4008B, .dec64 .r15, 0x4008E),  -- 49 ff cf                   dec r15
  (0x4008E, .je 0x401AB, 0x40094),  -- 0f 84 17 01 00 00          je 0x1ab <merge+0x1ab>
  (0x40094, .cmp 64 (.reg .rax) (.imm 0x1), 0x40098),  -- 48 83 f8 01                cmp rax, 0x1
  (0x40098, .jbe 0x401BA, 0x4009E),  -- 0f 86 1c 01 00 00          jbe 0x1ba <merge+0x1ba>
  (0x4009E, .cmp 8 (.mem .rbx 0x8) (.imm 0x1), 0x400A2),  -- 80 7b 08 01                cmp byte ptr [rbx + 0x8], 0x1
  (0x400A2, .jne 0x40085, 0x400A4),  -- 75 e1                      jne 0x85 <merge+0x85>
  (0x400A4, .lea .r13 .rax 0xFFFFFFFFFFFFFFFE, 0x400A8),  -- 4c 8d 68 fe                lea r13, [rax - 0x2]
  (0x400A8, .cmp 64 (.reg .r13) (.imm 0x37), 0x400AC),  -- 49 83 fd 37                cmp r13, 0x37
  (0x400AC, .jae 0x401E5, 0x400B2),  -- 0f 83 33 01 00 00          jae 0x1e5 <merge+0x1e5>
  (0x400B2, .lea .rdi .rax 0xFFFFFFFFFFFFFFFF, 0x400B6),  -- 48 8d 78 ff                lea rdi, [rax - 0x1]
  (0x400B6, .cmp 64 (.reg .rax) (.imm 0x38), 0x400BA),  -- 48 83 f8 38                cmp rax, 0x38
  (0x400BA, .jae 0x401D3, 0x400C0),  -- 0f 83 13 01 00 00          jae 0x1d3 <merge+0x1d3>
  (0x400C0, .shl64 .r13 5, 0x400C4),  -- 49 c1 e5 05                shl r13, 0x5
  (0x400C4, .shl64 .rdi 5, 0x400C8),  -- 48 c1 e7 05                shl rdi, 0x5
  (0x400C8, .movvi false 0 .r12 .r13 0x0, 0x400CD),  -- 43 0f 10 04 2c             movups xmm0, xmmword ptr [r12 + r13]
  (0x400CD, .movvi false 1 .r12 .r13 0x10, 0x400D3),  -- 43 0f 10 4c 2c 10          movups xmm1, xmmword ptr [r12 + r13 + 0x10]
  (0x400D3, .storev true .rsp 0x50 1, 0x400D8),  -- 0f 29 4c 24 50             movaps xmmword ptr [rsp + 0x50], xmm1
  (0x400D8, .storev true .rsp 0x40 0, 0x400DD),  -- 0f 29 44 24 40             movaps xmmword ptr [rsp + 0x40], xmm0
  (0x400DD, .movvi false 0 .r12 .rdi 0x0, 0x400E2),  -- 41 0f 10 04 3c             movups xmm0, xmmword ptr [r12 + rdi]
  (0x400E2, .movvi false 1 .r12 .rdi 0x10, 0x400E8),  -- 41 0f 10 4c 3c 10          movups xmm1, xmmword ptr [r12 + rdi + 0x10]
  (0x400E8, .lea .rax .rsp 0x60, 0x400ED),  -- 48 8d 44 24 60             lea rax, [rsp + 0x60]
  (0x400ED, .storev false .rax 0x10 1, 0x400F1),  -- 0f 11 48 10                movups xmmword ptr [rax + 0x10], xmm1
  (0x400F1, .storev false .rax 0x0 0, 0x400F4),  -- 0f 11 00                   movups xmmword ptr [rax], xmm0
  (0x400F4, .movv true 0 (.m .rsp 0x40), 0x400F9),  -- 0f 28 44 24 40             movaps xmm0, xmmword ptr [rsp + 0x40]
  (0x400F9, .movv true 1 (.m .rsp 0x50), 0x400FE),  -- 0f 28 4c 24 50             movaps xmm1, xmmword ptr [rsp + 0x50]
  (0x400FE, .movv true 2 (.m .rsp 0x60), 0x40103),  -- 0f 28 54 24 60             movaps xmm2, xmmword ptr [rsp + 0x60]
  (0x40103, .movv true 3 (.m .rsp 0x70), 0x40108),  -- 0f 28 5c 24 70             movaps xmm3, xmmword ptr [rsp + 0x70]
  (0x40108, .storev true .rsp 0xB0 3, 0x40110),  -- 0f 29 9c 24 b0 00 00 00    movaps xmmword ptr [rsp + 0xb0], xmm3
  (0x40110, .storev true .rsp 0xA0 2, 0x40118),  -- 0f 29 94 24 a0 00 00 00    movaps xmmword ptr [rsp + 0xa0], xmm2
  (0x40118, .storev true .rsp 0x90 1, 0x40120),  -- 0f 29 8c 24 90 00 00 00    movaps xmmword ptr [rsp + 0x90], xmm1
  (0x40120, .storev true .rsp 0x80 0, 0x40128),  -- 0f 29 84 24 80 00 00 00    movaps xmmword ptr [rsp + 0x80], xmm0
  (0x40128, .movv false 0 (.m .r14 0x0), 0x4012C),  -- 41 0f 10 06                movups xmm0, xmmword ptr [r14]
  (0x4012C, .movv false 1 (.m .r14 0x10), 0x40131),  -- 41 0f 10 4e 10             movups xmm1, xmmword ptr [r14 + 0x10]
  (0x40131, .lea .rax .rsp 0xC0, 0x40139),  -- 48 8d 84 24 c0 00 00 00    lea rax, [rsp + 0xc0]
  (0x40139, .storev true .rax 0x0 0, 0x4013C),  -- 0f 29 00                   movaps xmmword ptr [rax], xmm0
  (0x4013C, .storev true .rax 0x10 1, 0x40140),  -- 0f 29 48 10                movaps xmmword ptr [rax + 0x10], xmm1
  (0x40140, .mov 8 (.mem .rsp 0xE0) (.imm 0x40), 0x40148),  -- c6 84 24 e0 00 00 00 40    mov byte ptr [rsp + 0xe0], 0x40
  (0x40148, .mov 64 (.mem .rsp 0xE8) (.imm 0x0), 0x40154),  -- 48 c7 84 24 e8 00 00 00 00 00 00 00 mov qword ptr [rsp + 0xe8], 0x0
  (0x40154, .movzx8 .rax (.mem .rsp 0x3B), 0x40159),  -- 0f b6 44 24 3b             movzx eax, byte ptr [rsp + 0x3b]
  (0x40159, .mov 8 (.mem .rsp 0xF0) (.reg .rax), 0x40160),  -- 88 84 24 f0 00 00 00       mov byte ptr [rsp + 0xf0], al
  (0x40160, .movzx8 .rax (.mem .rsp 0x3A), 0x40165),  -- 0f b6 44 24 3a             movzx eax, byte ptr [rsp + 0x3a]
  (0x40165, .mov 8 (.mem .rsp 0xF1) (.reg .rax), 0x4016C),  -- 88 84 24 f1 00 00 00       mov byte ptr [rsp + 0xf1], al
  (0x4016C, .movv false 0 (.m .r14 0x0), 0x40170),  -- 41 0f 10 06                movups xmm0, xmmword ptr [r14]
  (0x40170, .movv false 1 (.m .r14 0x10), 0x40175),  -- 41 0f 10 4e 10             movups xmm1, xmmword ptr [r14 + 0x10]
  (0x40175, .storev true .rsp 0x50 1, 0x4017A),  -- 0f 29 4c 24 50             movaps xmmword ptr [rsp + 0x50], xmm1
  (0x4017A, .storev true .rsp 0x40 0, 0x4017F),  -- 0f 29 44 24 40             movaps xmmword ptr [rsp + 0x40], xmm0
  (0x4017F, .lea .rdi .rsp 0x40, 0x40184),  -- 48 8d 7c 24 40             lea rdi, [rsp + 0x40]
  (0x40184, .lea .rsi .rsp 0x80, 0x4018C),  -- 48 8d b4 24 80 00 00 00    lea rsi, [rsp + 0x80]
  (0x4018C, .mov 32 (.reg .rdx) (.imm 0x40), 0x40191),  -- ba 40 00 00 00             mov edx, 0x40
  (0x40191, .xor 32 (.reg .rcx) (.reg .rcx), 0x40193),  -- 31 c9                      xor ecx, ecx
  (0x40193, .cmp 8 (.reg .rax) (.imm 0x5), 0x40195),  -- 3c 05                      cmp al, 0x5
  (0x40195, .je 0x40050, 0x4019B),  -- 0f 84 b5 fe ff ff          je 0x50 <merge+0x50>
  (0x4019B, .mov 32 (.reg .r8) (.mem .rsp 0x3C), 0x401A0),  -- 44 8b 44 24 3c             mov r8d, dword ptr [rsp + 0x3c]
  (0x401A0, .call 0x20000, 0x401A6),  -- ff 15 00 00 00 00          call qword ptr [rip]
  (0x401A6, .jmp 0x4005B, 0x401AB),  -- e9 b0 fe ff ff             jmp 0x5b <merge+0x5b>
  (0x401AB, .lea .rsp .rbp 0xFFFFFFFFFFFFFFD8, 0x401AF),  -- 48 8d 65 d8                lea rsp, [rbp - 0x28]
  (0x401AF, .pop .rbx, 0x401B0),  -- 5b                         pop rbx
  (0x401B0, .pop .r12, 0x401B2),  -- 41 5c                      pop r12
  (0x401B2, .pop .r13, 0x401B4),  -- 41 5d                      pop r13
  (0x401B4, .pop .r14, 0x401B6),  -- 41 5e                      pop r14
  (0x401B6, .pop .r15, 0x401B8),  -- 41 5f                      pop r15
  (0x401B8, .pop .rbp, 0x401B9),  -- 5d                         pop rbp
  (0x401B9, .ret, 0x401BA)  -- c3                         ret 
]

end Merge
