import Machine

/-! `<blake3_servil_core::hasher::Output<blake3_servil_core::platform::Platform>>::chaining_val`, as llvm-objdump reads it, placed at 0x11000. Written by lift_one.py. -/

set_option maxRecDepth 100000
namespace ChainingValue
open X86

def entry : Nat := 0x11000

def table : List (Nat × Instr × Nat) := [
  (0x11000, .push .rbx, 0x11001),  -- 53                         push rbx
  (0x11001, .sub 64 (.reg .rsp) (.imm 0x20), 0x11005),  -- 48 83 ec 20                sub rsp, 0x20
  (0x11005, .mov 64 (.reg .rbx) (.reg .rdi), 0x11008),  -- 48 89 fb                   mov rbx, rdi
  (0x11008, .movv true 0 (.m .rsi 0x40), 0x1100C),  -- 0f 28 46 40                movaps xmm0, xmmword ptr [rsi + 0x40]
  (0x1100C, .movv true 1 (.m .rsi 0x50), 0x11010),  -- 0f 28 4e 50                movaps xmm1, xmmword ptr [rsi + 0x50]
  (0x11010, .storev true .rsp 0x10 1, 0x11015),  -- 0f 29 4c 24 10             movaps xmmword ptr [rsp + 0x10], xmm1
  (0x11015, .storev true .rsp 0x0 0, 0x11019),  -- 0f 29 04 24                movaps xmmword ptr [rsp], xmm0
  (0x11019, .movzx8 .rax (.mem .rsi 0x60), 0x1101D),  -- 0f b6 46 60                movzx eax, byte ptr [rsi + 0x60]
  (0x1101D, .mov 64 (.reg .rcx) (.mem .rsi 0x68), 0x11021),  -- 48 8b 4e 68                mov rcx, qword ptr [rsi + 0x68]
  (0x11021, .movzx8 .rdi (.mem .rsi 0x70), 0x11025),  -- 0f b6 7e 70                movzx edi, byte ptr [rsi + 0x70]
  (0x11025, .cmp 8 (.mem .rsi 0x71) (.imm 0x5), 0x11029),  -- 80 7e 71 05                cmp byte ptr [rsi + 0x71], 0x5
  (0x11029, .jne 0x1103D, 0x1102B),  -- 75 12                      jne 0x3d <<blake3_servil_core::hasher::Output<blake3_servil_core::platform::Platform>>::chaining_value+0x3d>
  (0x1102B, .movzx8 .rdx (.reg .rax), 0x1102E),  -- 0f b6 d0                   movzx edx, al
  (0x1102E, .movzx8 .r8 (.reg .rdi), 0x11032),  -- 44 0f b6 c7                movzx r8d, dil
  (0x11032, .mov 64 (.reg .rdi) (.reg .rsp), 0x11035),  -- 48 89 e7                   mov rdi, rsp
  (0x11035, .call 0x30000, 0x1103B),  -- ff 15 00 00 00 00          call qword ptr [rip]
  (0x1103B, .jmp 0x1104D, 0x1103D),  -- eb 10                      jmp 0x4d <<blake3_servil_core::hasher::Output<blake3_servil_core::platform::Platform>>::chaining_value+0x4d>
  (0x1103D, .movzx8 .rdx (.reg .rax), 0x11040),  -- 0f b6 d0                   movzx edx, al
  (0x11040, .movzx8 .r8 (.reg .rdi), 0x11044),  -- 44 0f b6 c7                movzx r8d, dil
  (0x11044, .mov 64 (.reg .rdi) (.reg .rsp), 0x11047),  -- 48 89 e7                   mov rdi, rsp
  (0x11047, .call 0x20000, 0x1104D),  -- ff 15 00 00 00 00          call qword ptr [rip]
  (0x1104D, .movv true 0 (.m .rsp 0x0), 0x11051),  -- 0f 28 04 24                movaps xmm0, xmmword ptr [rsp]
  (0x11051, .movv true 1 (.m .rsp 0x10), 0x11056),  -- 0f 28 4c 24 10             movaps xmm1, xmmword ptr [rsp + 0x10]
  (0x11056, .storev false .rbx 0x10 1, 0x1105A),  -- 0f 11 4b 10                movups xmmword ptr [rbx + 0x10], xmm1
  (0x1105A, .storev false .rbx 0x0 0, 0x1105D),  -- 0f 11 03                   movups xmmword ptr [rbx], xmm0
  (0x1105D, .mov 64 (.reg .rax) (.reg .rbx), 0x11060),  -- 48 89 d8                   mov rax, rbx
  (0x11060, .add 64 (.reg .rsp) (.imm 0x20), 0x11064),  -- 48 83 c4 20                add rsp, 0x20
  (0x11064, .pop .rbx, 0x11065),  -- 5b                         pop rbx
  (0x11065, .ret, 0x11066)  -- c3                         ret 
]

end ChainingValue
