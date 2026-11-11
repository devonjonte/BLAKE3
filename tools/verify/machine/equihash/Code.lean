import X86
import Attr

/-! The compiled functions, as llvm-objdump reads them. Written by lift.py; not edited by hand. -/

namespace Code
open X86

def table : List (Nat × Instr × Nat) := [
  -- __RNvMNtCslGntOAICRyN_8equihash6paramsNtB2_6Params3new
  (0x1D50, .push .rbp, 0x1D51),  -- 55                       push rbp
  (0x1D51, .mov 64 (.reg .rbp) (.reg .rsp), 0x1D54),  -- 48 89 e5                 mov rbp, rsp
  (0x1D54, .xor 32 (.reg .r8) (.reg .r8), 0x1D57),  -- 45 31 c0                 xor r8d, r8d
  (0x1D57, .cmp 32 (.reg .rdx) (.reg .rsi), 0x1D59),  -- 39 f2                    cmp edx, esi
  (0x1D59, .jcc .ae 0x1D97, 0x1D5B),  -- 73 3c                    jae 0xd97 <__RNvMNtCslGntOAICRyN_8equihash6paramsNtB2_6Params3new+0x47>
  (0x1D5B, .mov 32 (.reg .rax) (.reg .rsi), 0x1D5D),  -- 89 f0                    mov eax, esi
  (0x1D5D, .and 32 (.reg .rax) (.imm 0x7), 0x1D60),  -- 83 e0 07                 and eax, 0x7
  (0x1D60, .jcc .ne 0x1D97, 0x1D62),  -- 75 35                    jne 0xd97 <__RNvMNtCslGntOAICRyN_8equihash6paramsNtB2_6Params3new+0x47>
  (0x1D62, .mov 32 (.reg .rcx) (.reg .rdx), 0x1D64),  -- 89 d1                    mov ecx, edx
  (0x1D64, .cmp 32 (.reg .rdx) (.imm 0x3), 0x1D67),  -- 83 fa 03                 cmp edx, 0x3
  (0x1D67, .jcc .b 0x1D97, 0x1D69),  -- 72 2e                    jb 0xd97 <__RNvMNtCslGntOAICRyN_8equihash6paramsNtB2_6Params3new+0x47>
  (0x1D69, .lea32 .r8 .rcx 0x1, 0x1D6D),  -- 44 8d 41 01              lea r8d, [rcx + 0x1]
  (0x1D6D, .mov 32 (.reg .rax) (.reg .rsi), 0x1D6F),  -- 89 f0                    mov eax, esi
  (0x1D6F, .xor 32 (.reg .rdx) (.reg .rdx), 0x1D71),  -- 31 d2                    xor edx, edx
  (0x1D71, .div32 .r8, 0x1D74),  -- 41 f7 f0                 div r8d
  (0x1D74, .xor 32 (.reg .r8) (.reg .r8), 0x1D77),  -- 45 31 c0                 xor r8d, r8d
  (0x1D77, .cmp 32 (.reg .rsi) (.imm 0x200), 0x1D7D),  -- 81 fe 00 02 00 00        cmp esi, 0x200
  (0x1D7D, .jcc .a 0x1D97, 0x1D7F),  -- 77 18                    ja 0xd97 <__RNvMNtCslGntOAICRyN_8equihash6paramsNtB2_6Params3new+0x47>
  (0x1D7F, .test 32 (.reg .rdx) (.reg .rdx), 0x1D81),  -- 85 d2                    test edx, edx
  (0x1D81, .jcc .ne 0x1D97, 0x1D83),  -- 75 14                    jne 0xd97 <__RNvMNtCslGntOAICRyN_8equihash6paramsNtB2_6Params3new+0x47>
  (0x1D83, .add 32 (.reg .rax) (.imm 0xFFFFFFFFFFFFFFF8), 0x1D86),  -- 83 c0 f8                 add eax, -0x8
  (0x1D86, .cmp 32 (.reg .rax) (.imm 0x10), 0x1D89),  -- 83 f8 10                 cmp eax, 0x10
  (0x1D89, .jcc .a 0x1D97, 0x1D8B),  -- 77 0c                    ja 0xd97 <__RNvMNtCslGntOAICRyN_8equihash6paramsNtB2_6Params3new+0x47>
  (0x1D8B, .mov 32 (.mem .rdi 0x4) (.reg .rsi), 0x1D8E),  -- 89 77 04                 mov dword ptr [rdi + 0x4], esi
  (0x1D8E, .mov 32 (.mem .rdi 0x8) (.reg .rcx), 0x1D91),  -- 89 4f 08                 mov dword ptr [rdi + 0x8], ecx
  (0x1D91, .mov 32 (.reg .r8) (.imm 0x1), 0x1D97),  -- 41 b8 01 00 00 00        mov r8d, 0x1
  (0x1D97, .mov 32 (.mem .rdi 0x0) (.reg .r8), 0x1D9A),  -- 44 89 07                 mov dword ptr [rdi], r8d
  (0x1D9A, .mov 64 (.reg .rax) (.reg .rdi), 0x1D9D),  -- 48 89 f8                 mov rax, rdi
  (0x1D9D, .pop .rbp, 0x1D9E),  -- 5d                       pop rbp
  (0x1D9E, .ret, 0x1D9F)   -- c3                       ret 
]

/-- The instruction at an address, and the address after it. -/
def prog (pc : Nat) : Option (Instr × Nat) := table.lookup pc

@[code_at] theorem at_1D50 : prog 0x1D50 = some (.push .rbp, 0x1D51) := rfl
@[code_at] theorem at_1D51 : prog 0x1D51 = some (.mov 64 (.reg .rbp) (.reg .rsp), 0x1D54) := rfl
@[code_at] theorem at_1D54 : prog 0x1D54 = some (.xor 32 (.reg .r8) (.reg .r8), 0x1D57) := rfl
@[code_at] theorem at_1D57 : prog 0x1D57 = some (.cmp 32 (.reg .rdx) (.reg .rsi), 0x1D59) := rfl
@[code_at] theorem at_1D59 : prog 0x1D59 = some (.jcc .ae 0x1D97, 0x1D5B) := rfl
@[code_at] theorem at_1D5B : prog 0x1D5B = some (.mov 32 (.reg .rax) (.reg .rsi), 0x1D5D) := rfl
@[code_at] theorem at_1D5D : prog 0x1D5D = some (.and 32 (.reg .rax) (.imm 0x7), 0x1D60) := rfl
@[code_at] theorem at_1D60 : prog 0x1D60 = some (.jcc .ne 0x1D97, 0x1D62) := rfl
@[code_at] theorem at_1D62 : prog 0x1D62 = some (.mov 32 (.reg .rcx) (.reg .rdx), 0x1D64) := rfl
@[code_at] theorem at_1D64 : prog 0x1D64 = some (.cmp 32 (.reg .rdx) (.imm 0x3), 0x1D67) := rfl
@[code_at] theorem at_1D67 : prog 0x1D67 = some (.jcc .b 0x1D97, 0x1D69) := rfl
@[code_at] theorem at_1D69 : prog 0x1D69 = some (.lea32 .r8 .rcx 0x1, 0x1D6D) := rfl
@[code_at] theorem at_1D6D : prog 0x1D6D = some (.mov 32 (.reg .rax) (.reg .rsi), 0x1D6F) := rfl
@[code_at] theorem at_1D6F : prog 0x1D6F = some (.xor 32 (.reg .rdx) (.reg .rdx), 0x1D71) := rfl
@[code_at] theorem at_1D71 : prog 0x1D71 = some (.div32 .r8, 0x1D74) := rfl
@[code_at] theorem at_1D74 : prog 0x1D74 = some (.xor 32 (.reg .r8) (.reg .r8), 0x1D77) := rfl
@[code_at] theorem at_1D77 : prog 0x1D77 = some (.cmp 32 (.reg .rsi) (.imm 0x200), 0x1D7D) := rfl
@[code_at] theorem at_1D7D : prog 0x1D7D = some (.jcc .a 0x1D97, 0x1D7F) := rfl
@[code_at] theorem at_1D7F : prog 0x1D7F = some (.test 32 (.reg .rdx) (.reg .rdx), 0x1D81) := rfl
@[code_at] theorem at_1D81 : prog 0x1D81 = some (.jcc .ne 0x1D97, 0x1D83) := rfl
@[code_at] theorem at_1D83 : prog 0x1D83 = some (.add 32 (.reg .rax) (.imm 0xFFFFFFFFFFFFFFF8), 0x1D86) := rfl
@[code_at] theorem at_1D86 : prog 0x1D86 = some (.cmp 32 (.reg .rax) (.imm 0x10), 0x1D89) := rfl
@[code_at] theorem at_1D89 : prog 0x1D89 = some (.jcc .a 0x1D97, 0x1D8B) := rfl
@[code_at] theorem at_1D8B : prog 0x1D8B = some (.mov 32 (.mem .rdi 0x4) (.reg .rsi), 0x1D8E) := rfl
@[code_at] theorem at_1D8E : prog 0x1D8E = some (.mov 32 (.mem .rdi 0x8) (.reg .rcx), 0x1D91) := rfl
@[code_at] theorem at_1D91 : prog 0x1D91 = some (.mov 32 (.reg .r8) (.imm 0x1), 0x1D97) := rfl
@[code_at] theorem at_1D97 : prog 0x1D97 = some (.mov 32 (.mem .rdi 0x0) (.reg .r8), 0x1D9A) := rfl
@[code_at] theorem at_1D9A : prog 0x1D9A = some (.mov 64 (.reg .rax) (.reg .rdi), 0x1D9D) := rfl
@[code_at] theorem at_1D9D : prog 0x1D9D = some (.pop .rbp, 0x1D9E) := rfl
@[code_at] theorem at_1D9E : prog 0x1D9E = some (.ret, 0x1D9F) := rfl

end Code
