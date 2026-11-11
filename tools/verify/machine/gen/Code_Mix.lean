import X86
import Attr

/-! `mix` as rustc compiled it and llvm-objdump reads it. Written by make.py; not edited by hand. -/

namespace Code_Mix
open X86

def table : List (Nat × Instr × Nat) := [
  (0x1000, .push .rbp, 0x1001),  -- 55                   push rbp
  (0x1001, .mov 64 (.reg .rbp) (.reg .rsp), 0x1004),  -- 48 89 e5             mov rbp, rsp
  (0x1004, .test 64 (.reg .rsi) (.reg .rsi), 0x1007),  -- 48 85 f6             test rsi, rsi
  (0x1007, .jcc .e 0x1040, 0x1009),  -- 74 37                je 0xbc <_mix+0x40>
  (0x1009, .shl 64 (.reg .rsi) 2, 0x100D),  -- 48 c1 e6 02          shl rsi, 0x2
  (0x100D, .xor 32 (.reg .rcx) (.reg .rcx), 0x100F),  -- 31 c9                xor ecx, ecx
  (0x100F, .mov 32 (.reg .r8) (.imm 0xF0F0F0F0), 0x1015),  -- 41 b8 f0 f0 f0 f0    mov r8d, 0xf0f0f0f0
  (0x1015, .mov 32 (.reg .rax) (.memi .rdi .rcx), 0x1018),  -- 8b 04 0f             mov eax, dword ptr [rdi + rcx]
  (0x1018, .and 32 (.reg .rdx) (.imm 0xF0F0F0F), 0x101E),  -- 81 e2 0f 0f 0f 0f    and edx, 0xf0f0f0f
  (0x101E, .mov 32 (.reg .r9) (.reg .rax), 0x1021),  -- 41 89 c1             mov r9d, eax
  (0x1021, .and 32 (.reg .r9) (.reg .r8), 0x1024),  -- 45 21 c1             and r9d, r8d
  (0x1024, .or 32 (.reg .r9) (.reg .rdx), 0x1027),  -- 41 09 d1             or r9d, edx
  (0x1027, .xor 32 (.reg .r9) (.reg .r8), 0x102A),  -- 45 31 c1             xor r9d, r8d
  (0x102A, .shr 32 (.reg .rax) 3, 0x102D),  -- c1 e8 03             shr eax, 0x3
  (0x102D, .add 32 (.reg .rax) (.reg .r9), 0x1030),  -- 44 01 c8             add eax, r9d
  (0x1030, .mov 32 (.memi .rdi .rcx) (.reg .rax), 0x1033),  -- 89 04 0f             mov dword ptr [rdi + rcx], eax
  (0x1033, .add 64 (.reg .rcx) (.imm 0x4), 0x1037),  -- 48 83 c1 04          add rcx, 0x4
  (0x1037, .mov 32 (.reg .rdx) (.reg .rax), 0x1039),  -- 89 c2                mov edx, eax
  (0x1039, .cmp 64 (.reg .rsi) (.reg .rcx), 0x103C),  -- 48 39 ce             cmp rsi, rcx
  (0x103C, .jcc .ne 0x1015, 0x103E),  -- 75 d7                jne 0x91 <_mix+0x15>
  (0x103E, .jmp 0x1042, 0x1040),  -- eb 02                jmp 0xbe <_mix+0x42>
  (0x1040, .mov 32 (.reg .rax) (.reg .rdx), 0x1042),  -- 89 d0                mov eax, edx
  (0x1042, .pop .rbp, 0x1043),  -- 5d                   pop rbp
  (0x1043, .ret, 0x1044)   -- c3                   ret 
]

/-- The instruction at an address, and the address after it. -/
def prog (pc : Nat) : Option (Instr × Nat) := table.lookup pc

@[code_at] theorem at_1000 : prog 0x1000 = some (.push .rbp, 0x1001) := rfl
@[code_at] theorem at_1001 : prog 0x1001 = some (.mov 64 (.reg .rbp) (.reg .rsp), 0x1004) := rfl
@[code_at] theorem at_1004 : prog 0x1004 = some (.test 64 (.reg .rsi) (.reg .rsi), 0x1007) := rfl
@[code_at] theorem at_1007 : prog 0x1007 = some (.jcc .e 0x1040, 0x1009) := rfl
@[code_at] theorem at_1009 : prog 0x1009 = some (.shl 64 (.reg .rsi) 2, 0x100D) := rfl
@[code_at] theorem at_100D : prog 0x100D = some (.xor 32 (.reg .rcx) (.reg .rcx), 0x100F) := rfl
@[code_at] theorem at_100F : prog 0x100F = some (.mov 32 (.reg .r8) (.imm 0xF0F0F0F0), 0x1015) := rfl
@[code_at] theorem at_1015 : prog 0x1015 = some (.mov 32 (.reg .rax) (.memi .rdi .rcx), 0x1018) := rfl
@[code_at] theorem at_1018 : prog 0x1018 = some (.and 32 (.reg .rdx) (.imm 0xF0F0F0F), 0x101E) := rfl
@[code_at] theorem at_101E : prog 0x101E = some (.mov 32 (.reg .r9) (.reg .rax), 0x1021) := rfl
@[code_at] theorem at_1021 : prog 0x1021 = some (.and 32 (.reg .r9) (.reg .r8), 0x1024) := rfl
@[code_at] theorem at_1024 : prog 0x1024 = some (.or 32 (.reg .r9) (.reg .rdx), 0x1027) := rfl
@[code_at] theorem at_1027 : prog 0x1027 = some (.xor 32 (.reg .r9) (.reg .r8), 0x102A) := rfl
@[code_at] theorem at_102A : prog 0x102A = some (.shr 32 (.reg .rax) 3, 0x102D) := rfl
@[code_at] theorem at_102D : prog 0x102D = some (.add 32 (.reg .rax) (.reg .r9), 0x1030) := rfl
@[code_at] theorem at_1030 : prog 0x1030 = some (.mov 32 (.memi .rdi .rcx) (.reg .rax), 0x1033) := rfl
@[code_at] theorem at_1033 : prog 0x1033 = some (.add 64 (.reg .rcx) (.imm 0x4), 0x1037) := rfl
@[code_at] theorem at_1037 : prog 0x1037 = some (.mov 32 (.reg .rdx) (.reg .rax), 0x1039) := rfl
@[code_at] theorem at_1039 : prog 0x1039 = some (.cmp 64 (.reg .rsi) (.reg .rcx), 0x103C) := rfl
@[code_at] theorem at_103C : prog 0x103C = some (.jcc .ne 0x1015, 0x103E) := rfl
@[code_at] theorem at_103E : prog 0x103E = some (.jmp 0x1042, 0x1040) := rfl
@[code_at] theorem at_1040 : prog 0x1040 = some (.mov 32 (.reg .rax) (.reg .rdx), 0x1042) := rfl
@[code_at] theorem at_1042 : prog 0x1042 = some (.pop .rbp, 0x1043) := rfl
@[code_at] theorem at_1043 : prog 0x1043 = some (.ret, 0x1044) := rfl

end Code_Mix
