import X86
import Attr

/-! `addrot` as rustc compiled it and llvm-objdump reads it. Written by make.py; not edited by hand. -/

namespace Code_Addrot
open X86

def table : List (Nat × Instr × Nat) := [
  (0x1000, .push .rbp, 0x1001),  -- 55                   push rbp
  (0x1001, .mov 64 (.reg .rbp) (.reg .rsp), 0x1004),  -- 48 89 e5             mov rbp, rsp
  (0x1004, .mov 32 (.reg .rax) (.reg .rdx), 0x1006),  -- 89 d0                mov eax, edx
  (0x1006, .test 64 (.reg .rsi) (.reg .rsi), 0x1009),  -- 48 85 f6             test rsi, rsi
  (0x1009, .jcc .e 0x1029, 0x100B),  -- 74 1e                je 0x29 <_addrot+0x29>
  (0x100B, .shl 64 (.reg .rsi) 2, 0x100F),  -- 48 c1 e6 02          shl rsi, 0x2
  (0x100F, .xor 32 (.reg .rcx) (.reg .rcx), 0x1011),  -- 31 c9                xor ecx, ecx
  (0x1011, .mov 32 (.reg .rdx) (.reg .rax), 0x1013),  -- 89 c2                mov edx, eax
  (0x1013, .mov 32 (.reg .rax) (.memi .rdi .rcx), 0x1016),  -- 8b 04 0f             mov eax, dword ptr [rdi + rcx]
  (0x1016, .add 32 (.reg .rax) (.reg .rdx), 0x1018),  -- 01 d0                add eax, edx
  (0x1018, .rol32 .rax 7, 0x101B),  -- c1 c0 07             rol eax, 0x7
  (0x101B, .xor 32 (.reg .rax) (.reg .rdx), 0x101D),  -- 31 d0                xor eax, edx
  (0x101D, .mov 32 (.memi .rdi .rcx) (.reg .rax), 0x1020),  -- 89 04 0f             mov dword ptr [rdi + rcx], eax
  (0x1020, .add 64 (.reg .rcx) (.imm 0x4), 0x1024),  -- 48 83 c1 04          add rcx, 0x4
  (0x1024, .cmp 64 (.reg .rsi) (.reg .rcx), 0x1027),  -- 48 39 ce             cmp rsi, rcx
  (0x1027, .jcc .ne 0x1011, 0x1029),  -- 75 e8                jne 0x11 <_addrot+0x11>
  (0x1029, .pop .rbp, 0x102A),  -- 5d                   pop rbp
  (0x102A, .ret, 0x102B)   -- c3                   ret 
]

/-- The instruction at an address, and the address after it. -/
def prog (pc : Nat) : Option (Instr × Nat) := table.lookup pc

@[code_at] theorem at_1000 : prog 0x1000 = some (.push .rbp, 0x1001) := rfl
@[code_at] theorem at_1001 : prog 0x1001 = some (.mov 64 (.reg .rbp) (.reg .rsp), 0x1004) := rfl
@[code_at] theorem at_1004 : prog 0x1004 = some (.mov 32 (.reg .rax) (.reg .rdx), 0x1006) := rfl
@[code_at] theorem at_1006 : prog 0x1006 = some (.test 64 (.reg .rsi) (.reg .rsi), 0x1009) := rfl
@[code_at] theorem at_1009 : prog 0x1009 = some (.jcc .e 0x1029, 0x100B) := rfl
@[code_at] theorem at_100B : prog 0x100B = some (.shl 64 (.reg .rsi) 2, 0x100F) := rfl
@[code_at] theorem at_100F : prog 0x100F = some (.xor 32 (.reg .rcx) (.reg .rcx), 0x1011) := rfl
@[code_at] theorem at_1011 : prog 0x1011 = some (.mov 32 (.reg .rdx) (.reg .rax), 0x1013) := rfl
@[code_at] theorem at_1013 : prog 0x1013 = some (.mov 32 (.reg .rax) (.memi .rdi .rcx), 0x1016) := rfl
@[code_at] theorem at_1016 : prog 0x1016 = some (.add 32 (.reg .rax) (.reg .rdx), 0x1018) := rfl
@[code_at] theorem at_1018 : prog 0x1018 = some (.rol32 .rax 7, 0x101B) := rfl
@[code_at] theorem at_101B : prog 0x101B = some (.xor 32 (.reg .rax) (.reg .rdx), 0x101D) := rfl
@[code_at] theorem at_101D : prog 0x101D = some (.mov 32 (.memi .rdi .rcx) (.reg .rax), 0x1020) := rfl
@[code_at] theorem at_1020 : prog 0x1020 = some (.add 64 (.reg .rcx) (.imm 0x4), 0x1024) := rfl
@[code_at] theorem at_1024 : prog 0x1024 = some (.cmp 64 (.reg .rsi) (.reg .rcx), 0x1027) := rfl
@[code_at] theorem at_1027 : prog 0x1027 = some (.jcc .ne 0x1011, 0x1029) := rfl
@[code_at] theorem at_1029 : prog 0x1029 = some (.pop .rbp, 0x102A) := rfl
@[code_at] theorem at_102A : prog 0x102A = some (.ret, 0x102B) := rfl

end Code_Addrot
