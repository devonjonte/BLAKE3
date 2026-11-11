import X86
import Attr

/-! `quarter` as rustc compiled it and llvm-objdump reads it. Written by make.py; not edited by hand. -/

namespace Code_Quarter
open X86

def table : List (Nat × Instr × Nat) := [
  (0x1000, .push .rbp, 0x1001),  -- 55                   push rbp
  (0x1001, .mov 64 (.reg .rbp) (.reg .rsp), 0x1004),  -- 48 89 e5             mov rbp, rsp
  (0x1004, .mov 32 (.reg .rax) (.reg .rdx), 0x1006),  -- 89 d0                mov eax, edx
  (0x1006, .test 64 (.reg .rsi) (.reg .rsi), 0x1009),  -- 48 85 f6             test rsi, rsi
  (0x1009, .jcc .e 0x102C, 0x100B),  -- 74 21                je 0xec <_quarter+0x2c>
  (0x100B, .shl 64 (.reg .rsi) 2, 0x100F),  -- 48 c1 e6 02          shl rsi, 0x2
  (0x100F, .xor 32 (.reg .rcx) (.reg .rcx), 0x1011),  -- 31 c9                xor ecx, ecx
  (0x1011, .mov 32 (.reg .rdx) (.memi .rdi .rcx), 0x1014),  -- 8b 14 0f             mov edx, dword ptr [rdi + rcx]
  (0x1014, .lea32 .rax .rax .rdx 0xFFFFFFFF9E3779B9, 0x101B),  -- 8d 84 10 b9 79 37 9e lea eax, [rax + rdx - 0x61c88647]
  (0x101B, .rol32 .rax 16, 0x101E),  -- c1 c0 10             rol eax, 0x10
  (0x101E, .xor 32 (.reg .rax) (.reg .rdx), 0x1020),  -- 31 d0                xor eax, edx
  (0x1020, .mov 32 (.memi .rdi .rcx) (.reg .rax), 0x1023),  -- 89 04 0f             mov dword ptr [rdi + rcx], eax
  (0x1023, .add 64 (.reg .rcx) (.imm 0x4), 0x1027),  -- 48 83 c1 04          add rcx, 0x4
  (0x1027, .cmp 64 (.reg .rsi) (.reg .rcx), 0x102A),  -- 48 39 ce             cmp rsi, rcx
  (0x102A, .jcc .ne 0x1011, 0x102C),  -- 75 e5                jne 0xd1 <_quarter+0x11>
  (0x102C, .pop .rbp, 0x102D),  -- 5d                   pop rbp
  (0x102D, .ret, 0x102E)   -- c3                   ret 
]

/-- The instruction at an address, and the address after it. -/
def prog (pc : Nat) : Option (Instr × Nat) := table.lookup pc

@[code_at] theorem at_1000 : prog 0x1000 = some (.push .rbp, 0x1001) := rfl
@[code_at] theorem at_1001 : prog 0x1001 = some (.mov 64 (.reg .rbp) (.reg .rsp), 0x1004) := rfl
@[code_at] theorem at_1004 : prog 0x1004 = some (.mov 32 (.reg .rax) (.reg .rdx), 0x1006) := rfl
@[code_at] theorem at_1006 : prog 0x1006 = some (.test 64 (.reg .rsi) (.reg .rsi), 0x1009) := rfl
@[code_at] theorem at_1009 : prog 0x1009 = some (.jcc .e 0x102C, 0x100B) := rfl
@[code_at] theorem at_100B : prog 0x100B = some (.shl 64 (.reg .rsi) 2, 0x100F) := rfl
@[code_at] theorem at_100F : prog 0x100F = some (.xor 32 (.reg .rcx) (.reg .rcx), 0x1011) := rfl
@[code_at] theorem at_1011 : prog 0x1011 = some (.mov 32 (.reg .rdx) (.memi .rdi .rcx), 0x1014) := rfl
@[code_at] theorem at_1014 : prog 0x1014 = some (.lea32 .rax .rax .rdx 0xFFFFFFFF9E3779B9, 0x101B) := rfl
@[code_at] theorem at_101B : prog 0x101B = some (.rol32 .rax 16, 0x101E) := rfl
@[code_at] theorem at_101E : prog 0x101E = some (.xor 32 (.reg .rax) (.reg .rdx), 0x1020) := rfl
@[code_at] theorem at_1020 : prog 0x1020 = some (.mov 32 (.memi .rdi .rcx) (.reg .rax), 0x1023) := rfl
@[code_at] theorem at_1023 : prog 0x1023 = some (.add 64 (.reg .rcx) (.imm 0x4), 0x1027) := rfl
@[code_at] theorem at_1027 : prog 0x1027 = some (.cmp 64 (.reg .rsi) (.reg .rcx), 0x102A) := rfl
@[code_at] theorem at_102A : prog 0x102A = some (.jcc .ne 0x1011, 0x102C) := rfl
@[code_at] theorem at_102C : prog 0x102C = some (.pop .rbp, 0x102D) := rfl
@[code_at] theorem at_102D : prog 0x102D = some (.ret, 0x102E) := rfl

end Code_Quarter
