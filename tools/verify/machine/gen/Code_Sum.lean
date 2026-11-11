import X86
import Attr

/-! `sum` as rustc compiled it and llvm-objdump reads it. Written by make.py; not edited by hand. -/

namespace Code_Sum
open X86

def table : List (Nat × Instr × Nat) := [
  (0x1000, .push .rbp, 0x1001),  -- 55                   push rbp
  (0x1001, .mov 64 (.reg .rbp) (.reg .rsp), 0x1004),  -- 48 89 e5             mov rbp, rsp
  (0x1004, .mov 32 (.reg .rax) (.reg .rdx), 0x1006),  -- 89 d0                mov eax, edx
  (0x1006, .test 64 (.reg .rsi) (.reg .rsi), 0x1009),  -- 48 85 f6             test rsi, rsi
  (0x1009, .jcc .e 0x1020, 0x100B),  -- 74 15                je 0x15c <_sum+0x20>
  (0x100B, .shl 64 (.reg .rsi) 2, 0x100F),  -- 48 c1 e6 02          shl rsi, 0x2
  (0x100F, .xor 32 (.reg .rcx) (.reg .rcx), 0x1011),  -- 31 c9                xor ecx, ecx
  (0x1011, .add 32 (.reg .rax) (.memi .rdi .rcx), 0x1014),  -- 03 04 0f             add eax, dword ptr [rdi + rcx]
  (0x1014, .mov 32 (.memi .rdi .rcx) (.reg .rax), 0x1017),  -- 89 04 0f             mov dword ptr [rdi + rcx], eax
  (0x1017, .add 64 (.reg .rcx) (.imm 0x4), 0x101B),  -- 48 83 c1 04          add rcx, 0x4
  (0x101B, .cmp 64 (.reg .rsi) (.reg .rcx), 0x101E),  -- 48 39 ce             cmp rsi, rcx
  (0x101E, .jcc .ne 0x1011, 0x1020),  -- 75 f1                jne 0x14d <_sum+0x11>
  (0x1020, .pop .rbp, 0x1021),  -- 5d                   pop rbp
  (0x1021, .ret, 0x1022)   -- c3                   ret 
]

/-- The instruction at an address, and the address after it. -/
def prog (pc : Nat) : Option (Instr × Nat) := table.lookup pc

@[code_at] theorem at_1000 : prog 0x1000 = some (.push .rbp, 0x1001) := rfl
@[code_at] theorem at_1001 : prog 0x1001 = some (.mov 64 (.reg .rbp) (.reg .rsp), 0x1004) := rfl
@[code_at] theorem at_1004 : prog 0x1004 = some (.mov 32 (.reg .rax) (.reg .rdx), 0x1006) := rfl
@[code_at] theorem at_1006 : prog 0x1006 = some (.test 64 (.reg .rsi) (.reg .rsi), 0x1009) := rfl
@[code_at] theorem at_1009 : prog 0x1009 = some (.jcc .e 0x1020, 0x100B) := rfl
@[code_at] theorem at_100B : prog 0x100B = some (.shl 64 (.reg .rsi) 2, 0x100F) := rfl
@[code_at] theorem at_100F : prog 0x100F = some (.xor 32 (.reg .rcx) (.reg .rcx), 0x1011) := rfl
@[code_at] theorem at_1011 : prog 0x1011 = some (.add 32 (.reg .rax) (.memi .rdi .rcx), 0x1014) := rfl
@[code_at] theorem at_1014 : prog 0x1014 = some (.mov 32 (.memi .rdi .rcx) (.reg .rax), 0x1017) := rfl
@[code_at] theorem at_1017 : prog 0x1017 = some (.add 64 (.reg .rcx) (.imm 0x4), 0x101B) := rfl
@[code_at] theorem at_101B : prog 0x101B = some (.cmp 64 (.reg .rsi) (.reg .rcx), 0x101E) := rfl
@[code_at] theorem at_101E : prog 0x101E = some (.jcc .ne 0x1011, 0x1020) := rfl
@[code_at] theorem at_1020 : prog 0x1020 = some (.pop .rbp, 0x1021) := rfl
@[code_at] theorem at_1021 : prog 0x1021 = some (.ret, 0x1022) := rfl

end Code_Sum
