import X86

/-! The compiled functions, as llvm-objdump reads them. Written by lift.py; not edited by hand. -/

namespace Code
open X86

def table : List (Nat × Instr × Nat) := [
  -- _scan2
  (0x1000, .mov 32 (.reg .rax) (.reg .rdx), 0x1002),  -- 89 d0                    mov eax, edx
  (0x1002, .test 64 (.reg .rsi) (.reg .rsi), 0x1005),  -- 48 85 f6                 test rsi, rsi
  (0x1005, .jcc .e 0x1024, 0x1007),  -- 74 1d                    je 0x24 <_scan+0x24>
  (0x1007, .push .rbp, 0x1008),  -- 55                       push rbp
  (0x1008, .mov 64 (.reg .rbp) (.reg .rsp), 0x100B),  -- 48 89 e5                 mov rbp, rsp
  (0x100B, .shl 64 (.reg .rsi) 2, 0x100F),  -- 48 c1 e6 02              shl rsi, 0x2
  (0x100F, .xor 32 (.reg .rcx) (.reg .rcx), 0x1011),  -- 31 c9                    xor ecx, ecx
  (0x1011, .rol32 .rax 5, 0x1014),  -- c1 c0 05                 rol eax, 0x5
  (0x1014, .xor 32 (.reg .rax) (.memi .rdi .rcx), 0x1017),  -- 33 04 0f                 xor eax, dword ptr [rdi + rcx]
  (0x1017, .mov 32 (.memi .rdi .rcx) (.reg .rax), 0x101A),  -- 89 04 0f                 mov dword ptr [rdi + rcx], eax
  (0x101A, .add 64 (.reg .rcx) (.imm 0x4), 0x101E),  -- 48 83 c1 04              add rcx, 0x4
  (0x101E, .cmp 64 (.reg .rsi) (.reg .rcx), 0x1021),  -- 48 39 ce                 cmp rsi, rcx
  (0x1021, .jcc .ne 0x1011, 0x1023),  -- 75 ee                    jne 0x11 <_scan+0x11>
  (0x1023, .pop .rbp, 0x1024),  -- 5d                       pop rbp
  (0x1024, .ret, 0x1025),  -- c3                       ret 
  (0x1025, .push .rbp, 0x1026),  -- 55                       push rbp
  (0x1026, .mov 64 (.reg .rbp) (.reg .rsp), 0x1029),  -- 48 89 e5                 mov rbp, rsp
  (0x1029, .push .r14, 0x102B),  -- 41 56                    push r14
  (0x102B, .push .rbx, 0x102C),  -- 53                       push rbx
  (0x102C, .mov 64 (.reg .rbx) (.reg .rcx), 0x102F),  -- 48 89 cb                 mov rbx, rcx
  (0x102F, .mov 64 (.reg .r14) (.reg .rdx), 0x1032),  -- 49 89 d6                 mov r14, rdx
  (0x1032, .mov 32 (.reg .rdx) (.reg .r8), 0x1035),  -- 44 89 c2                 mov edx, r8d
  (0x1035, .call 0x1000, 0x103A),  -- e8 00 00 00 00           call 0x3a <_scan2+0x15>
  (0x103A, .mov 64 (.reg .rdi) (.reg .r14), 0x103D),  -- 4c 89 f7                 mov rdi, r14
  (0x103D, .mov 64 (.reg .rsi) (.reg .rbx), 0x1040),  -- 48 89 de                 mov rsi, rbx
  (0x1040, .mov 32 (.reg .rdx) (.reg .rax), 0x1042),  -- 89 c2                    mov edx, eax
  (0x1042, .pop .rbx, 0x1043),  -- 5b                       pop rbx
  (0x1043, .pop .r14, 0x1045),  -- 41 5e                    pop r14
  (0x1045, .pop .rbp, 0x1046),  -- 5d                       pop rbp
  (0x1046, .jmp 0x1000, 0x104B)   -- e9 00 00 00 00           jmp 0x4b <_scan2+0x26>
]

/-- The instruction at an address, and the address after it. -/
def prog (pc : Nat) : Option (Instr × Nat) := table.lookup pc

@[simp] theorem at_1000 : prog 0x1000 = some (.mov 32 (.reg .rax) (.reg .rdx), 0x1002) := rfl
@[simp] theorem at_1002 : prog 0x1002 = some (.test 64 (.reg .rsi) (.reg .rsi), 0x1005) := rfl
@[simp] theorem at_1005 : prog 0x1005 = some (.jcc .e 0x1024, 0x1007) := rfl
@[simp] theorem at_1007 : prog 0x1007 = some (.push .rbp, 0x1008) := rfl
@[simp] theorem at_1008 : prog 0x1008 = some (.mov 64 (.reg .rbp) (.reg .rsp), 0x100B) := rfl
@[simp] theorem at_100B : prog 0x100B = some (.shl 64 (.reg .rsi) 2, 0x100F) := rfl
@[simp] theorem at_100F : prog 0x100F = some (.xor 32 (.reg .rcx) (.reg .rcx), 0x1011) := rfl
@[simp] theorem at_1011 : prog 0x1011 = some (.rol32 .rax 5, 0x1014) := rfl
@[simp] theorem at_1014 : prog 0x1014 = some (.xor 32 (.reg .rax) (.memi .rdi .rcx), 0x1017) := rfl
@[simp] theorem at_1017 : prog 0x1017 = some (.mov 32 (.memi .rdi .rcx) (.reg .rax), 0x101A) := rfl
@[simp] theorem at_101A : prog 0x101A = some (.add 64 (.reg .rcx) (.imm 0x4), 0x101E) := rfl
@[simp] theorem at_101E : prog 0x101E = some (.cmp 64 (.reg .rsi) (.reg .rcx), 0x1021) := rfl
@[simp] theorem at_1021 : prog 0x1021 = some (.jcc .ne 0x1011, 0x1023) := rfl
@[simp] theorem at_1023 : prog 0x1023 = some (.pop .rbp, 0x1024) := rfl
@[simp] theorem at_1024 : prog 0x1024 = some (.ret, 0x1025) := rfl
@[simp] theorem at_1025 : prog 0x1025 = some (.push .rbp, 0x1026) := rfl
@[simp] theorem at_1026 : prog 0x1026 = some (.mov 64 (.reg .rbp) (.reg .rsp), 0x1029) := rfl
@[simp] theorem at_1029 : prog 0x1029 = some (.push .r14, 0x102B) := rfl
@[simp] theorem at_102B : prog 0x102B = some (.push .rbx, 0x102C) := rfl
@[simp] theorem at_102C : prog 0x102C = some (.mov 64 (.reg .rbx) (.reg .rcx), 0x102F) := rfl
@[simp] theorem at_102F : prog 0x102F = some (.mov 64 (.reg .r14) (.reg .rdx), 0x1032) := rfl
@[simp] theorem at_1032 : prog 0x1032 = some (.mov 32 (.reg .rdx) (.reg .r8), 0x1035) := rfl
@[simp] theorem at_1035 : prog 0x1035 = some (.call 0x1000, 0x103A) := rfl
@[simp] theorem at_103A : prog 0x103A = some (.mov 64 (.reg .rdi) (.reg .r14), 0x103D) := rfl
@[simp] theorem at_103D : prog 0x103D = some (.mov 64 (.reg .rsi) (.reg .rbx), 0x1040) := rfl
@[simp] theorem at_1040 : prog 0x1040 = some (.mov 32 (.reg .rdx) (.reg .rax), 0x1042) := rfl
@[simp] theorem at_1042 : prog 0x1042 = some (.pop .rbx, 0x1043) := rfl
@[simp] theorem at_1043 : prog 0x1043 = some (.pop .r14, 0x1045) := rfl
@[simp] theorem at_1045 : prog 0x1045 = some (.pop .rbp, 0x1046) := rfl
@[simp] theorem at_1046 : prog 0x1046 = some (.jmp 0x1000, 0x104B) := rfl

end Code
