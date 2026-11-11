import X86

/-! The compiled functions, as llvm-objdump reads them. Written by lift.py; not edited by hand. -/

namespace Code
open X86

def table : List (Nat × Instr × Nat) := [
  -- _scan
  (0x1000, .mov 32 (.reg .rax) (.reg .rdx), 0x1002),  -- 89 d0                    mov eax, edx
  (0x1002, .test 64 (.reg .rsi) (.reg .rsi), 0x1005),  -- 48 85 f6                 test rsi, rsi
  (0x1005, .jcc .e 0x1021, 0x1007),  -- 74 1a                    je 0x21 <_fold+0x21>
  (0x1007, .push .rbp, 0x1008),  -- 55                       push rbp
  (0x1008, .mov 64 (.reg .rbp) (.reg .rsp), 0x100B),  -- 48 89 e5                 mov rbp, rsp
  (0x100B, .shl 64 (.reg .rsi) 2, 0x100F),  -- 48 c1 e6 02              shl rsi, 0x2
  (0x100F, .xor 32 (.reg .rcx) (.reg .rcx), 0x1011),  -- 31 c9                    xor ecx, ecx
  (0x1011, .rol32 .rax 5, 0x1014),  -- c1 c0 05                 rol eax, 0x5
  (0x1014, .xor 32 (.reg .rax) (.memi .rdi .rcx), 0x1017),  -- 33 04 0f                 xor eax, dword ptr [rdi + rcx]
  (0x1017, .add 64 (.reg .rcx) (.imm 0x4), 0x101B),  -- 48 83 c1 04              add rcx, 0x4
  (0x101B, .cmp 64 (.reg .rsi) (.reg .rcx), 0x101E),  -- 48 39 ce                 cmp rsi, rcx
  (0x101E, .jcc .ne 0x1011, 0x1020),  -- 75 f1                    jne 0x11 <_fold+0x11>
  (0x1020, .pop .rbp, 0x1021),  -- 5d                       pop rbp
  (0x1021, .ret, 0x1022),  -- c3                       ret 
  (0x1022, .mov 32 (.reg .rax) (.reg .rdx), 0x1024),  -- 89 d0                    mov eax, edx
  (0x1024, .test 64 (.reg .rsi) (.reg .rsi), 0x1027),  -- 48 85 f6                 test rsi, rsi
  (0x1027, .jcc .e 0x1046, 0x1029),  -- 74 1d                    je 0x46 <_scan+0x24>
  (0x1029, .push .rbp, 0x102A),  -- 55                       push rbp
  (0x102A, .mov 64 (.reg .rbp) (.reg .rsp), 0x102D),  -- 48 89 e5                 mov rbp, rsp
  (0x102D, .shl 64 (.reg .rsi) 2, 0x1031),  -- 48 c1 e6 02              shl rsi, 0x2
  (0x1031, .xor 32 (.reg .rcx) (.reg .rcx), 0x1033),  -- 31 c9                    xor ecx, ecx
  (0x1033, .rol32 .rax 5, 0x1036),  -- c1 c0 05                 rol eax, 0x5
  (0x1036, .xor 32 (.reg .rax) (.memi .rdi .rcx), 0x1039),  -- 33 04 0f                 xor eax, dword ptr [rdi + rcx]
  (0x1039, .mov 32 (.memi .rdi .rcx) (.reg .rax), 0x103C),  -- 89 04 0f                 mov dword ptr [rdi + rcx], eax
  (0x103C, .add 64 (.reg .rcx) (.imm 0x4), 0x1040),  -- 48 83 c1 04              add rcx, 0x4
  (0x1040, .cmp 64 (.reg .rsi) (.reg .rcx), 0x1043),  -- 48 39 ce                 cmp rsi, rcx
  (0x1043, .jcc .ne 0x1033, 0x1045),  -- 75 ee                    jne 0x33 <_scan+0x11>
  (0x1045, .pop .rbp, 0x1046),  -- 5d                       pop rbp
  (0x1046, .ret, 0x1047)   -- c3                       ret 
]

/-- The instruction at an address, and the address after it. -/
def prog (pc : Nat) : Option (Instr × Nat) := table.lookup pc

@[simp] theorem at_1000 : prog 0x1000 = some (.mov 32 (.reg .rax) (.reg .rdx), 0x1002) := rfl
@[simp] theorem at_1002 : prog 0x1002 = some (.test 64 (.reg .rsi) (.reg .rsi), 0x1005) := rfl
@[simp] theorem at_1005 : prog 0x1005 = some (.jcc .e 0x1021, 0x1007) := rfl
@[simp] theorem at_1007 : prog 0x1007 = some (.push .rbp, 0x1008) := rfl
@[simp] theorem at_1008 : prog 0x1008 = some (.mov 64 (.reg .rbp) (.reg .rsp), 0x100B) := rfl
@[simp] theorem at_100B : prog 0x100B = some (.shl 64 (.reg .rsi) 2, 0x100F) := rfl
@[simp] theorem at_100F : prog 0x100F = some (.xor 32 (.reg .rcx) (.reg .rcx), 0x1011) := rfl
@[simp] theorem at_1011 : prog 0x1011 = some (.rol32 .rax 5, 0x1014) := rfl
@[simp] theorem at_1014 : prog 0x1014 = some (.xor 32 (.reg .rax) (.memi .rdi .rcx), 0x1017) := rfl
@[simp] theorem at_1017 : prog 0x1017 = some (.add 64 (.reg .rcx) (.imm 0x4), 0x101B) := rfl
@[simp] theorem at_101B : prog 0x101B = some (.cmp 64 (.reg .rsi) (.reg .rcx), 0x101E) := rfl
@[simp] theorem at_101E : prog 0x101E = some (.jcc .ne 0x1011, 0x1020) := rfl
@[simp] theorem at_1020 : prog 0x1020 = some (.pop .rbp, 0x1021) := rfl
@[simp] theorem at_1021 : prog 0x1021 = some (.ret, 0x1022) := rfl
@[simp] theorem at_1022 : prog 0x1022 = some (.mov 32 (.reg .rax) (.reg .rdx), 0x1024) := rfl
@[simp] theorem at_1024 : prog 0x1024 = some (.test 64 (.reg .rsi) (.reg .rsi), 0x1027) := rfl
@[simp] theorem at_1027 : prog 0x1027 = some (.jcc .e 0x1046, 0x1029) := rfl
@[simp] theorem at_1029 : prog 0x1029 = some (.push .rbp, 0x102A) := rfl
@[simp] theorem at_102A : prog 0x102A = some (.mov 64 (.reg .rbp) (.reg .rsp), 0x102D) := rfl
@[simp] theorem at_102D : prog 0x102D = some (.shl 64 (.reg .rsi) 2, 0x1031) := rfl
@[simp] theorem at_1031 : prog 0x1031 = some (.xor 32 (.reg .rcx) (.reg .rcx), 0x1033) := rfl
@[simp] theorem at_1033 : prog 0x1033 = some (.rol32 .rax 5, 0x1036) := rfl
@[simp] theorem at_1036 : prog 0x1036 = some (.xor 32 (.reg .rax) (.memi .rdi .rcx), 0x1039) := rfl
@[simp] theorem at_1039 : prog 0x1039 = some (.mov 32 (.memi .rdi .rcx) (.reg .rax), 0x103C) := rfl
@[simp] theorem at_103C : prog 0x103C = some (.add 64 (.reg .rcx) (.imm 0x4), 0x1040) := rfl
@[simp] theorem at_1040 : prog 0x1040 = some (.cmp 64 (.reg .rsi) (.reg .rcx), 0x1043) := rfl
@[simp] theorem at_1043 : prog 0x1043 = some (.jcc .ne 0x1033, 0x1045) := rfl
@[simp] theorem at_1045 : prog 0x1045 = some (.pop .rbp, 0x1046) := rfl
@[simp] theorem at_1046 : prog 0x1046 = some (.ret, 0x1047) := rfl

end Code
