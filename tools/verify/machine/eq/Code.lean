import X86
import Attr

/-! `constant_time_eq::constant_time_eq_32` (0.4.2), which `Hash == Hash` is, as rustc 1.99.1 compiled it and
llvm-objdump reads it. Written by lift_eq.py; not edited by hand. -/

namespace Code
open X86

def table : List (Nat × Instr × Nat) := [
  (0x1000, .push .rbp, 0x1001),  -- 55                       push rbp
  (0x1001, .mov 64 (.reg .rbp) (.reg .rsp), 0x1004),  -- 48 89 e5                 mov rbp, rsp
  (0x1004, .loadv 0 (.mem .rdi 0x0), 0x1007),  -- 0f 10 07                 movups xmm0, xmmword ptr [rdi]
  (0x1007, .loadv 1 (.mem .rdi 0x10), 0x100B),  -- 0f 10 4f 10              movups xmm1, xmmword ptr [rdi + 0x10]
  (0x100B, .loadv 2 (.mem .rsi 0x0), 0x100E),  -- 0f 10 16                 movups xmm2, xmmword ptr [rsi]
  (0x100E, .loadv 3 (.mem .rsi 0x10), 0x1012),  -- 0f 10 5e 10              movups xmm3, xmmword ptr [rsi + 0x10]
  (0x1012, .pcmpeqb 0 2, 0x1016),  -- 66 0f 74 c2              pcmpeqb xmm0, xmm2
  (0x1016, .pcmpeqb 1 3, 0x101A),  -- 66 0f 74 cb              pcmpeqb xmm1, xmm3
  (0x101A, .pand 0 1, 0x101E),  -- 66 0f db c1              pand xmm0, xmm1
  (0x101E, .pmovmskb .rax 0, 0x1022),  -- 66 0f d7 c0              pmovmskb eax, xmm0
  (0x1022, .cmp 32 (.reg .rax) (.imm 0xFFFF), 0x1027),  -- 3d ff ff 00 00           cmp eax, 0xffff
  (0x1027, .sete .rax, 0x102A),  -- 0f 94 c0                 sete al
  (0x102A, .pop .rbp, 0x102B),  -- 5d                       pop rbp
  (0x102B, .ret, 0x102C)   -- c3                       ret 
]

def prog (pc : Nat) : Option (Instr × Nat) := table.lookup pc

@[code_at] theorem at_1000 : prog 0x1000 = some (.push .rbp, 0x1001) := rfl
@[code_at] theorem at_1001 : prog 0x1001 = some (.mov 64 (.reg .rbp) (.reg .rsp), 0x1004) := rfl
@[code_at] theorem at_1004 : prog 0x1004 = some (.loadv 0 (.mem .rdi 0x0), 0x1007) := rfl
@[code_at] theorem at_1007 : prog 0x1007 = some (.loadv 1 (.mem .rdi 0x10), 0x100B) := rfl
@[code_at] theorem at_100B : prog 0x100B = some (.loadv 2 (.mem .rsi 0x0), 0x100E) := rfl
@[code_at] theorem at_100E : prog 0x100E = some (.loadv 3 (.mem .rsi 0x10), 0x1012) := rfl
@[code_at] theorem at_1012 : prog 0x1012 = some (.pcmpeqb 0 2, 0x1016) := rfl
@[code_at] theorem at_1016 : prog 0x1016 = some (.pcmpeqb 1 3, 0x101A) := rfl
@[code_at] theorem at_101A : prog 0x101A = some (.pand 0 1, 0x101E) := rfl
@[code_at] theorem at_101E : prog 0x101E = some (.pmovmskb .rax 0, 0x1022) := rfl
@[code_at] theorem at_1022 : prog 0x1022 = some (.cmp 32 (.reg .rax) (.imm 0xFFFF), 0x1027) := rfl
@[code_at] theorem at_1027 : prog 0x1027 = some (.sete .rax, 0x102A) := rfl
@[code_at] theorem at_102A : prog 0x102A = some (.pop .rbp, 0x102B) := rfl
@[code_at] theorem at_102B : prog 0x102B = some (.ret, 0x102C) := rfl

end Code
