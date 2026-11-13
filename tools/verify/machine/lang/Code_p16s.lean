import Machine
import KCode
import Cells
open X86

/-! `p16s` as assembled: 61 instructions. Written from the lifter's rows. -/

set_option maxRecDepth 100000
namespace Code_p16s

def table : List (Nat × Instr × Nat) := [
  (0x18000, .push .rbx, 0x18001),
  (0x18001, .push .rbp, 0x18002),
  (0x18002, .push .r12, 0x18004),
  (0x18004, .push .r13, 0x18006),
  (0x18006, .push .r14, 0x18008),
  (0x18008, .push .r15, 0x1800A),
  (0x1800A, .sub 64 (.reg .rsp) (.imm 0x28), 0x1800E),
  (0x1800E, .mov 64 (.reg .rbx) (.reg .rdi), 0x18011),
  (0x18011, .mov 64 (.reg .rbp) (.reg .rsi), 0x18014),
  (0x18014, .mov 64 (.reg .r12) (.reg .rdx), 0x18017),
  (0x18017, .mov 64 (.reg .r13) (.reg .rcx), 0x1801A),
  (0x1801A, .mov 64 (.reg .r14) (.reg .r8), 0x1801D),
  (0x1801D, .mov 64 (.reg .r15) (.reg .r9), 0x18020),
  (0x18020, .mov 64 (.reg .rax) (.reg .r14), 0x18023),
  (0x18023, .and 64 (.reg .rax) (.imm 0xFF), 0x18029),
  (0x18029, .mov 64 (.mem .rsp 0x0) (.reg .rax), 0x1802D),
  (0x1802D, .mov 64 (.reg .rax) (.imm 0x0), 0x18034),
  (0x18034, .mov 64 (.mem .rsp 0x8) (.reg .rax), 0x18039),
  (0x18039, .mov 64 (.reg .rax) (.imm 0x0), 0x18040),
  (0x18040, .mov 64 (.mem .rsp 0x10) (.reg .rax), 0x18045),
  (0x18045, .mov 64 (.reg .rax) (.imm 0x0), 0x1804C),
  (0x1804C, .mov 64 (.mem .rsp 0x18) (.reg .rax), 0x18051),
  (0x18051, .mov 64 (.reg .rax) (.mem .rsp 0x8), 0x18056),
  (0x18056, .mov 64 (.reg .rcx) (.imm 0x10), 0x1805D),
  (0x1805D, .cmp 64 (.reg .rax) (.reg .rcx), 0x18060),
  (0x18060, .jae 0x180D7, 0x18062),
  (0x18062, .mov 64 (.reg .rax) (.reg .rbx), 0x18065),
  (0x18065, .mov 64 (.reg .rcx) (.mem .rsp 0x8), 0x1806A),
  (0x1806A, .shl64 .rcx 3, 0x1806E),
  (0x1806E, .add 64 (.reg .rax) (.reg .rcx), 0x18071),
  (0x18071, .mov 64 (.reg .rax) (.mem .rax 0x0), 0x18074),
  (0x18074, .mov 64 (.mem .rsp 0x10) (.reg .rax), 0x18079),
  (0x18079, .mov 64 (.reg .rax) (.reg .r15), 0x1807C),
  (0x1807C, .mov 64 (.reg .rcx) (.mem .rsp 0x8), 0x18081),
  (0x18081, .shl64 .rcx 5, 0x18085),
  (0x18085, .add 64 (.reg .rax) (.reg .rcx), 0x18088),
  (0x18088, .mov 64 (.mem .rsp 0x18) (.reg .rax), 0x1808D),
  (0x1808D, .mov 64 (.reg .rax) (.reg .r12), 0x18090),
  (0x18090, .mov 64 (.reg .rcx) (.mem .rsp 0x18), 0x18095),
  (0x18095, .movv false 0 (.m .rax 0x0), 0x18098),
  (0x18098, .storev false .rcx 0x0 0, 0x1809B),
  (0x1809B, .movv false 0 (.m .rax 0x10), 0x1809F),
  (0x1809F, .storev false .rcx 0x10 0, 0x180A3),
  (0x180A3, .mov 64 (.reg .rdi) (.mem .rsp 0x18), 0x180A8),
  (0x180A8, .mov 64 (.reg .rsi) (.mem .rsp 0x10), 0x180AD),
  (0x180AD, .mov 64 (.reg .rdx) (.imm 0x40), 0x180B4),
  (0x180B4, .mov 64 (.reg .rcx) (.imm 0x0), 0x180BB),
  (0x180BB, .mov 64 (.reg .r8) (.mem .rsp 0x0), 0x180BF),
  (0x180BF, .call 0x30000, 0x180C4),
  (0x180C4, .mov 64 (.reg .rax) (.mem .rsp 0x8), 0x180C9),
  (0x180C9, .add 64 (.reg .rax) (.imm 0x1), 0x180CD),
  (0x180CD, .mov 64 (.mem .rsp 0x8) (.reg .rax), 0x180D2),
  (0x180D2, .jmp 0x18051, 0x180D7),
  (0x180D7, .add 64 (.reg .rsp) (.imm 0x28), 0x180DB),
  (0x180DB, .pop .r15, 0x180DD),
  (0x180DD, .pop .r14, 0x180DF),
  (0x180DF, .pop .r13, 0x180E1),
  (0x180E1, .pop .r12, 0x180E3),
  (0x180E3, .pop .rbp, 0x180E4),
  (0x180E4, .pop .rbx, 0x180E5),
  (0x180E5, .ret, 0x180E6)
]

def pre0 : List (Nat × Instr × Nat) := KCode.table

/-- Every instruction of the program: the two kernels' (one/KCode.lean), then this function's. -/
def whole : List (Nat × Instr × Nat) := pre0 ++ table

def prog (pc : Nat) : Option (Instr × Nat) := whole.lookup pc

/-- The addresses the program has an instruction at. -/
def keys : List Nat := whole.map (·.1)

theorem keys_of : ∀ pc x, prog pc = some x → pc ∈ keys := fun pc x h => lookup_mem_keys whole pc x h

theorem has_kernels : ∀ pc x, KCode.prog pc = some x → prog pc = some x := by
  intro pc x h
  exact lookup_append_left pre0 table pc x (h)

@[ode_at] theorem at_18000 : prog 0x18000 = some (.push .rbx, 0x18001) := rfl
@[ode_at] theorem at_18001 : prog 0x18001 = some (.push .rbp, 0x18002) := rfl
@[ode_at] theorem at_18002 : prog 0x18002 = some (.push .r12, 0x18004) := rfl
@[ode_at] theorem at_18004 : prog 0x18004 = some (.push .r13, 0x18006) := rfl
@[ode_at] theorem at_18006 : prog 0x18006 = some (.push .r14, 0x18008) := rfl
@[ode_at] theorem at_18008 : prog 0x18008 = some (.push .r15, 0x1800A) := rfl
@[ode_at] theorem at_1800A : prog 0x1800A = some (.sub 64 (.reg .rsp) (.imm 0x28), 0x1800E) := rfl
@[ode_at] theorem at_1800E : prog 0x1800E = some (.mov 64 (.reg .rbx) (.reg .rdi), 0x18011) := rfl
@[ode_at] theorem at_18011 : prog 0x18011 = some (.mov 64 (.reg .rbp) (.reg .rsi), 0x18014) := rfl
@[ode_at] theorem at_18014 : prog 0x18014 = some (.mov 64 (.reg .r12) (.reg .rdx), 0x18017) := rfl
@[ode_at] theorem at_18017 : prog 0x18017 = some (.mov 64 (.reg .r13) (.reg .rcx), 0x1801A) := rfl
@[ode_at] theorem at_1801A : prog 0x1801A = some (.mov 64 (.reg .r14) (.reg .r8), 0x1801D) := rfl
@[ode_at] theorem at_1801D : prog 0x1801D = some (.mov 64 (.reg .r15) (.reg .r9), 0x18020) := rfl
@[ode_at] theorem at_18020 : prog 0x18020 = some (.mov 64 (.reg .rax) (.reg .r14), 0x18023) := rfl
@[ode_at] theorem at_18023 : prog 0x18023 = some (.and 64 (.reg .rax) (.imm 0xFF), 0x18029) := rfl
@[ode_at] theorem at_18029 : prog 0x18029 = some (.mov 64 (.mem .rsp 0x0) (.reg .rax), 0x1802D) := rfl
@[ode_at] theorem at_1802D : prog 0x1802D = some (.mov 64 (.reg .rax) (.imm 0x0), 0x18034) := rfl
@[ode_at] theorem at_18034 : prog 0x18034 = some (.mov 64 (.mem .rsp 0x8) (.reg .rax), 0x18039) := rfl
@[ode_at] theorem at_18039 : prog 0x18039 = some (.mov 64 (.reg .rax) (.imm 0x0), 0x18040) := rfl
@[ode_at] theorem at_18040 : prog 0x18040 = some (.mov 64 (.mem .rsp 0x10) (.reg .rax), 0x18045) := rfl
@[ode_at] theorem at_18045 : prog 0x18045 = some (.mov 64 (.reg .rax) (.imm 0x0), 0x1804C) := rfl
@[ode_at] theorem at_1804C : prog 0x1804C = some (.mov 64 (.mem .rsp 0x18) (.reg .rax), 0x18051) := rfl
@[ode_at] theorem at_18051 : prog 0x18051 = some (.mov 64 (.reg .rax) (.mem .rsp 0x8), 0x18056) := rfl
@[ode_at] theorem at_18056 : prog 0x18056 = some (.mov 64 (.reg .rcx) (.imm 0x10), 0x1805D) := rfl
@[ode_at] theorem at_1805D : prog 0x1805D = some (.cmp 64 (.reg .rax) (.reg .rcx), 0x18060) := rfl
@[ode_at] theorem at_18060 : prog 0x18060 = some (.jae 0x180D7, 0x18062) := rfl
@[ode_at] theorem at_18062 : prog 0x18062 = some (.mov 64 (.reg .rax) (.reg .rbx), 0x18065) := rfl
@[ode_at] theorem at_18065 : prog 0x18065 = some (.mov 64 (.reg .rcx) (.mem .rsp 0x8), 0x1806A) := rfl
@[ode_at] theorem at_1806A : prog 0x1806A = some (.shl64 .rcx 3, 0x1806E) := rfl
@[ode_at] theorem at_1806E : prog 0x1806E = some (.add 64 (.reg .rax) (.reg .rcx), 0x18071) := rfl
@[ode_at] theorem at_18071 : prog 0x18071 = some (.mov 64 (.reg .rax) (.mem .rax 0x0), 0x18074) := rfl
@[ode_at] theorem at_18074 : prog 0x18074 = some (.mov 64 (.mem .rsp 0x10) (.reg .rax), 0x18079) := rfl
@[ode_at] theorem at_18079 : prog 0x18079 = some (.mov 64 (.reg .rax) (.reg .r15), 0x1807C) := rfl
@[ode_at] theorem at_1807C : prog 0x1807C = some (.mov 64 (.reg .rcx) (.mem .rsp 0x8), 0x18081) := rfl
@[ode_at] theorem at_18081 : prog 0x18081 = some (.shl64 .rcx 5, 0x18085) := rfl
@[ode_at] theorem at_18085 : prog 0x18085 = some (.add 64 (.reg .rax) (.reg .rcx), 0x18088) := rfl
@[ode_at] theorem at_18088 : prog 0x18088 = some (.mov 64 (.mem .rsp 0x18) (.reg .rax), 0x1808D) := rfl
@[ode_at] theorem at_1808D : prog 0x1808D = some (.mov 64 (.reg .rax) (.reg .r12), 0x18090) := rfl
@[ode_at] theorem at_18090 : prog 0x18090 = some (.mov 64 (.reg .rcx) (.mem .rsp 0x18), 0x18095) := rfl
@[ode_at] theorem at_18095 : prog 0x18095 = some (.movv false 0 (.m .rax 0x0), 0x18098) := rfl
@[ode_at] theorem at_18098 : prog 0x18098 = some (.storev false .rcx 0x0 0, 0x1809B) := rfl
@[ode_at] theorem at_1809B : prog 0x1809B = some (.movv false 0 (.m .rax 0x10), 0x1809F) := rfl
@[ode_at] theorem at_1809F : prog 0x1809F = some (.storev false .rcx 0x10 0, 0x180A3) := rfl
@[ode_at] theorem at_180A3 : prog 0x180A3 = some (.mov 64 (.reg .rdi) (.mem .rsp 0x18), 0x180A8) := rfl
@[ode_at] theorem at_180A8 : prog 0x180A8 = some (.mov 64 (.reg .rsi) (.mem .rsp 0x10), 0x180AD) := rfl
@[ode_at] theorem at_180AD : prog 0x180AD = some (.mov 64 (.reg .rdx) (.imm 0x40), 0x180B4) := rfl
@[ode_at] theorem at_180B4 : prog 0x180B4 = some (.mov 64 (.reg .rcx) (.imm 0x0), 0x180BB) := rfl
@[ode_at] theorem at_180BB : prog 0x180BB = some (.mov 64 (.reg .r8) (.mem .rsp 0x0), 0x180BF) := rfl
@[ode_at] theorem at_180BF : prog 0x180BF = some (.call 0x30000, 0x180C4) := rfl
@[ode_at] theorem at_180C4 : prog 0x180C4 = some (.mov 64 (.reg .rax) (.mem .rsp 0x8), 0x180C9) := rfl
@[ode_at] theorem at_180C9 : prog 0x180C9 = some (.add 64 (.reg .rax) (.imm 0x1), 0x180CD) := rfl
@[ode_at] theorem at_180CD : prog 0x180CD = some (.mov 64 (.mem .rsp 0x8) (.reg .rax), 0x180D2) := rfl
@[ode_at] theorem at_180D2 : prog 0x180D2 = some (.jmp 0x18051, 0x180D7) := rfl
@[ode_at] theorem at_180D7 : prog 0x180D7 = some (.add 64 (.reg .rsp) (.imm 0x28), 0x180DB) := rfl
@[ode_at] theorem at_180DB : prog 0x180DB = some (.pop .r15, 0x180DD) := rfl
@[ode_at] theorem at_180DD : prog 0x180DD = some (.pop .r14, 0x180DF) := rfl
@[ode_at] theorem at_180DF : prog 0x180DF = some (.pop .r13, 0x180E1) := rfl
@[ode_at] theorem at_180E1 : prog 0x180E1 = some (.pop .r12, 0x180E3) := rfl
@[ode_at] theorem at_180E3 : prog 0x180E3 = some (.pop .rbp, 0x180E4) := rfl
@[ode_at] theorem at_180E4 : prog 0x180E4 = some (.pop .rbx, 0x180E5) := rfl
@[ode_at] theorem at_180E5 : prog 0x180E5 = some (.ret, 0x180E6) := rfl

end Code_p16s
