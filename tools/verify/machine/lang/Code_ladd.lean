import Machine
import KCode
import Cells
open X86

/-! `ladd` as assembled: 95 instructions. Written from the lifter's rows. -/

set_option maxRecDepth 100000
namespace Code_ladd

def table : List (Nat × Instr × Nat) := [
  (0xB0000, .push .rbx, 0xB0001),
  (0xB0001, .push .rbp, 0xB0002),
  (0xB0002, .push .r12, 0xB0004),
  (0xB0004, .push .r13, 0xB0006),
  (0xB0006, .push .r14, 0xB0008),
  (0xB0008, .push .r15, 0xB000A),
  (0xB000A, .sub 64 (.reg .rsp) (.imm 0x28), 0xB000E),
  (0xB000E, .mov 64 (.reg .r12) (.reg .rdi), 0xB0011),
  (0xB0011, .mov 64 (.reg .r13) (.reg .rsi), 0xB0014),
  (0xB0014, .mov 64 (.mem .rsp 0x0) (.reg .rdx), 0xB0018),
  (0xB0018, .mov 64 (.reg .r14) (.reg .rcx), 0xB001B),
  (0xB001B, .mov 64 (.mem .rsp 0x8) (.reg .r8), 0xB0020),
  (0xB0020, .mov 64 (.reg .rax) (.mem .rsp 0x0), 0xB0024),
  (0xB0024, .or 64 (.reg .rax) (.imm 0x4), 0xB0028),
  (0xB0028, .mov 64 (.mem .rsp 0x10) (.reg .rax), 0xB002D),
  (0xB002D, .mov 64 (.reg .rax) (.reg .r12), 0xB0030),
  (0xB0030, .mov 64 (.reg .rax) (.mem .rax 0x0), 0xB0033),
  (0xB0033, .mov 64 (.mem .rsp 0x18) (.reg .rax), 0xB0038),
  (0xB0038, .mov 64 (.reg .rax) (.mem .rsp 0x18), 0xB003D),
  (0xB003D, .mov 64 (.reg .rcx) (.mem .rsp 0x18), 0xB0042),
  (0xB0042, .sub 64 (.reg .rcx) (.imm 0x1), 0xB0046),
  (0xB0046, .shr64 .rcx 63, 0xB004A),
  (0xB004A, .or 64 (.reg .rax) (.reg .rcx), 0xB004D),
  (0xB004D, .mov 64 (.reg .rbx) (.reg .rax), 0xB0050),
  (0xB0050, .mov 64 (.reg .rax) (.reg .r12), 0xB0053),
  (0xB0053, .add 64 (.reg .rax) (.imm 0x40), 0xB0057),
  (0xB0057, .mov 64 (.reg .rbp) (.reg .rax), 0xB005A),
  (0xB005A, .mov 64 (.reg .rax) (.reg .rbx), 0xB005D),
  (0xB005D, .and 64 (.reg .rax) (.imm 0x1), 0xB0061),
  (0xB0061, .mov 64 (.reg .rcx) (.imm 0x0), 0xB0068),
  (0xB0068, .cmp 64 (.reg .rax) (.reg .rcx), 0xB006B),
  (0xB006B, .jne 0xB0106, 0xB0071),
  (0xB0071, .mov 64 (.reg .rax) (.reg .rbx), 0xB0074),
  (0xB0074, .shr64 .rax 1, 0xB0077),
  (0xB0077, .mov 64 (.reg .rbx) (.reg .rax), 0xB007A),
  (0xB007A, .mov 64 (.reg .rax) (.reg .rbp), 0xB007D),
  (0xB007D, .add 64 (.reg .rax) (.imm 0x40), 0xB0081),
  (0xB0081, .mov 64 (.reg .rcx) (.reg .rbx), 0xB0084),
  (0xB0084, .add 64 (.reg .rcx) (.imm 0x1), 0xB0088),
  (0xB0088, .and 64 (.reg .rcx) (.imm 0x1), 0xB008C),
  (0xB008C, .shl64 .rcx 5, 0xB0090),
  (0xB0090, .add 64 (.reg .rax) (.reg .rcx), 0xB0093),
  (0xB0093, .mov 64 (.reg .r15) (.reg .rax), 0xB0096),
  (0xB0096, .mov 64 (.reg .rax) (.reg .r13), 0xB0099),
  (0xB0099, .mov 64 (.reg .rcx) (.reg .r15), 0xB009C),
  (0xB009C, .movv false 0 (.m .rax 0x0), 0xB009F),
  (0xB009F, .storev false .rcx 0x0 0, 0xB00A2),
  (0xB00A2, .movv false 0 (.m .rax 0x10), 0xB00A6),
  (0xB00A6, .storev false .rcx 0x10 0, 0xB00AA),
  (0xB00AA, .mov 64 (.reg .rax) (.reg .r14), 0xB00AD),
  (0xB00AD, .mov 64 (.reg .rcx) (.imm 0x5), 0xB00B4),
  (0xB00B4, .cmp 64 (.reg .rax) (.reg .rcx), 0xB00B7),
  (0xB00B7, .jne 0xB00D9, 0xB00B9),
  (0xB00B9, .mov 64 (.reg .rdi) (.reg .r15), 0xB00BC),
  (0xB00BC, .mov 64 (.reg .rsi) (.reg .rbp), 0xB00BF),
  (0xB00BF, .mov 64 (.reg .rdx) (.imm 0x40), 0xB00C6),
  (0xB00C6, .mov 64 (.reg .rcx) (.imm 0x0), 0xB00CD),
  (0xB00CD, .mov 64 (.reg .r8) (.mem .rsp 0x10), 0xB00D2),
  (0xB00D2, .call 0x30000, 0xB00D7),
  (0xB00D7, .jmp 0xB00F7, 0xB00D9),
  (0xB00D9, .mov 64 (.reg .rdi) (.reg .r15), 0xB00DC),
  (0xB00DC, .mov 64 (.reg .rsi) (.reg .rbp), 0xB00DF),
  (0xB00DF, .mov 64 (.reg .rdx) (.imm 0x40), 0xB00E6),
  (0xB00E6, .mov 64 (.reg .rcx) (.imm 0x0), 0xB00ED),
  (0xB00ED, .mov 64 (.reg .r8) (.mem .rsp 0x10), 0xB00F2),
  (0xB00F2, .call 0x20000, 0xB00F7),
  (0xB00F7, .mov 64 (.reg .rax) (.reg .rbp), 0xB00FA),
  (0xB00FA, .add 64 (.reg .rax) (.imm 0x40), 0xB00FE),
  (0xB00FE, .mov 64 (.reg .rbp) (.reg .rax), 0xB0101),
  (0xB0101, .jmp 0xB005A, 0xB0106),
  (0xB0106, .mov 64 (.reg .rax) (.mem .rsp 0x8), 0xB010B),
  (0xB010B, .mov 64 (.reg .rcx) (.reg .r12), 0xB010E),
  (0xB010E, .add 64 (.reg .rcx) (.imm 0x40), 0xB0112),
  (0xB0112, .mov 64 (.reg .rdx) (.mem .rsp 0x18), 0xB0117),
  (0xB0117, .and 64 (.reg .rdx) (.imm 0x1), 0xB011B),
  (0xB011B, .shl64 .rdx 5, 0xB011F),
  (0xB011F, .add 64 (.reg .rcx) (.reg .rdx), 0xB0122),
  (0xB0122, .movv false 0 (.m .rax 0x0), 0xB0125),
  (0xB0125, .storev false .rcx 0x0 0, 0xB0128),
  (0xB0128, .movv false 0 (.m .rax 0x10), 0xB012C),
  (0xB012C, .storev false .rcx 0x10 0, 0xB0130),
  (0xB0130, .mov 64 (.reg .rax) (.mem .rsp 0x18), 0xB0135),
  (0xB0135, .add 64 (.reg .rax) (.imm 0x1), 0xB0139),
  (0xB0139, .mov 64 (.reg .rcx) (.reg .r12), 0xB013C),
  (0xB013C, .mov 64 (.mem .rcx 0x0) (.reg .rax), 0xB013F),
  (0xB013F, .mov 64 (.reg .rax) (.mem .rsp 0x18), 0xB0144),
  (0xB0144, .add 64 (.reg .rax) (.imm 0x1), 0xB0148),
  (0xB0148, .add 64 (.reg .rsp) (.imm 0x28), 0xB014C),
  (0xB014C, .pop .r15, 0xB014E),
  (0xB014E, .pop .r14, 0xB0150),
  (0xB0150, .pop .r13, 0xB0152),
  (0xB0152, .pop .r12, 0xB0154),
  (0xB0154, .pop .rbp, 0xB0155),
  (0xB0155, .pop .rbx, 0xB0156),
  (0xB0156, .ret, 0xB0157)
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

@[ode_at] theorem at_B0000 : prog 0xB0000 = some (.push .rbx, 0xB0001) := rfl
@[ode_at] theorem at_B0001 : prog 0xB0001 = some (.push .rbp, 0xB0002) := rfl
@[ode_at] theorem at_B0002 : prog 0xB0002 = some (.push .r12, 0xB0004) := rfl
@[ode_at] theorem at_B0004 : prog 0xB0004 = some (.push .r13, 0xB0006) := rfl
@[ode_at] theorem at_B0006 : prog 0xB0006 = some (.push .r14, 0xB0008) := rfl
@[ode_at] theorem at_B0008 : prog 0xB0008 = some (.push .r15, 0xB000A) := rfl
@[ode_at] theorem at_B000A : prog 0xB000A = some (.sub 64 (.reg .rsp) (.imm 0x28), 0xB000E) := rfl
@[ode_at] theorem at_B000E : prog 0xB000E = some (.mov 64 (.reg .r12) (.reg .rdi), 0xB0011) := rfl
@[ode_at] theorem at_B0011 : prog 0xB0011 = some (.mov 64 (.reg .r13) (.reg .rsi), 0xB0014) := rfl
@[ode_at] theorem at_B0014 : prog 0xB0014 = some (.mov 64 (.mem .rsp 0x0) (.reg .rdx), 0xB0018) := rfl
@[ode_at] theorem at_B0018 : prog 0xB0018 = some (.mov 64 (.reg .r14) (.reg .rcx), 0xB001B) := rfl
@[ode_at] theorem at_B001B : prog 0xB001B = some (.mov 64 (.mem .rsp 0x8) (.reg .r8), 0xB0020) := rfl
@[ode_at] theorem at_B0020 : prog 0xB0020 = some (.mov 64 (.reg .rax) (.mem .rsp 0x0), 0xB0024) := rfl
@[ode_at] theorem at_B0024 : prog 0xB0024 = some (.or 64 (.reg .rax) (.imm 0x4), 0xB0028) := rfl
@[ode_at] theorem at_B0028 : prog 0xB0028 = some (.mov 64 (.mem .rsp 0x10) (.reg .rax), 0xB002D) := rfl
@[ode_at] theorem at_B002D : prog 0xB002D = some (.mov 64 (.reg .rax) (.reg .r12), 0xB0030) := rfl
@[ode_at] theorem at_B0030 : prog 0xB0030 = some (.mov 64 (.reg .rax) (.mem .rax 0x0), 0xB0033) := rfl
@[ode_at] theorem at_B0033 : prog 0xB0033 = some (.mov 64 (.mem .rsp 0x18) (.reg .rax), 0xB0038) := rfl
@[ode_at] theorem at_B0038 : prog 0xB0038 = some (.mov 64 (.reg .rax) (.mem .rsp 0x18), 0xB003D) := rfl
@[ode_at] theorem at_B003D : prog 0xB003D = some (.mov 64 (.reg .rcx) (.mem .rsp 0x18), 0xB0042) := rfl
@[ode_at] theorem at_B0042 : prog 0xB0042 = some (.sub 64 (.reg .rcx) (.imm 0x1), 0xB0046) := rfl
@[ode_at] theorem at_B0046 : prog 0xB0046 = some (.shr64 .rcx 63, 0xB004A) := rfl
@[ode_at] theorem at_B004A : prog 0xB004A = some (.or 64 (.reg .rax) (.reg .rcx), 0xB004D) := rfl
@[ode_at] theorem at_B004D : prog 0xB004D = some (.mov 64 (.reg .rbx) (.reg .rax), 0xB0050) := rfl
@[ode_at] theorem at_B0050 : prog 0xB0050 = some (.mov 64 (.reg .rax) (.reg .r12), 0xB0053) := rfl
@[ode_at] theorem at_B0053 : prog 0xB0053 = some (.add 64 (.reg .rax) (.imm 0x40), 0xB0057) := rfl
@[ode_at] theorem at_B0057 : prog 0xB0057 = some (.mov 64 (.reg .rbp) (.reg .rax), 0xB005A) := rfl
@[ode_at] theorem at_B005A : prog 0xB005A = some (.mov 64 (.reg .rax) (.reg .rbx), 0xB005D) := rfl
@[ode_at] theorem at_B005D : prog 0xB005D = some (.and 64 (.reg .rax) (.imm 0x1), 0xB0061) := rfl
@[ode_at] theorem at_B0061 : prog 0xB0061 = some (.mov 64 (.reg .rcx) (.imm 0x0), 0xB0068) := rfl
@[ode_at] theorem at_B0068 : prog 0xB0068 = some (.cmp 64 (.reg .rax) (.reg .rcx), 0xB006B) := rfl
@[ode_at] theorem at_B006B : prog 0xB006B = some (.jne 0xB0106, 0xB0071) := rfl
@[ode_at] theorem at_B0071 : prog 0xB0071 = some (.mov 64 (.reg .rax) (.reg .rbx), 0xB0074) := rfl
@[ode_at] theorem at_B0074 : prog 0xB0074 = some (.shr64 .rax 1, 0xB0077) := rfl
@[ode_at] theorem at_B0077 : prog 0xB0077 = some (.mov 64 (.reg .rbx) (.reg .rax), 0xB007A) := rfl
@[ode_at] theorem at_B007A : prog 0xB007A = some (.mov 64 (.reg .rax) (.reg .rbp), 0xB007D) := rfl
@[ode_at] theorem at_B007D : prog 0xB007D = some (.add 64 (.reg .rax) (.imm 0x40), 0xB0081) := rfl
@[ode_at] theorem at_B0081 : prog 0xB0081 = some (.mov 64 (.reg .rcx) (.reg .rbx), 0xB0084) := rfl
@[ode_at] theorem at_B0084 : prog 0xB0084 = some (.add 64 (.reg .rcx) (.imm 0x1), 0xB0088) := rfl
@[ode_at] theorem at_B0088 : prog 0xB0088 = some (.and 64 (.reg .rcx) (.imm 0x1), 0xB008C) := rfl
@[ode_at] theorem at_B008C : prog 0xB008C = some (.shl64 .rcx 5, 0xB0090) := rfl
@[ode_at] theorem at_B0090 : prog 0xB0090 = some (.add 64 (.reg .rax) (.reg .rcx), 0xB0093) := rfl
@[ode_at] theorem at_B0093 : prog 0xB0093 = some (.mov 64 (.reg .r15) (.reg .rax), 0xB0096) := rfl
@[ode_at] theorem at_B0096 : prog 0xB0096 = some (.mov 64 (.reg .rax) (.reg .r13), 0xB0099) := rfl
@[ode_at] theorem at_B0099 : prog 0xB0099 = some (.mov 64 (.reg .rcx) (.reg .r15), 0xB009C) := rfl
@[ode_at] theorem at_B009C : prog 0xB009C = some (.movv false 0 (.m .rax 0x0), 0xB009F) := rfl
@[ode_at] theorem at_B009F : prog 0xB009F = some (.storev false .rcx 0x0 0, 0xB00A2) := rfl
@[ode_at] theorem at_B00A2 : prog 0xB00A2 = some (.movv false 0 (.m .rax 0x10), 0xB00A6) := rfl
@[ode_at] theorem at_B00A6 : prog 0xB00A6 = some (.storev false .rcx 0x10 0, 0xB00AA) := rfl
@[ode_at] theorem at_B00AA : prog 0xB00AA = some (.mov 64 (.reg .rax) (.reg .r14), 0xB00AD) := rfl
@[ode_at] theorem at_B00AD : prog 0xB00AD = some (.mov 64 (.reg .rcx) (.imm 0x5), 0xB00B4) := rfl
@[ode_at] theorem at_B00B4 : prog 0xB00B4 = some (.cmp 64 (.reg .rax) (.reg .rcx), 0xB00B7) := rfl
@[ode_at] theorem at_B00B7 : prog 0xB00B7 = some (.jne 0xB00D9, 0xB00B9) := rfl
@[ode_at] theorem at_B00B9 : prog 0xB00B9 = some (.mov 64 (.reg .rdi) (.reg .r15), 0xB00BC) := rfl
@[ode_at] theorem at_B00BC : prog 0xB00BC = some (.mov 64 (.reg .rsi) (.reg .rbp), 0xB00BF) := rfl
@[ode_at] theorem at_B00BF : prog 0xB00BF = some (.mov 64 (.reg .rdx) (.imm 0x40), 0xB00C6) := rfl
@[ode_at] theorem at_B00C6 : prog 0xB00C6 = some (.mov 64 (.reg .rcx) (.imm 0x0), 0xB00CD) := rfl
@[ode_at] theorem at_B00CD : prog 0xB00CD = some (.mov 64 (.reg .r8) (.mem .rsp 0x10), 0xB00D2) := rfl
@[ode_at] theorem at_B00D2 : prog 0xB00D2 = some (.call 0x30000, 0xB00D7) := rfl
@[ode_at] theorem at_B00D7 : prog 0xB00D7 = some (.jmp 0xB00F7, 0xB00D9) := rfl
@[ode_at] theorem at_B00D9 : prog 0xB00D9 = some (.mov 64 (.reg .rdi) (.reg .r15), 0xB00DC) := rfl
@[ode_at] theorem at_B00DC : prog 0xB00DC = some (.mov 64 (.reg .rsi) (.reg .rbp), 0xB00DF) := rfl
@[ode_at] theorem at_B00DF : prog 0xB00DF = some (.mov 64 (.reg .rdx) (.imm 0x40), 0xB00E6) := rfl
@[ode_at] theorem at_B00E6 : prog 0xB00E6 = some (.mov 64 (.reg .rcx) (.imm 0x0), 0xB00ED) := rfl
@[ode_at] theorem at_B00ED : prog 0xB00ED = some (.mov 64 (.reg .r8) (.mem .rsp 0x10), 0xB00F2) := rfl
@[ode_at] theorem at_B00F2 : prog 0xB00F2 = some (.call 0x20000, 0xB00F7) := rfl
@[ode_at] theorem at_B00F7 : prog 0xB00F7 = some (.mov 64 (.reg .rax) (.reg .rbp), 0xB00FA) := rfl
@[ode_at] theorem at_B00FA : prog 0xB00FA = some (.add 64 (.reg .rax) (.imm 0x40), 0xB00FE) := rfl
@[ode_at] theorem at_B00FE : prog 0xB00FE = some (.mov 64 (.reg .rbp) (.reg .rax), 0xB0101) := rfl
@[ode_at] theorem at_B0101 : prog 0xB0101 = some (.jmp 0xB005A, 0xB0106) := rfl
@[ode_at] theorem at_B0106 : prog 0xB0106 = some (.mov 64 (.reg .rax) (.mem .rsp 0x8), 0xB010B) := rfl
@[ode_at] theorem at_B010B : prog 0xB010B = some (.mov 64 (.reg .rcx) (.reg .r12), 0xB010E) := rfl
@[ode_at] theorem at_B010E : prog 0xB010E = some (.add 64 (.reg .rcx) (.imm 0x40), 0xB0112) := rfl
@[ode_at] theorem at_B0112 : prog 0xB0112 = some (.mov 64 (.reg .rdx) (.mem .rsp 0x18), 0xB0117) := rfl
@[ode_at] theorem at_B0117 : prog 0xB0117 = some (.and 64 (.reg .rdx) (.imm 0x1), 0xB011B) := rfl
@[ode_at] theorem at_B011B : prog 0xB011B = some (.shl64 .rdx 5, 0xB011F) := rfl
@[ode_at] theorem at_B011F : prog 0xB011F = some (.add 64 (.reg .rcx) (.reg .rdx), 0xB0122) := rfl
@[ode_at] theorem at_B0122 : prog 0xB0122 = some (.movv false 0 (.m .rax 0x0), 0xB0125) := rfl
@[ode_at] theorem at_B0125 : prog 0xB0125 = some (.storev false .rcx 0x0 0, 0xB0128) := rfl
@[ode_at] theorem at_B0128 : prog 0xB0128 = some (.movv false 0 (.m .rax 0x10), 0xB012C) := rfl
@[ode_at] theorem at_B012C : prog 0xB012C = some (.storev false .rcx 0x10 0, 0xB0130) := rfl
@[ode_at] theorem at_B0130 : prog 0xB0130 = some (.mov 64 (.reg .rax) (.mem .rsp 0x18), 0xB0135) := rfl
@[ode_at] theorem at_B0135 : prog 0xB0135 = some (.add 64 (.reg .rax) (.imm 0x1), 0xB0139) := rfl
@[ode_at] theorem at_B0139 : prog 0xB0139 = some (.mov 64 (.reg .rcx) (.reg .r12), 0xB013C) := rfl
@[ode_at] theorem at_B013C : prog 0xB013C = some (.mov 64 (.mem .rcx 0x0) (.reg .rax), 0xB013F) := rfl
@[ode_at] theorem at_B013F : prog 0xB013F = some (.mov 64 (.reg .rax) (.mem .rsp 0x18), 0xB0144) := rfl
@[ode_at] theorem at_B0144 : prog 0xB0144 = some (.add 64 (.reg .rax) (.imm 0x1), 0xB0148) := rfl
@[ode_at] theorem at_B0148 : prog 0xB0148 = some (.add 64 (.reg .rsp) (.imm 0x28), 0xB014C) := rfl
@[ode_at] theorem at_B014C : prog 0xB014C = some (.pop .r15, 0xB014E) := rfl
@[ode_at] theorem at_B014E : prog 0xB014E = some (.pop .r14, 0xB0150) := rfl
@[ode_at] theorem at_B0150 : prog 0xB0150 = some (.pop .r13, 0xB0152) := rfl
@[ode_at] theorem at_B0152 : prog 0xB0152 = some (.pop .r12, 0xB0154) := rfl
@[ode_at] theorem at_B0154 : prog 0xB0154 = some (.pop .rbp, 0xB0155) := rfl
@[ode_at] theorem at_B0155 : prog 0xB0155 = some (.pop .rbx, 0xB0156) := rfl
@[ode_at] theorem at_B0156 : prog 0xB0156 = some (.ret, 0xB0157) := rfl

end Code_ladd
