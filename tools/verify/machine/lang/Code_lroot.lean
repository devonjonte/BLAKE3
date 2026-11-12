import Machine
import KCode
import Cells
open X86

/-! `lroot` as assembled: 107 instructions. Written from the lifter's rows. -/

set_option maxRecDepth 100000
namespace Code_lroot

def table : List (Nat × Instr × Nat) := [
  (0xC0000, .push .rbx, 0xC0001),
  (0xC0001, .push .rbp, 0xC0002),
  (0xC0002, .push .r12, 0xC0004),
  (0xC0004, .push .r13, 0xC0006),
  (0xC0006, .push .r14, 0xC0008),
  (0xC0008, .push .r15, 0xC000A),
  (0xC000A, .sub 64 (.reg .rsp) (.imm 0x78), 0xC000E),
  (0xC000E, .mov 64 (.mem .rsp 0x60) (.reg .rdi), 0xC0013),
  (0xC0013, .mov 64 (.reg .r13) (.reg .rsi), 0xC0016),
  (0xC0016, .mov 64 (.reg .r14) (.reg .rdx), 0xC0019),
  (0xC0019, .mov 64 (.mem .rsp 0x68) (.reg .rcx), 0xC001E),
  (0xC001E, .mov 64 (.reg .r15) (.reg .r8), 0xC0021),
  (0xC0021, .mov 64 (.reg .rax) (.mem .rsp 0x68), 0xC0026),
  (0xC0026, .or 64 (.reg .rax) (.imm 0x4), 0xC002A),
  (0xC002A, .mov 64 (.mem .rsp 0x70) (.reg .rax), 0xC002F),
  (0xC002F, .mov 64 (.reg .rax) (.reg .r13), 0xC0032),
  (0xC0032, .mov 64 (.reg .rax) (.mem .rax 0x0), 0xC0035),
  (0xC0035, .sub 64 (.reg .rax) (.imm 0x1), 0xC0039),
  (0xC0039, .mov 64 (.reg .rbx) (.reg .rax), 0xC003C),
  (0xC003C, .mov 64 (.reg .rax) (.reg .r13), 0xC003F),
  (0xC003F, .add 64 (.reg .rax) (.imm 0x40), 0xC0043),
  (0xC0043, .mov 64 (.reg .rbp) (.reg .rax), 0xC0046),
  (0xC0046, .mov 64 (.reg .rax) (.reg .rbp), 0xC0049),
  (0xC0049, .mov 64 (.reg .rcx) (.reg .rbx), 0xC004C),
  (0xC004C, .and 64 (.reg .rcx) (.imm 0x1), 0xC0050),
  (0xC0050, .shl64 .rcx 5, 0xC0054),
  (0xC0054, .add 64 (.reg .rax) (.reg .rcx), 0xC0057),
  (0xC0057, .lea .rcx .rsp 0x40, 0xC005C),
  (0xC005C, .movv false 0 (.m .rax 0x0), 0xC005F),
  (0xC005F, .storev false .rcx 0x0 0, 0xC0062),
  (0xC0062, .movv false 0 (.m .rax 0x10), 0xC0066),
  (0xC0066, .storev false .rcx 0x10 0, 0xC006A),
  (0xC006A, .mov 64 (.reg .rax) (.imm 0x0), 0xC0071),
  (0xC0071, .mov 64 (.reg .rcx) (.reg .rbx), 0xC0074),
  (0xC0074, .cmp 64 (.reg .rax) (.reg .rcx), 0xC0077),
  (0xC0077, .jae 0xC0164, 0xC007D),
  (0xC007D, .mov 64 (.reg .rax) (.reg .rbx), 0xC0080),
  (0xC0080, .and 64 (.reg .rax) (.imm 0x1), 0xC0084),
  (0xC0084, .mov 64 (.reg .rcx) (.imm 0x1), 0xC008B),
  (0xC008B, .cmp 64 (.reg .rax) (.reg .rcx), 0xC008E),
  (0xC008E, .jne 0xC014C, 0xC0094),
  (0xC0094, .mov 64 (.reg .rax) (.mem .rsp 0x70), 0xC0099),
  (0xC0099, .mov 64 (.reg .r12) (.reg .rax), 0xC009C),
  (0xC009C, .mov 64 (.reg .rax) (.reg .rbx), 0xC009F),
  (0xC009F, .mov 64 (.reg .rcx) (.imm 0x1), 0xC00A6),
  (0xC00A6, .cmp 64 (.reg .rax) (.reg .rcx), 0xC00A9),
  (0xC00A9, .jne 0xC00B7, 0xC00AB),
  (0xC00AB, .mov 64 (.reg .rax) (.mem .rsp 0x70), 0xC00B0),
  (0xC00B0, .or 64 (.reg .rax) (.imm 0x8), 0xC00B4),
  (0xC00B4, .mov 64 (.reg .r12) (.reg .rax), 0xC00B7),
  (0xC00B7, .mov 64 (.reg .rax) (.reg .rbp), 0xC00BA),
  (0xC00BA, .lea .rcx .rsp 0x0, 0xC00BE),
  (0xC00BE, .movv false 0 (.m .rax 0x0), 0xC00C1),
  (0xC00C1, .storev false .rcx 0x0 0, 0xC00C4),
  (0xC00C4, .movv false 0 (.m .rax 0x10), 0xC00C8),
  (0xC00C8, .storev false .rcx 0x10 0, 0xC00CC),
  (0xC00CC, .lea .rax .rsp 0x40, 0xC00D1),
  (0xC00D1, .lea .rcx .rsp 0x0, 0xC00D5),
  (0xC00D5, .add 64 (.reg .rcx) (.imm 0x20), 0xC00D9),
  (0xC00D9, .movv false 0 (.m .rax 0x0), 0xC00DC),
  (0xC00DC, .storev false .rcx 0x0 0, 0xC00DF),
  (0xC00DF, .movv false 0 (.m .rax 0x10), 0xC00E3),
  (0xC00E3, .storev false .rcx 0x10 0, 0xC00E7),
  (0xC00E7, .mov 64 (.reg .rax) (.reg .r14), 0xC00EA),
  (0xC00EA, .lea .rcx .rsp 0x40, 0xC00EF),
  (0xC00EF, .movv false 0 (.m .rax 0x0), 0xC00F2),
  (0xC00F2, .storev false .rcx 0x0 0, 0xC00F5),
  (0xC00F5, .movv false 0 (.m .rax 0x10), 0xC00F9),
  (0xC00F9, .storev false .rcx 0x10 0, 0xC00FD),
  (0xC00FD, .mov 64 (.reg .rax) (.reg .r15), 0xC0100),
  (0xC0100, .mov 64 (.reg .rcx) (.imm 0x5), 0xC0107),
  (0xC0107, .cmp 64 (.reg .rax) (.reg .rcx), 0xC010A),
  (0xC010A, .jne 0xC012D, 0xC010C),
  (0xC010C, .lea .rdi .rsp 0x40, 0xC0111),
  (0xC0111, .lea .rsi .rsp 0x0, 0xC0115),
  (0xC0115, .mov 64 (.reg .rdx) (.imm 0x40), 0xC011C),
  (0xC011C, .mov 64 (.reg .rcx) (.imm 0x0), 0xC0123),
  (0xC0123, .mov 64 (.reg .r8) (.reg .r12), 0xC0126),
  (0xC0126, .call 0x30000, 0xC012B),
  (0xC012B, .jmp 0xC014C, 0xC012D),
  (0xC012D, .lea .rdi .rsp 0x40, 0xC0132),
  (0xC0132, .lea .rsi .rsp 0x0, 0xC0136),
  (0xC0136, .mov 64 (.reg .rdx) (.imm 0x40), 0xC013D),
  (0xC013D, .mov 64 (.reg .rcx) (.imm 0x0), 0xC0144),
  (0xC0144, .mov 64 (.reg .r8) (.reg .r12), 0xC0147),
  (0xC0147, .call 0x20000, 0xC014C),
  (0xC014C, .mov 64 (.reg .rax) (.reg .rbx), 0xC014F),
  (0xC014F, .shr64 .rax 1, 0xC0152),
  (0xC0152, .mov 64 (.reg .rbx) (.reg .rax), 0xC0155),
  (0xC0155, .mov 64 (.reg .rax) (.reg .rbp), 0xC0158),
  (0xC0158, .add 64 (.reg .rax) (.imm 0x40), 0xC015C),
  (0xC015C, .mov 64 (.reg .rbp) (.reg .rax), 0xC015F),
  (0xC015F, .jmp 0xC006A, 0xC0164),
  (0xC0164, .lea .rax .rsp 0x40, 0xC0169),
  (0xC0169, .mov 64 (.reg .rcx) (.mem .rsp 0x60), 0xC016E),
  (0xC016E, .movv false 0 (.m .rax 0x0), 0xC0171),
  (0xC0171, .storev false .rcx 0x0 0, 0xC0174),
  (0xC0174, .movv false 0 (.m .rax 0x10), 0xC0178),
  (0xC0178, .storev false .rcx 0x10 0, 0xC017C),
  (0xC017C, .add 64 (.reg .rsp) (.imm 0x78), 0xC0180),
  (0xC0180, .pop .r15, 0xC0182),
  (0xC0182, .pop .r14, 0xC0184),
  (0xC0184, .pop .r13, 0xC0186),
  (0xC0186, .pop .r12, 0xC0188),
  (0xC0188, .pop .rbp, 0xC0189),
  (0xC0189, .pop .rbx, 0xC018A),
  (0xC018A, .ret, 0xC018B)
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

@[ode_at] theorem at_C0000 : prog 0xC0000 = some (.push .rbx, 0xC0001) := rfl
@[ode_at] theorem at_C0001 : prog 0xC0001 = some (.push .rbp, 0xC0002) := rfl
@[ode_at] theorem at_C0002 : prog 0xC0002 = some (.push .r12, 0xC0004) := rfl
@[ode_at] theorem at_C0004 : prog 0xC0004 = some (.push .r13, 0xC0006) := rfl
@[ode_at] theorem at_C0006 : prog 0xC0006 = some (.push .r14, 0xC0008) := rfl
@[ode_at] theorem at_C0008 : prog 0xC0008 = some (.push .r15, 0xC000A) := rfl
@[ode_at] theorem at_C000A : prog 0xC000A = some (.sub 64 (.reg .rsp) (.imm 0x78), 0xC000E) := rfl
@[ode_at] theorem at_C000E : prog 0xC000E = some (.mov 64 (.mem .rsp 0x60) (.reg .rdi), 0xC0013) := rfl
@[ode_at] theorem at_C0013 : prog 0xC0013 = some (.mov 64 (.reg .r13) (.reg .rsi), 0xC0016) := rfl
@[ode_at] theorem at_C0016 : prog 0xC0016 = some (.mov 64 (.reg .r14) (.reg .rdx), 0xC0019) := rfl
@[ode_at] theorem at_C0019 : prog 0xC0019 = some (.mov 64 (.mem .rsp 0x68) (.reg .rcx), 0xC001E) := rfl
@[ode_at] theorem at_C001E : prog 0xC001E = some (.mov 64 (.reg .r15) (.reg .r8), 0xC0021) := rfl
@[ode_at] theorem at_C0021 : prog 0xC0021 = some (.mov 64 (.reg .rax) (.mem .rsp 0x68), 0xC0026) := rfl
@[ode_at] theorem at_C0026 : prog 0xC0026 = some (.or 64 (.reg .rax) (.imm 0x4), 0xC002A) := rfl
@[ode_at] theorem at_C002A : prog 0xC002A = some (.mov 64 (.mem .rsp 0x70) (.reg .rax), 0xC002F) := rfl
@[ode_at] theorem at_C002F : prog 0xC002F = some (.mov 64 (.reg .rax) (.reg .r13), 0xC0032) := rfl
@[ode_at] theorem at_C0032 : prog 0xC0032 = some (.mov 64 (.reg .rax) (.mem .rax 0x0), 0xC0035) := rfl
@[ode_at] theorem at_C0035 : prog 0xC0035 = some (.sub 64 (.reg .rax) (.imm 0x1), 0xC0039) := rfl
@[ode_at] theorem at_C0039 : prog 0xC0039 = some (.mov 64 (.reg .rbx) (.reg .rax), 0xC003C) := rfl
@[ode_at] theorem at_C003C : prog 0xC003C = some (.mov 64 (.reg .rax) (.reg .r13), 0xC003F) := rfl
@[ode_at] theorem at_C003F : prog 0xC003F = some (.add 64 (.reg .rax) (.imm 0x40), 0xC0043) := rfl
@[ode_at] theorem at_C0043 : prog 0xC0043 = some (.mov 64 (.reg .rbp) (.reg .rax), 0xC0046) := rfl
@[ode_at] theorem at_C0046 : prog 0xC0046 = some (.mov 64 (.reg .rax) (.reg .rbp), 0xC0049) := rfl
@[ode_at] theorem at_C0049 : prog 0xC0049 = some (.mov 64 (.reg .rcx) (.reg .rbx), 0xC004C) := rfl
@[ode_at] theorem at_C004C : prog 0xC004C = some (.and 64 (.reg .rcx) (.imm 0x1), 0xC0050) := rfl
@[ode_at] theorem at_C0050 : prog 0xC0050 = some (.shl64 .rcx 5, 0xC0054) := rfl
@[ode_at] theorem at_C0054 : prog 0xC0054 = some (.add 64 (.reg .rax) (.reg .rcx), 0xC0057) := rfl
@[ode_at] theorem at_C0057 : prog 0xC0057 = some (.lea .rcx .rsp 0x40, 0xC005C) := rfl
@[ode_at] theorem at_C005C : prog 0xC005C = some (.movv false 0 (.m .rax 0x0), 0xC005F) := rfl
@[ode_at] theorem at_C005F : prog 0xC005F = some (.storev false .rcx 0x0 0, 0xC0062) := rfl
@[ode_at] theorem at_C0062 : prog 0xC0062 = some (.movv false 0 (.m .rax 0x10), 0xC0066) := rfl
@[ode_at] theorem at_C0066 : prog 0xC0066 = some (.storev false .rcx 0x10 0, 0xC006A) := rfl
@[ode_at] theorem at_C006A : prog 0xC006A = some (.mov 64 (.reg .rax) (.imm 0x0), 0xC0071) := rfl
@[ode_at] theorem at_C0071 : prog 0xC0071 = some (.mov 64 (.reg .rcx) (.reg .rbx), 0xC0074) := rfl
@[ode_at] theorem at_C0074 : prog 0xC0074 = some (.cmp 64 (.reg .rax) (.reg .rcx), 0xC0077) := rfl
@[ode_at] theorem at_C0077 : prog 0xC0077 = some (.jae 0xC0164, 0xC007D) := rfl
@[ode_at] theorem at_C007D : prog 0xC007D = some (.mov 64 (.reg .rax) (.reg .rbx), 0xC0080) := rfl
@[ode_at] theorem at_C0080 : prog 0xC0080 = some (.and 64 (.reg .rax) (.imm 0x1), 0xC0084) := rfl
@[ode_at] theorem at_C0084 : prog 0xC0084 = some (.mov 64 (.reg .rcx) (.imm 0x1), 0xC008B) := rfl
@[ode_at] theorem at_C008B : prog 0xC008B = some (.cmp 64 (.reg .rax) (.reg .rcx), 0xC008E) := rfl
@[ode_at] theorem at_C008E : prog 0xC008E = some (.jne 0xC014C, 0xC0094) := rfl
@[ode_at] theorem at_C0094 : prog 0xC0094 = some (.mov 64 (.reg .rax) (.mem .rsp 0x70), 0xC0099) := rfl
@[ode_at] theorem at_C0099 : prog 0xC0099 = some (.mov 64 (.reg .r12) (.reg .rax), 0xC009C) := rfl
@[ode_at] theorem at_C009C : prog 0xC009C = some (.mov 64 (.reg .rax) (.reg .rbx), 0xC009F) := rfl
@[ode_at] theorem at_C009F : prog 0xC009F = some (.mov 64 (.reg .rcx) (.imm 0x1), 0xC00A6) := rfl
@[ode_at] theorem at_C00A6 : prog 0xC00A6 = some (.cmp 64 (.reg .rax) (.reg .rcx), 0xC00A9) := rfl
@[ode_at] theorem at_C00A9 : prog 0xC00A9 = some (.jne 0xC00B7, 0xC00AB) := rfl
@[ode_at] theorem at_C00AB : prog 0xC00AB = some (.mov 64 (.reg .rax) (.mem .rsp 0x70), 0xC00B0) := rfl
@[ode_at] theorem at_C00B0 : prog 0xC00B0 = some (.or 64 (.reg .rax) (.imm 0x8), 0xC00B4) := rfl
@[ode_at] theorem at_C00B4 : prog 0xC00B4 = some (.mov 64 (.reg .r12) (.reg .rax), 0xC00B7) := rfl
@[ode_at] theorem at_C00B7 : prog 0xC00B7 = some (.mov 64 (.reg .rax) (.reg .rbp), 0xC00BA) := rfl
@[ode_at] theorem at_C00BA : prog 0xC00BA = some (.lea .rcx .rsp 0x0, 0xC00BE) := rfl
@[ode_at] theorem at_C00BE : prog 0xC00BE = some (.movv false 0 (.m .rax 0x0), 0xC00C1) := rfl
@[ode_at] theorem at_C00C1 : prog 0xC00C1 = some (.storev false .rcx 0x0 0, 0xC00C4) := rfl
@[ode_at] theorem at_C00C4 : prog 0xC00C4 = some (.movv false 0 (.m .rax 0x10), 0xC00C8) := rfl
@[ode_at] theorem at_C00C8 : prog 0xC00C8 = some (.storev false .rcx 0x10 0, 0xC00CC) := rfl
@[ode_at] theorem at_C00CC : prog 0xC00CC = some (.lea .rax .rsp 0x40, 0xC00D1) := rfl
@[ode_at] theorem at_C00D1 : prog 0xC00D1 = some (.lea .rcx .rsp 0x0, 0xC00D5) := rfl
@[ode_at] theorem at_C00D5 : prog 0xC00D5 = some (.add 64 (.reg .rcx) (.imm 0x20), 0xC00D9) := rfl
@[ode_at] theorem at_C00D9 : prog 0xC00D9 = some (.movv false 0 (.m .rax 0x0), 0xC00DC) := rfl
@[ode_at] theorem at_C00DC : prog 0xC00DC = some (.storev false .rcx 0x0 0, 0xC00DF) := rfl
@[ode_at] theorem at_C00DF : prog 0xC00DF = some (.movv false 0 (.m .rax 0x10), 0xC00E3) := rfl
@[ode_at] theorem at_C00E3 : prog 0xC00E3 = some (.storev false .rcx 0x10 0, 0xC00E7) := rfl
@[ode_at] theorem at_C00E7 : prog 0xC00E7 = some (.mov 64 (.reg .rax) (.reg .r14), 0xC00EA) := rfl
@[ode_at] theorem at_C00EA : prog 0xC00EA = some (.lea .rcx .rsp 0x40, 0xC00EF) := rfl
@[ode_at] theorem at_C00EF : prog 0xC00EF = some (.movv false 0 (.m .rax 0x0), 0xC00F2) := rfl
@[ode_at] theorem at_C00F2 : prog 0xC00F2 = some (.storev false .rcx 0x0 0, 0xC00F5) := rfl
@[ode_at] theorem at_C00F5 : prog 0xC00F5 = some (.movv false 0 (.m .rax 0x10), 0xC00F9) := rfl
@[ode_at] theorem at_C00F9 : prog 0xC00F9 = some (.storev false .rcx 0x10 0, 0xC00FD) := rfl
@[ode_at] theorem at_C00FD : prog 0xC00FD = some (.mov 64 (.reg .rax) (.reg .r15), 0xC0100) := rfl
@[ode_at] theorem at_C0100 : prog 0xC0100 = some (.mov 64 (.reg .rcx) (.imm 0x5), 0xC0107) := rfl
@[ode_at] theorem at_C0107 : prog 0xC0107 = some (.cmp 64 (.reg .rax) (.reg .rcx), 0xC010A) := rfl
@[ode_at] theorem at_C010A : prog 0xC010A = some (.jne 0xC012D, 0xC010C) := rfl
@[ode_at] theorem at_C010C : prog 0xC010C = some (.lea .rdi .rsp 0x40, 0xC0111) := rfl
@[ode_at] theorem at_C0111 : prog 0xC0111 = some (.lea .rsi .rsp 0x0, 0xC0115) := rfl
@[ode_at] theorem at_C0115 : prog 0xC0115 = some (.mov 64 (.reg .rdx) (.imm 0x40), 0xC011C) := rfl
@[ode_at] theorem at_C011C : prog 0xC011C = some (.mov 64 (.reg .rcx) (.imm 0x0), 0xC0123) := rfl
@[ode_at] theorem at_C0123 : prog 0xC0123 = some (.mov 64 (.reg .r8) (.reg .r12), 0xC0126) := rfl
@[ode_at] theorem at_C0126 : prog 0xC0126 = some (.call 0x30000, 0xC012B) := rfl
@[ode_at] theorem at_C012B : prog 0xC012B = some (.jmp 0xC014C, 0xC012D) := rfl
@[ode_at] theorem at_C012D : prog 0xC012D = some (.lea .rdi .rsp 0x40, 0xC0132) := rfl
@[ode_at] theorem at_C0132 : prog 0xC0132 = some (.lea .rsi .rsp 0x0, 0xC0136) := rfl
@[ode_at] theorem at_C0136 : prog 0xC0136 = some (.mov 64 (.reg .rdx) (.imm 0x40), 0xC013D) := rfl
@[ode_at] theorem at_C013D : prog 0xC013D = some (.mov 64 (.reg .rcx) (.imm 0x0), 0xC0144) := rfl
@[ode_at] theorem at_C0144 : prog 0xC0144 = some (.mov 64 (.reg .r8) (.reg .r12), 0xC0147) := rfl
@[ode_at] theorem at_C0147 : prog 0xC0147 = some (.call 0x20000, 0xC014C) := rfl
@[ode_at] theorem at_C014C : prog 0xC014C = some (.mov 64 (.reg .rax) (.reg .rbx), 0xC014F) := rfl
@[ode_at] theorem at_C014F : prog 0xC014F = some (.shr64 .rax 1, 0xC0152) := rfl
@[ode_at] theorem at_C0152 : prog 0xC0152 = some (.mov 64 (.reg .rbx) (.reg .rax), 0xC0155) := rfl
@[ode_at] theorem at_C0155 : prog 0xC0155 = some (.mov 64 (.reg .rax) (.reg .rbp), 0xC0158) := rfl
@[ode_at] theorem at_C0158 : prog 0xC0158 = some (.add 64 (.reg .rax) (.imm 0x40), 0xC015C) := rfl
@[ode_at] theorem at_C015C : prog 0xC015C = some (.mov 64 (.reg .rbp) (.reg .rax), 0xC015F) := rfl
@[ode_at] theorem at_C015F : prog 0xC015F = some (.jmp 0xC006A, 0xC0164) := rfl
@[ode_at] theorem at_C0164 : prog 0xC0164 = some (.lea .rax .rsp 0x40, 0xC0169) := rfl
@[ode_at] theorem at_C0169 : prog 0xC0169 = some (.mov 64 (.reg .rcx) (.mem .rsp 0x60), 0xC016E) := rfl
@[ode_at] theorem at_C016E : prog 0xC016E = some (.movv false 0 (.m .rax 0x0), 0xC0171) := rfl
@[ode_at] theorem at_C0171 : prog 0xC0171 = some (.storev false .rcx 0x0 0, 0xC0174) := rfl
@[ode_at] theorem at_C0174 : prog 0xC0174 = some (.movv false 0 (.m .rax 0x10), 0xC0178) := rfl
@[ode_at] theorem at_C0178 : prog 0xC0178 = some (.storev false .rcx 0x10 0, 0xC017C) := rfl
@[ode_at] theorem at_C017C : prog 0xC017C = some (.add 64 (.reg .rsp) (.imm 0x78), 0xC0180) := rfl
@[ode_at] theorem at_C0180 : prog 0xC0180 = some (.pop .r15, 0xC0182) := rfl
@[ode_at] theorem at_C0182 : prog 0xC0182 = some (.pop .r14, 0xC0184) := rfl
@[ode_at] theorem at_C0184 : prog 0xC0184 = some (.pop .r13, 0xC0186) := rfl
@[ode_at] theorem at_C0186 : prog 0xC0186 = some (.pop .r12, 0xC0188) := rfl
@[ode_at] theorem at_C0188 : prog 0xC0188 = some (.pop .rbp, 0xC0189) := rfl
@[ode_at] theorem at_C0189 : prog 0xC0189 = some (.pop .rbx, 0xC018A) := rfl
@[ode_at] theorem at_C018A : prog 0xC018A = some (.ret, 0xC018B) := rfl

end Code_lroot
