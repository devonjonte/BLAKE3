import Machine
import KCode
import Cells
open X86

/-! `node_out` as assembled: 58 instructions. Written from the lifter's rows. -/

set_option maxRecDepth 100000
namespace Code_node_out

def table : List (Nat × Instr × Nat) := [
  (0xD0000, .push .rbx, 0xD0001),
  (0xD0001, .push .rbp, 0xD0002),
  (0xD0002, .push .r12, 0xD0004),
  (0xD0004, .push .r13, 0xD0006),
  (0xD0006, .push .r14, 0xD0008),
  (0xD0008, .push .r15, 0xD000A),
  (0xD000A, .sub 64 (.reg .rsp) (.imm 0x18), 0xD000E),
  (0xD000E, .mov 64 (.reg .rbx) (.reg .rdi), 0xD0011),
  (0xD0011, .mov 64 (.reg .rbp) (.reg .rsi), 0xD0014),
  (0xD0014, .mov 64 (.reg .r12) (.reg .rdx), 0xD0017),
  (0xD0017, .mov 64 (.reg .r13) (.reg .rcx), 0xD001A),
  (0xD001A, .mov 64 (.reg .rax) (.reg .rbp), 0xD001D),
  (0xD001D, .add 64 (.reg .rax) (.imm 0x20), 0xD0021),
  (0xD0021, .mov 64 (.reg .r14) (.reg .rax), 0xD0024),
  (0xD0024, .mov 64 (.reg .rax) (.reg .rbp), 0xD0027),
  (0xD0027, .add 64 (.reg .rax) (.imm 0x68), 0xD002B),
  (0xD002B, .mov 64 (.reg .rax) (.mem .rax 0x0), 0xD002E),
  (0xD002E, .mov 64 (.reg .r15) (.reg .rax), 0xD0031),
  (0xD0031, .mov 64 (.reg .rax) (.reg .rbp), 0xD0034),
  (0xD0034, .add 64 (.reg .rax) (.imm 0x60), 0xD0038),
  (0xD0038, .mov 64 (.reg .rax) (.mem .rax 0x0), 0xD003B),
  (0xD003B, .mov 64 (.mem .rsp 0x0) (.reg .rax), 0xD003F),
  (0xD003F, .mov 64 (.reg .rax) (.reg .rbp), 0xD0042),
  (0xD0042, .add 64 (.reg .rax) (.imm 0x70), 0xD0046),
  (0xD0046, .mov 64 (.reg .rax) (.mem .rax 0x0), 0xD0049),
  (0xD0049, .or 64 (.reg .rax) (.reg .r12), 0xD004C),
  (0xD004C, .mov 64 (.mem .rsp 0x8) (.reg .rax), 0xD0051),
  (0xD0051, .mov 64 (.reg .rax) (.reg .rbp), 0xD0054),
  (0xD0054, .mov 64 (.reg .rcx) (.reg .rbx), 0xD0057),
  (0xD0057, .movv false 0 (.m .rax 0x0), 0xD005A),
  (0xD005A, .storev false .rcx 0x0 0, 0xD005D),
  (0xD005D, .movv false 0 (.m .rax 0x10), 0xD0061),
  (0xD0061, .storev false .rcx 0x10 0, 0xD0065),
  (0xD0065, .mov 64 (.reg .rax) (.reg .r13), 0xD0068),
  (0xD0068, .mov 64 (.reg .rcx) (.imm 0x5), 0xD006F),
  (0xD006F, .cmp 64 (.reg .rax) (.reg .rcx), 0xD0072),
  (0xD0072, .jne 0xD008D, 0xD0074),
  (0xD0074, .mov 64 (.reg .rdi) (.reg .rbx), 0xD0077),
  (0xD0077, .mov 64 (.reg .rsi) (.reg .r14), 0xD007A),
  (0xD007A, .mov 64 (.reg .rdx) (.reg .r15), 0xD007D),
  (0xD007D, .mov 64 (.reg .rcx) (.mem .rsp 0x0), 0xD0081),
  (0xD0081, .mov 64 (.reg .r8) (.mem .rsp 0x8), 0xD0086),
  (0xD0086, .call 0x30000, 0xD008B),
  (0xD008B, .jmp 0xD00A4, 0xD008D),
  (0xD008D, .mov 64 (.reg .rdi) (.reg .rbx), 0xD0090),
  (0xD0090, .mov 64 (.reg .rsi) (.reg .r14), 0xD0093),
  (0xD0093, .mov 64 (.reg .rdx) (.reg .r15), 0xD0096),
  (0xD0096, .mov 64 (.reg .rcx) (.mem .rsp 0x0), 0xD009A),
  (0xD009A, .mov 64 (.reg .r8) (.mem .rsp 0x8), 0xD009F),
  (0xD009F, .call 0x20000, 0xD00A4),
  (0xD00A4, .add 64 (.reg .rsp) (.imm 0x18), 0xD00A8),
  (0xD00A8, .pop .r15, 0xD00AA),
  (0xD00AA, .pop .r14, 0xD00AC),
  (0xD00AC, .pop .r13, 0xD00AE),
  (0xD00AE, .pop .r12, 0xD00B0),
  (0xD00B0, .pop .rbp, 0xD00B1),
  (0xD00B1, .pop .rbx, 0xD00B2),
  (0xD00B2, .ret, 0xD00B3)
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

@[ode_at] theorem at_D0000 : prog 0xD0000 = some (.push .rbx, 0xD0001) := rfl
@[ode_at] theorem at_D0001 : prog 0xD0001 = some (.push .rbp, 0xD0002) := rfl
@[ode_at] theorem at_D0002 : prog 0xD0002 = some (.push .r12, 0xD0004) := rfl
@[ode_at] theorem at_D0004 : prog 0xD0004 = some (.push .r13, 0xD0006) := rfl
@[ode_at] theorem at_D0006 : prog 0xD0006 = some (.push .r14, 0xD0008) := rfl
@[ode_at] theorem at_D0008 : prog 0xD0008 = some (.push .r15, 0xD000A) := rfl
@[ode_at] theorem at_D000A : prog 0xD000A = some (.sub 64 (.reg .rsp) (.imm 0x18), 0xD000E) := rfl
@[ode_at] theorem at_D000E : prog 0xD000E = some (.mov 64 (.reg .rbx) (.reg .rdi), 0xD0011) := rfl
@[ode_at] theorem at_D0011 : prog 0xD0011 = some (.mov 64 (.reg .rbp) (.reg .rsi), 0xD0014) := rfl
@[ode_at] theorem at_D0014 : prog 0xD0014 = some (.mov 64 (.reg .r12) (.reg .rdx), 0xD0017) := rfl
@[ode_at] theorem at_D0017 : prog 0xD0017 = some (.mov 64 (.reg .r13) (.reg .rcx), 0xD001A) := rfl
@[ode_at] theorem at_D001A : prog 0xD001A = some (.mov 64 (.reg .rax) (.reg .rbp), 0xD001D) := rfl
@[ode_at] theorem at_D001D : prog 0xD001D = some (.add 64 (.reg .rax) (.imm 0x20), 0xD0021) := rfl
@[ode_at] theorem at_D0021 : prog 0xD0021 = some (.mov 64 (.reg .r14) (.reg .rax), 0xD0024) := rfl
@[ode_at] theorem at_D0024 : prog 0xD0024 = some (.mov 64 (.reg .rax) (.reg .rbp), 0xD0027) := rfl
@[ode_at] theorem at_D0027 : prog 0xD0027 = some (.add 64 (.reg .rax) (.imm 0x68), 0xD002B) := rfl
@[ode_at] theorem at_D002B : prog 0xD002B = some (.mov 64 (.reg .rax) (.mem .rax 0x0), 0xD002E) := rfl
@[ode_at] theorem at_D002E : prog 0xD002E = some (.mov 64 (.reg .r15) (.reg .rax), 0xD0031) := rfl
@[ode_at] theorem at_D0031 : prog 0xD0031 = some (.mov 64 (.reg .rax) (.reg .rbp), 0xD0034) := rfl
@[ode_at] theorem at_D0034 : prog 0xD0034 = some (.add 64 (.reg .rax) (.imm 0x60), 0xD0038) := rfl
@[ode_at] theorem at_D0038 : prog 0xD0038 = some (.mov 64 (.reg .rax) (.mem .rax 0x0), 0xD003B) := rfl
@[ode_at] theorem at_D003B : prog 0xD003B = some (.mov 64 (.mem .rsp 0x0) (.reg .rax), 0xD003F) := rfl
@[ode_at] theorem at_D003F : prog 0xD003F = some (.mov 64 (.reg .rax) (.reg .rbp), 0xD0042) := rfl
@[ode_at] theorem at_D0042 : prog 0xD0042 = some (.add 64 (.reg .rax) (.imm 0x70), 0xD0046) := rfl
@[ode_at] theorem at_D0046 : prog 0xD0046 = some (.mov 64 (.reg .rax) (.mem .rax 0x0), 0xD0049) := rfl
@[ode_at] theorem at_D0049 : prog 0xD0049 = some (.or 64 (.reg .rax) (.reg .r12), 0xD004C) := rfl
@[ode_at] theorem at_D004C : prog 0xD004C = some (.mov 64 (.mem .rsp 0x8) (.reg .rax), 0xD0051) := rfl
@[ode_at] theorem at_D0051 : prog 0xD0051 = some (.mov 64 (.reg .rax) (.reg .rbp), 0xD0054) := rfl
@[ode_at] theorem at_D0054 : prog 0xD0054 = some (.mov 64 (.reg .rcx) (.reg .rbx), 0xD0057) := rfl
@[ode_at] theorem at_D0057 : prog 0xD0057 = some (.movv false 0 (.m .rax 0x0), 0xD005A) := rfl
@[ode_at] theorem at_D005A : prog 0xD005A = some (.storev false .rcx 0x0 0, 0xD005D) := rfl
@[ode_at] theorem at_D005D : prog 0xD005D = some (.movv false 0 (.m .rax 0x10), 0xD0061) := rfl
@[ode_at] theorem at_D0061 : prog 0xD0061 = some (.storev false .rcx 0x10 0, 0xD0065) := rfl
@[ode_at] theorem at_D0065 : prog 0xD0065 = some (.mov 64 (.reg .rax) (.reg .r13), 0xD0068) := rfl
@[ode_at] theorem at_D0068 : prog 0xD0068 = some (.mov 64 (.reg .rcx) (.imm 0x5), 0xD006F) := rfl
@[ode_at] theorem at_D006F : prog 0xD006F = some (.cmp 64 (.reg .rax) (.reg .rcx), 0xD0072) := rfl
@[ode_at] theorem at_D0072 : prog 0xD0072 = some (.jne 0xD008D, 0xD0074) := rfl
@[ode_at] theorem at_D0074 : prog 0xD0074 = some (.mov 64 (.reg .rdi) (.reg .rbx), 0xD0077) := rfl
@[ode_at] theorem at_D0077 : prog 0xD0077 = some (.mov 64 (.reg .rsi) (.reg .r14), 0xD007A) := rfl
@[ode_at] theorem at_D007A : prog 0xD007A = some (.mov 64 (.reg .rdx) (.reg .r15), 0xD007D) := rfl
@[ode_at] theorem at_D007D : prog 0xD007D = some (.mov 64 (.reg .rcx) (.mem .rsp 0x0), 0xD0081) := rfl
@[ode_at] theorem at_D0081 : prog 0xD0081 = some (.mov 64 (.reg .r8) (.mem .rsp 0x8), 0xD0086) := rfl
@[ode_at] theorem at_D0086 : prog 0xD0086 = some (.call 0x30000, 0xD008B) := rfl
@[ode_at] theorem at_D008B : prog 0xD008B = some (.jmp 0xD00A4, 0xD008D) := rfl
@[ode_at] theorem at_D008D : prog 0xD008D = some (.mov 64 (.reg .rdi) (.reg .rbx), 0xD0090) := rfl
@[ode_at] theorem at_D0090 : prog 0xD0090 = some (.mov 64 (.reg .rsi) (.reg .r14), 0xD0093) := rfl
@[ode_at] theorem at_D0093 : prog 0xD0093 = some (.mov 64 (.reg .rdx) (.reg .r15), 0xD0096) := rfl
@[ode_at] theorem at_D0096 : prog 0xD0096 = some (.mov 64 (.reg .rcx) (.mem .rsp 0x0), 0xD009A) := rfl
@[ode_at] theorem at_D009A : prog 0xD009A = some (.mov 64 (.reg .r8) (.mem .rsp 0x8), 0xD009F) := rfl
@[ode_at] theorem at_D009F : prog 0xD009F = some (.call 0x20000, 0xD00A4) := rfl
@[ode_at] theorem at_D00A4 : prog 0xD00A4 = some (.add 64 (.reg .rsp) (.imm 0x18), 0xD00A8) := rfl
@[ode_at] theorem at_D00A8 : prog 0xD00A8 = some (.pop .r15, 0xD00AA) := rfl
@[ode_at] theorem at_D00AA : prog 0xD00AA = some (.pop .r14, 0xD00AC) := rfl
@[ode_at] theorem at_D00AC : prog 0xD00AC = some (.pop .r13, 0xD00AE) := rfl
@[ode_at] theorem at_D00AE : prog 0xD00AE = some (.pop .r12, 0xD00B0) := rfl
@[ode_at] theorem at_D00B0 : prog 0xD00B0 = some (.pop .rbp, 0xD00B1) := rfl
@[ode_at] theorem at_D00B1 : prog 0xD00B1 = some (.pop .rbx, 0xD00B2) := rfl
@[ode_at] theorem at_D00B2 : prog 0xD00B2 = some (.ret, 0xD00B3) := rfl

end Code_node_out
