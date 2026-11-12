import Machine
import Cells
open X86

/-! `pad` as assembled: 39 instructions. Written from the lifter's rows. -/

set_option maxRecDepth 100000
namespace Code_pad

def table : List (Nat × Instr × Nat) := [
  (0xE0000, .push .rbx, 0xE0001),
  (0xE0001, .push .rbp, 0xE0002),
  (0xE0002, .push .r12, 0xE0004),
  (0xE0004, .push .r13, 0xE0006),
  (0xE0006, .sub 64 (.reg .rsp) (.imm 0x8), 0xE000A),
  (0xE000A, .mov 64 (.reg .rbx) (.reg .rdi), 0xE000D),
  (0xE000D, .mov 64 (.reg .rbp) (.reg .rsi), 0xE0010),
  (0xE0010, .mov 64 (.reg .r12) (.reg .rdx), 0xE0013),
  (0xE0013, .mov 64 (.reg .rax) (.imm 0x40), 0xE001A),
  (0xE001A, .mov 64 (.reg .r13) (.reg .rax), 0xE001D),
  (0xE001D, .mov 64 (.reg .rax) (.imm 0x0), 0xE0024),
  (0xE0024, .mov 64 (.reg .rcx) (.reg .r13), 0xE0027),
  (0xE0027, .cmp 64 (.reg .rax) (.reg .rcx), 0xE002A),
  (0xE002A, .jae 0xE0065, 0xE002C),
  (0xE002C, .mov 64 (.reg .rax) (.reg .r13), 0xE002F),
  (0xE002F, .sub 64 (.reg .rax) (.imm 0x1), 0xE0033),
  (0xE0033, .mov 64 (.reg .r13) (.reg .rax), 0xE0036),
  (0xE0036, .mov 64 (.reg .rax) (.reg .r13), 0xE0039),
  (0xE0039, .mov 64 (.reg .rcx) (.reg .r12), 0xE003C),
  (0xE003C, .cmp 64 (.reg .rax) (.reg .rcx), 0xE003F),
  (0xE003F, .jae 0xE0054, 0xE0041),
  (0xE0041, .mov 64 (.reg .rax) (.reg .rbp), 0xE0044),
  (0xE0044, .add 64 (.reg .rax) (.reg .r13), 0xE0047),
  (0xE0047, .movzx8 .rax (.mem .rax 0x0), 0xE004A),
  (0xE004A, .mov 64 (.reg .rcx) (.reg .rbx), 0xE004D),
  (0xE004D, .add 64 (.reg .rcx) (.reg .r13), 0xE0050),
  (0xE0050, .mov 8 (.mem .rcx 0x0) (.reg .rax), 0xE0052),
  (0xE0052, .jmp 0xE0063, 0xE0054),
  (0xE0054, .mov 64 (.reg .rax) (.imm 0x0), 0xE005B),
  (0xE005B, .mov 64 (.reg .rcx) (.reg .rbx), 0xE005E),
  (0xE005E, .add 64 (.reg .rcx) (.reg .r13), 0xE0061),
  (0xE0061, .mov 8 (.mem .rcx 0x0) (.reg .rax), 0xE0063),
  (0xE0063, .jmp 0xE001D, 0xE0065),
  (0xE0065, .add 64 (.reg .rsp) (.imm 0x8), 0xE0069),
  (0xE0069, .pop .r13, 0xE006B),
  (0xE006B, .pop .r12, 0xE006D),
  (0xE006D, .pop .rbp, 0xE006E),
  (0xE006E, .pop .rbx, 0xE006F),
  (0xE006F, .ret, 0xE0070)
]

/-- Every instruction of the program: this function's (it calls nothing). -/
def whole : List (Nat × Instr × Nat) := table

def prog (pc : Nat) : Option (Instr × Nat) := whole.lookup pc

/-- The addresses the program has an instruction at. -/
def keys : List Nat := whole.map (·.1)

theorem keys_of : ∀ pc x, prog pc = some x → pc ∈ keys := fun pc x h => lookup_mem_keys whole pc x h

@[ode_at] theorem at_E0000 : prog 0xE0000 = some (.push .rbx, 0xE0001) := rfl
@[ode_at] theorem at_E0001 : prog 0xE0001 = some (.push .rbp, 0xE0002) := rfl
@[ode_at] theorem at_E0002 : prog 0xE0002 = some (.push .r12, 0xE0004) := rfl
@[ode_at] theorem at_E0004 : prog 0xE0004 = some (.push .r13, 0xE0006) := rfl
@[ode_at] theorem at_E0006 : prog 0xE0006 = some (.sub 64 (.reg .rsp) (.imm 0x8), 0xE000A) := rfl
@[ode_at] theorem at_E000A : prog 0xE000A = some (.mov 64 (.reg .rbx) (.reg .rdi), 0xE000D) := rfl
@[ode_at] theorem at_E000D : prog 0xE000D = some (.mov 64 (.reg .rbp) (.reg .rsi), 0xE0010) := rfl
@[ode_at] theorem at_E0010 : prog 0xE0010 = some (.mov 64 (.reg .r12) (.reg .rdx), 0xE0013) := rfl
@[ode_at] theorem at_E0013 : prog 0xE0013 = some (.mov 64 (.reg .rax) (.imm 0x40), 0xE001A) := rfl
@[ode_at] theorem at_E001A : prog 0xE001A = some (.mov 64 (.reg .r13) (.reg .rax), 0xE001D) := rfl
@[ode_at] theorem at_E001D : prog 0xE001D = some (.mov 64 (.reg .rax) (.imm 0x0), 0xE0024) := rfl
@[ode_at] theorem at_E0024 : prog 0xE0024 = some (.mov 64 (.reg .rcx) (.reg .r13), 0xE0027) := rfl
@[ode_at] theorem at_E0027 : prog 0xE0027 = some (.cmp 64 (.reg .rax) (.reg .rcx), 0xE002A) := rfl
@[ode_at] theorem at_E002A : prog 0xE002A = some (.jae 0xE0065, 0xE002C) := rfl
@[ode_at] theorem at_E002C : prog 0xE002C = some (.mov 64 (.reg .rax) (.reg .r13), 0xE002F) := rfl
@[ode_at] theorem at_E002F : prog 0xE002F = some (.sub 64 (.reg .rax) (.imm 0x1), 0xE0033) := rfl
@[ode_at] theorem at_E0033 : prog 0xE0033 = some (.mov 64 (.reg .r13) (.reg .rax), 0xE0036) := rfl
@[ode_at] theorem at_E0036 : prog 0xE0036 = some (.mov 64 (.reg .rax) (.reg .r13), 0xE0039) := rfl
@[ode_at] theorem at_E0039 : prog 0xE0039 = some (.mov 64 (.reg .rcx) (.reg .r12), 0xE003C) := rfl
@[ode_at] theorem at_E003C : prog 0xE003C = some (.cmp 64 (.reg .rax) (.reg .rcx), 0xE003F) := rfl
@[ode_at] theorem at_E003F : prog 0xE003F = some (.jae 0xE0054, 0xE0041) := rfl
@[ode_at] theorem at_E0041 : prog 0xE0041 = some (.mov 64 (.reg .rax) (.reg .rbp), 0xE0044) := rfl
@[ode_at] theorem at_E0044 : prog 0xE0044 = some (.add 64 (.reg .rax) (.reg .r13), 0xE0047) := rfl
@[ode_at] theorem at_E0047 : prog 0xE0047 = some (.movzx8 .rax (.mem .rax 0x0), 0xE004A) := rfl
@[ode_at] theorem at_E004A : prog 0xE004A = some (.mov 64 (.reg .rcx) (.reg .rbx), 0xE004D) := rfl
@[ode_at] theorem at_E004D : prog 0xE004D = some (.add 64 (.reg .rcx) (.reg .r13), 0xE0050) := rfl
@[ode_at] theorem at_E0050 : prog 0xE0050 = some (.mov 8 (.mem .rcx 0x0) (.reg .rax), 0xE0052) := rfl
@[ode_at] theorem at_E0052 : prog 0xE0052 = some (.jmp 0xE0063, 0xE0054) := rfl
@[ode_at] theorem at_E0054 : prog 0xE0054 = some (.mov 64 (.reg .rax) (.imm 0x0), 0xE005B) := rfl
@[ode_at] theorem at_E005B : prog 0xE005B = some (.mov 64 (.reg .rcx) (.reg .rbx), 0xE005E) := rfl
@[ode_at] theorem at_E005E : prog 0xE005E = some (.add 64 (.reg .rcx) (.reg .r13), 0xE0061) := rfl
@[ode_at] theorem at_E0061 : prog 0xE0061 = some (.mov 8 (.mem .rcx 0x0) (.reg .rax), 0xE0063) := rfl
@[ode_at] theorem at_E0063 : prog 0xE0063 = some (.jmp 0xE001D, 0xE0065) := rfl
@[ode_at] theorem at_E0065 : prog 0xE0065 = some (.add 64 (.reg .rsp) (.imm 0x8), 0xE0069) := rfl
@[ode_at] theorem at_E0069 : prog 0xE0069 = some (.pop .r13, 0xE006B) := rfl
@[ode_at] theorem at_E006B : prog 0xE006B = some (.pop .r12, 0xE006D) := rfl
@[ode_at] theorem at_E006D : prog 0xE006D = some (.pop .rbp, 0xE006E) := rfl
@[ode_at] theorem at_E006E : prog 0xE006E = some (.pop .rbx, 0xE006F) := rfl
@[ode_at] theorem at_E006F : prog 0xE006F = some (.ret, 0xE0070) := rfl

end Code_pad
