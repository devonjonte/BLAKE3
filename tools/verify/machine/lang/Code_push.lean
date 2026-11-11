import Machine
import Code
import Cells
open X86

/-! `push` as assembled: 32 instructions. Written from the lifter's rows. -/

set_option maxRecDepth 100000
namespace Code_push

def table : List (Nat × Instr × Nat) := [
  (0x61000, .push .rbx, 0x61001),
  (0x61001, .push .rbp, 0x61002),
  (0x61002, .push .r12, 0x61004),
  (0x61004, .mov 64 (.reg .rbx) (.reg .rdi), 0x61007),
  (0x61007, .mov 64 (.reg .rbp) (.reg .rsi), 0x6100A),
  (0x6100A, .mov 64 (.reg .rax) (.reg .rbx), 0x6100D),
  (0x6100D, .mov 64 (.reg .rax) (.mem .rax 0x0), 0x61010),
  (0x61010, .mov 64 (.reg .r12) (.reg .rax), 0x61013),
  (0x61013, .mov 64 (.reg .rax) (.reg .r12), 0x61016),
  (0x61016, .mov 64 (.reg .rcx) (.imm 0x37), 0x6101D),
  (0x6101D, .cmp 64 (.reg .rax) (.reg .rcx), 0x61020),
  (0x61020, .jae 0x61024, 0x61022),
  (0x61022, .jmp 0x61026, 0x61024),
  (0x61026, .mov 64 (.reg .rax) (.reg .rbp), 0x61029),
  (0x61029, .mov 64 (.reg .rcx) (.reg .rbx), 0x6102C),
  (0x6102C, .add 64 (.reg .rcx) (.imm 0x20), 0x61030),
  (0x61030, .mov 64 (.reg .rdx) (.reg .r12), 0x61033),
  (0x61033, .shl64 .rdx 5, 0x61037),
  (0x61037, .add 64 (.reg .rcx) (.reg .rdx), 0x6103A),
  (0x6103A, .movv false 0 (.m .rax 0x0), 0x6103D),
  (0x6103D, .storev false .rcx 0x0 0, 0x61040),
  (0x61040, .movv false 0 (.m .rax 0x10), 0x61044),
  (0x61044, .storev false .rcx 0x10 0, 0x61048),
  (0x61048, .mov 64 (.reg .rax) (.reg .r12), 0x6104B),
  (0x6104B, .add 64 (.reg .rax) (.imm 0x1), 0x6104F),
  (0x6104F, .mov 64 (.reg .rcx) (.reg .rbx), 0x61052),
  (0x61052, .mov 64 (.mem .rcx 0x0) (.reg .rax), 0x61055),
  (0x61055, .mov 64 (.reg .rax) (.imm 0x0), 0x6105C),
  (0x6105C, .pop .r12, 0x6105E),
  (0x6105E, .pop .rbp, 0x6105F),
  (0x6105F, .pop .rbx, 0x61060),
  (0x61060, .ret, 0x61061)
]

/-- This function's instructions and the kernels' (one/Code.lean) as one program. -/
def prog (pc : Nat) : Option (Instr × Nat) := (Code.prog pc).or (table.lookup pc)

theorem has_kernels : ∀ pc x, Code.prog pc = some x → prog pc = some x := by
  intro pc x h; simp only [prog, h, Option.some_or]

@[ode_at] theorem at_61000 : prog 0x61000 = some (.push .rbx, 0x61001) := rfl
@[ode_at] theorem at_61001 : prog 0x61001 = some (.push .rbp, 0x61002) := rfl
@[ode_at] theorem at_61002 : prog 0x61002 = some (.push .r12, 0x61004) := rfl
@[ode_at] theorem at_61004 : prog 0x61004 = some (.mov 64 (.reg .rbx) (.reg .rdi), 0x61007) := rfl
@[ode_at] theorem at_61007 : prog 0x61007 = some (.mov 64 (.reg .rbp) (.reg .rsi), 0x6100A) := rfl
@[ode_at] theorem at_6100A : prog 0x6100A = some (.mov 64 (.reg .rax) (.reg .rbx), 0x6100D) := rfl
@[ode_at] theorem at_6100D : prog 0x6100D = some (.mov 64 (.reg .rax) (.mem .rax 0x0), 0x61010) := rfl
@[ode_at] theorem at_61010 : prog 0x61010 = some (.mov 64 (.reg .r12) (.reg .rax), 0x61013) := rfl
@[ode_at] theorem at_61013 : prog 0x61013 = some (.mov 64 (.reg .rax) (.reg .r12), 0x61016) := rfl
@[ode_at] theorem at_61016 : prog 0x61016 = some (.mov 64 (.reg .rcx) (.imm 0x37), 0x6101D) := rfl
@[ode_at] theorem at_6101D : prog 0x6101D = some (.cmp 64 (.reg .rax) (.reg .rcx), 0x61020) := rfl
@[ode_at] theorem at_61020 : prog 0x61020 = some (.jae 0x61024, 0x61022) := rfl
@[ode_at] theorem at_61022 : prog 0x61022 = some (.jmp 0x61026, 0x61024) := rfl
@[ode_at] theorem at_61026 : prog 0x61026 = some (.mov 64 (.reg .rax) (.reg .rbp), 0x61029) := rfl
@[ode_at] theorem at_61029 : prog 0x61029 = some (.mov 64 (.reg .rcx) (.reg .rbx), 0x6102C) := rfl
@[ode_at] theorem at_6102C : prog 0x6102C = some (.add 64 (.reg .rcx) (.imm 0x20), 0x61030) := rfl
@[ode_at] theorem at_61030 : prog 0x61030 = some (.mov 64 (.reg .rdx) (.reg .r12), 0x61033) := rfl
@[ode_at] theorem at_61033 : prog 0x61033 = some (.shl64 .rdx 5, 0x61037) := rfl
@[ode_at] theorem at_61037 : prog 0x61037 = some (.add 64 (.reg .rcx) (.reg .rdx), 0x6103A) := rfl
@[ode_at] theorem at_6103A : prog 0x6103A = some (.movv false 0 (.m .rax 0x0), 0x6103D) := rfl
@[ode_at] theorem at_6103D : prog 0x6103D = some (.storev false .rcx 0x0 0, 0x61040) := rfl
@[ode_at] theorem at_61040 : prog 0x61040 = some (.movv false 0 (.m .rax 0x10), 0x61044) := rfl
@[ode_at] theorem at_61044 : prog 0x61044 = some (.storev false .rcx 0x10 0, 0x61048) := rfl
@[ode_at] theorem at_61048 : prog 0x61048 = some (.mov 64 (.reg .rax) (.reg .r12), 0x6104B) := rfl
@[ode_at] theorem at_6104B : prog 0x6104B = some (.add 64 (.reg .rax) (.imm 0x1), 0x6104F) := rfl
@[ode_at] theorem at_6104F : prog 0x6104F = some (.mov 64 (.reg .rcx) (.reg .rbx), 0x61052) := rfl
@[ode_at] theorem at_61052 : prog 0x61052 = some (.mov 64 (.mem .rcx 0x0) (.reg .rax), 0x61055) := rfl
@[ode_at] theorem at_61055 : prog 0x61055 = some (.mov 64 (.reg .rax) (.imm 0x0), 0x6105C) := rfl
@[ode_at] theorem at_6105C : prog 0x6105C = some (.pop .r12, 0x6105E) := rfl
@[ode_at] theorem at_6105E : prog 0x6105E = some (.pop .rbp, 0x6105F) := rfl
@[ode_at] theorem at_6105F : prog 0x6105F = some (.pop .rbx, 0x61060) := rfl
@[ode_at] theorem at_61060 : prog 0x61060 = some (.ret, 0x61061) := rfl

end Code_push
