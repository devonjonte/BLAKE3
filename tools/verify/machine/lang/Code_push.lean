import Machine
import Cells
open X86

/-! `push` as assembled: 27 instructions. Written from the lifter's rows. -/

set_option maxRecDepth 100000
namespace Code_push

def table : List (Nat × Instr × Nat) := [
  (0x70000, .push .rbx, 0x70001),
  (0x70001, .push .rbp, 0x70002),
  (0x70002, .push .r12, 0x70004),
  (0x70004, .mov 64 (.reg .rbx) (.reg .rdi), 0x70007),
  (0x70007, .mov 64 (.reg .rbp) (.reg .rsi), 0x7000A),
  (0x7000A, .mov 64 (.reg .rax) (.reg .rbx), 0x7000D),
  (0x7000D, .mov 64 (.reg .rax) (.mem .rax 0x0), 0x70010),
  (0x70010, .mov 64 (.reg .r12) (.reg .rax), 0x70013),
  (0x70013, .mov 64 (.reg .rax) (.reg .rbp), 0x70016),
  (0x70016, .mov 64 (.reg .rcx) (.reg .rbx), 0x70019),
  (0x70019, .add 64 (.reg .rcx) (.imm 0x20), 0x7001D),
  (0x7001D, .mov 64 (.reg .rdx) (.reg .r12), 0x70020),
  (0x70020, .shl64 .rdx 5, 0x70024),
  (0x70024, .add 64 (.reg .rcx) (.reg .rdx), 0x70027),
  (0x70027, .movv false 0 (.m .rax 0x0), 0x7002A),
  (0x7002A, .storev false .rcx 0x0 0, 0x7002D),
  (0x7002D, .movv false 0 (.m .rax 0x10), 0x70031),
  (0x70031, .storev false .rcx 0x10 0, 0x70035),
  (0x70035, .mov 64 (.reg .rax) (.reg .r12), 0x70038),
  (0x70038, .add 64 (.reg .rax) (.imm 0x1), 0x7003C),
  (0x7003C, .mov 64 (.reg .rcx) (.reg .rbx), 0x7003F),
  (0x7003F, .mov 64 (.mem .rcx 0x0) (.reg .rax), 0x70042),
  (0x70042, .mov 64 (.reg .rax) (.imm 0x0), 0x70049),
  (0x70049, .pop .r12, 0x7004B),
  (0x7004B, .pop .rbp, 0x7004C),
  (0x7004C, .pop .rbx, 0x7004D),
  (0x7004D, .ret, 0x7004E)
]

/-- This function's instructions: the whole program (it calls nothing). -/
def prog (pc : Nat) : Option (Instr × Nat) := table.lookup pc

@[ode_at] theorem at_70000 : prog 0x70000 = some (.push .rbx, 0x70001) := rfl
@[ode_at] theorem at_70001 : prog 0x70001 = some (.push .rbp, 0x70002) := rfl
@[ode_at] theorem at_70002 : prog 0x70002 = some (.push .r12, 0x70004) := rfl
@[ode_at] theorem at_70004 : prog 0x70004 = some (.mov 64 (.reg .rbx) (.reg .rdi), 0x70007) := rfl
@[ode_at] theorem at_70007 : prog 0x70007 = some (.mov 64 (.reg .rbp) (.reg .rsi), 0x7000A) := rfl
@[ode_at] theorem at_7000A : prog 0x7000A = some (.mov 64 (.reg .rax) (.reg .rbx), 0x7000D) := rfl
@[ode_at] theorem at_7000D : prog 0x7000D = some (.mov 64 (.reg .rax) (.mem .rax 0x0), 0x70010) := rfl
@[ode_at] theorem at_70010 : prog 0x70010 = some (.mov 64 (.reg .r12) (.reg .rax), 0x70013) := rfl
@[ode_at] theorem at_70013 : prog 0x70013 = some (.mov 64 (.reg .rax) (.reg .rbp), 0x70016) := rfl
@[ode_at] theorem at_70016 : prog 0x70016 = some (.mov 64 (.reg .rcx) (.reg .rbx), 0x70019) := rfl
@[ode_at] theorem at_70019 : prog 0x70019 = some (.add 64 (.reg .rcx) (.imm 0x20), 0x7001D) := rfl
@[ode_at] theorem at_7001D : prog 0x7001D = some (.mov 64 (.reg .rdx) (.reg .r12), 0x70020) := rfl
@[ode_at] theorem at_70020 : prog 0x70020 = some (.shl64 .rdx 5, 0x70024) := rfl
@[ode_at] theorem at_70024 : prog 0x70024 = some (.add 64 (.reg .rcx) (.reg .rdx), 0x70027) := rfl
@[ode_at] theorem at_70027 : prog 0x70027 = some (.movv false 0 (.m .rax 0x0), 0x7002A) := rfl
@[ode_at] theorem at_7002A : prog 0x7002A = some (.storev false .rcx 0x0 0, 0x7002D) := rfl
@[ode_at] theorem at_7002D : prog 0x7002D = some (.movv false 0 (.m .rax 0x10), 0x70031) := rfl
@[ode_at] theorem at_70031 : prog 0x70031 = some (.storev false .rcx 0x10 0, 0x70035) := rfl
@[ode_at] theorem at_70035 : prog 0x70035 = some (.mov 64 (.reg .rax) (.reg .r12), 0x70038) := rfl
@[ode_at] theorem at_70038 : prog 0x70038 = some (.add 64 (.reg .rax) (.imm 0x1), 0x7003C) := rfl
@[ode_at] theorem at_7003C : prog 0x7003C = some (.mov 64 (.reg .rcx) (.reg .rbx), 0x7003F) := rfl
@[ode_at] theorem at_7003F : prog 0x7003F = some (.mov 64 (.mem .rcx 0x0) (.reg .rax), 0x70042) := rfl
@[ode_at] theorem at_70042 : prog 0x70042 = some (.mov 64 (.reg .rax) (.imm 0x0), 0x70049) := rfl
@[ode_at] theorem at_70049 : prog 0x70049 = some (.pop .r12, 0x7004B) := rfl
@[ode_at] theorem at_7004B : prog 0x7004B = some (.pop .rbp, 0x7004C) := rfl
@[ode_at] theorem at_7004C : prog 0x7004C = some (.pop .rbx, 0x7004D) := rfl
@[ode_at] theorem at_7004D : prog 0x7004D = some (.ret, 0x7004E) := rfl

end Code_push
