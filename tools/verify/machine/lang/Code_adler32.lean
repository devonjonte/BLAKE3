import Machine
import Cells
open X86

/-! `adler32` as assembled: 55 instructions. Written from the lifter's rows. -/

set_option maxRecDepth 100000
namespace Code_adler32

def table : List (Nat × Instr × Nat) := [
  (0x100000, .push .rbx, 0x100001),
  (0x100001, .push .rbp, 0x100002),
  (0x100002, .push .r12, 0x100004),
  (0x100004, .push .r13, 0x100006),
  (0x100006, .push .r14, 0x100008),
  (0x100008, .mov 64 (.reg .rbx) (.reg .rdi), 0x10000B),
  (0x10000B, .mov 64 (.reg .rbp) (.reg .rsi), 0x10000E),
  (0x10000E, .mov 64 (.reg .rax) (.imm 0x1), 0x100015),
  (0x100015, .mov 64 (.reg .r12) (.reg .rax), 0x100018),
  (0x100018, .mov 64 (.reg .rax) (.imm 0x0), 0x10001F),
  (0x10001F, .mov 64 (.reg .r13) (.reg .rax), 0x100022),
  (0x100022, .mov 64 (.reg .rax) (.imm 0x0), 0x100029),
  (0x100029, .mov 64 (.reg .r14) (.reg .rax), 0x10002C),
  (0x10002C, .mov 64 (.reg .rax) (.reg .r14), 0x10002F),
  (0x10002F, .mov 64 (.reg .rcx) (.reg .rbp), 0x100032),
  (0x100032, .cmp 64 (.reg .rax) (.reg .rcx), 0x100035),
  (0x100035, .jae 0x100098, 0x100037),
  (0x100037, .mov 64 (.reg .rax) (.reg .r12), 0x10003A),
  (0x10003A, .mov 64 (.reg .rcx) (.reg .rbx), 0x10003D),
  (0x10003D, .add 64 (.reg .rcx) (.reg .r14), 0x100040),
  (0x100040, .movzx8 .rcx (.mem .rcx 0x0), 0x100043),
  (0x100043, .add 64 (.reg .rax) (.reg .rcx), 0x100046),
  (0x100046, .mov 64 (.reg .r12) (.reg .rax), 0x100049),
  (0x100049, .mov 64 (.reg .rax) (.reg .r12), 0x10004C),
  (0x10004C, .mov 64 (.reg .rcx) (.imm 0xFFF1), 0x100053),
  (0x100053, .cmp 64 (.reg .rax) (.reg .rcx), 0x100056),
  (0x100056, .jae 0x10005A, 0x100058),
  (0x100058, .jmp 0x100066, 0x10005A),
  (0x10005A, .mov 64 (.reg .rax) (.reg .r12), 0x10005D),
  (0x10005D, .sub 64 (.reg .rax) (.imm 0xFFF1), 0x100063),
  (0x100063, .mov 64 (.reg .r12) (.reg .rax), 0x100066),
  (0x100066, .mov 64 (.reg .rax) (.reg .r13), 0x100069),
  (0x100069, .add 64 (.reg .rax) (.reg .r12), 0x10006C),
  (0x10006C, .mov 64 (.reg .r13) (.reg .rax), 0x10006F),
  (0x10006F, .mov 64 (.reg .rax) (.reg .r13), 0x100072),
  (0x100072, .mov 64 (.reg .rcx) (.imm 0xFFF1), 0x100079),
  (0x100079, .cmp 64 (.reg .rax) (.reg .rcx), 0x10007C),
  (0x10007C, .jae 0x100080, 0x10007E),
  (0x10007E, .jmp 0x10008C, 0x100080),
  (0x100080, .mov 64 (.reg .rax) (.reg .r13), 0x100083),
  (0x100083, .sub 64 (.reg .rax) (.imm 0xFFF1), 0x100089),
  (0x100089, .mov 64 (.reg .r13) (.reg .rax), 0x10008C),
  (0x10008C, .mov 64 (.reg .rax) (.reg .r14), 0x10008F),
  (0x10008F, .add 64 (.reg .rax) (.imm 0x1), 0x100093),
  (0x100093, .mov 64 (.reg .r14) (.reg .rax), 0x100096),
  (0x100096, .jmp 0x10002C, 0x100098),
  (0x100098, .mov 64 (.reg .rax) (.reg .r13), 0x10009B),
  (0x10009B, .shl64 .rax 16, 0x10009F),
  (0x10009F, .or 64 (.reg .rax) (.reg .r12), 0x1000A2),
  (0x1000A2, .pop .r14, 0x1000A4),
  (0x1000A4, .pop .r13, 0x1000A6),
  (0x1000A6, .pop .r12, 0x1000A8),
  (0x1000A8, .pop .rbp, 0x1000A9),
  (0x1000A9, .pop .rbx, 0x1000AA),
  (0x1000AA, .ret, 0x1000AB)
]

/-- Every instruction of the program: this function's (it calls nothing). -/
def whole : List (Nat × Instr × Nat) := table

def prog (pc : Nat) : Option (Instr × Nat) := whole.lookup pc

/-- The addresses the program has an instruction at. -/
def keys : List Nat := whole.map (·.1)

theorem keys_of : ∀ pc x, prog pc = some x → pc ∈ keys := fun pc x h => lookup_mem_keys whole pc x h

@[ode_at] theorem at_100000 : prog 0x100000 = some (.push .rbx, 0x100001) := rfl
@[ode_at] theorem at_100001 : prog 0x100001 = some (.push .rbp, 0x100002) := rfl
@[ode_at] theorem at_100002 : prog 0x100002 = some (.push .r12, 0x100004) := rfl
@[ode_at] theorem at_100004 : prog 0x100004 = some (.push .r13, 0x100006) := rfl
@[ode_at] theorem at_100006 : prog 0x100006 = some (.push .r14, 0x100008) := rfl
@[ode_at] theorem at_100008 : prog 0x100008 = some (.mov 64 (.reg .rbx) (.reg .rdi), 0x10000B) := rfl
@[ode_at] theorem at_10000B : prog 0x10000B = some (.mov 64 (.reg .rbp) (.reg .rsi), 0x10000E) := rfl
@[ode_at] theorem at_10000E : prog 0x10000E = some (.mov 64 (.reg .rax) (.imm 0x1), 0x100015) := rfl
@[ode_at] theorem at_100015 : prog 0x100015 = some (.mov 64 (.reg .r12) (.reg .rax), 0x100018) := rfl
@[ode_at] theorem at_100018 : prog 0x100018 = some (.mov 64 (.reg .rax) (.imm 0x0), 0x10001F) := rfl
@[ode_at] theorem at_10001F : prog 0x10001F = some (.mov 64 (.reg .r13) (.reg .rax), 0x100022) := rfl
@[ode_at] theorem at_100022 : prog 0x100022 = some (.mov 64 (.reg .rax) (.imm 0x0), 0x100029) := rfl
@[ode_at] theorem at_100029 : prog 0x100029 = some (.mov 64 (.reg .r14) (.reg .rax), 0x10002C) := rfl
@[ode_at] theorem at_10002C : prog 0x10002C = some (.mov 64 (.reg .rax) (.reg .r14), 0x10002F) := rfl
@[ode_at] theorem at_10002F : prog 0x10002F = some (.mov 64 (.reg .rcx) (.reg .rbp), 0x100032) := rfl
@[ode_at] theorem at_100032 : prog 0x100032 = some (.cmp 64 (.reg .rax) (.reg .rcx), 0x100035) := rfl
@[ode_at] theorem at_100035 : prog 0x100035 = some (.jae 0x100098, 0x100037) := rfl
@[ode_at] theorem at_100037 : prog 0x100037 = some (.mov 64 (.reg .rax) (.reg .r12), 0x10003A) := rfl
@[ode_at] theorem at_10003A : prog 0x10003A = some (.mov 64 (.reg .rcx) (.reg .rbx), 0x10003D) := rfl
@[ode_at] theorem at_10003D : prog 0x10003D = some (.add 64 (.reg .rcx) (.reg .r14), 0x100040) := rfl
@[ode_at] theorem at_100040 : prog 0x100040 = some (.movzx8 .rcx (.mem .rcx 0x0), 0x100043) := rfl
@[ode_at] theorem at_100043 : prog 0x100043 = some (.add 64 (.reg .rax) (.reg .rcx), 0x100046) := rfl
@[ode_at] theorem at_100046 : prog 0x100046 = some (.mov 64 (.reg .r12) (.reg .rax), 0x100049) := rfl
@[ode_at] theorem at_100049 : prog 0x100049 = some (.mov 64 (.reg .rax) (.reg .r12), 0x10004C) := rfl
@[ode_at] theorem at_10004C : prog 0x10004C = some (.mov 64 (.reg .rcx) (.imm 0xFFF1), 0x100053) := rfl
@[ode_at] theorem at_100053 : prog 0x100053 = some (.cmp 64 (.reg .rax) (.reg .rcx), 0x100056) := rfl
@[ode_at] theorem at_100056 : prog 0x100056 = some (.jae 0x10005A, 0x100058) := rfl
@[ode_at] theorem at_100058 : prog 0x100058 = some (.jmp 0x100066, 0x10005A) := rfl
@[ode_at] theorem at_10005A : prog 0x10005A = some (.mov 64 (.reg .rax) (.reg .r12), 0x10005D) := rfl
@[ode_at] theorem at_10005D : prog 0x10005D = some (.sub 64 (.reg .rax) (.imm 0xFFF1), 0x100063) := rfl
@[ode_at] theorem at_100063 : prog 0x100063 = some (.mov 64 (.reg .r12) (.reg .rax), 0x100066) := rfl
@[ode_at] theorem at_100066 : prog 0x100066 = some (.mov 64 (.reg .rax) (.reg .r13), 0x100069) := rfl
@[ode_at] theorem at_100069 : prog 0x100069 = some (.add 64 (.reg .rax) (.reg .r12), 0x10006C) := rfl
@[ode_at] theorem at_10006C : prog 0x10006C = some (.mov 64 (.reg .r13) (.reg .rax), 0x10006F) := rfl
@[ode_at] theorem at_10006F : prog 0x10006F = some (.mov 64 (.reg .rax) (.reg .r13), 0x100072) := rfl
@[ode_at] theorem at_100072 : prog 0x100072 = some (.mov 64 (.reg .rcx) (.imm 0xFFF1), 0x100079) := rfl
@[ode_at] theorem at_100079 : prog 0x100079 = some (.cmp 64 (.reg .rax) (.reg .rcx), 0x10007C) := rfl
@[ode_at] theorem at_10007C : prog 0x10007C = some (.jae 0x100080, 0x10007E) := rfl
@[ode_at] theorem at_10007E : prog 0x10007E = some (.jmp 0x10008C, 0x100080) := rfl
@[ode_at] theorem at_100080 : prog 0x100080 = some (.mov 64 (.reg .rax) (.reg .r13), 0x100083) := rfl
@[ode_at] theorem at_100083 : prog 0x100083 = some (.sub 64 (.reg .rax) (.imm 0xFFF1), 0x100089) := rfl
@[ode_at] theorem at_100089 : prog 0x100089 = some (.mov 64 (.reg .r13) (.reg .rax), 0x10008C) := rfl
@[ode_at] theorem at_10008C : prog 0x10008C = some (.mov 64 (.reg .rax) (.reg .r14), 0x10008F) := rfl
@[ode_at] theorem at_10008F : prog 0x10008F = some (.add 64 (.reg .rax) (.imm 0x1), 0x100093) := rfl
@[ode_at] theorem at_100093 : prog 0x100093 = some (.mov 64 (.reg .r14) (.reg .rax), 0x100096) := rfl
@[ode_at] theorem at_100096 : prog 0x100096 = some (.jmp 0x10002C, 0x100098) := rfl
@[ode_at] theorem at_100098 : prog 0x100098 = some (.mov 64 (.reg .rax) (.reg .r13), 0x10009B) := rfl
@[ode_at] theorem at_10009B : prog 0x10009B = some (.shl64 .rax 16, 0x10009F) := rfl
@[ode_at] theorem at_10009F : prog 0x10009F = some (.or 64 (.reg .rax) (.reg .r12), 0x1000A2) := rfl
@[ode_at] theorem at_1000A2 : prog 0x1000A2 = some (.pop .r14, 0x1000A4) := rfl
@[ode_at] theorem at_1000A4 : prog 0x1000A4 = some (.pop .r13, 0x1000A6) := rfl
@[ode_at] theorem at_1000A6 : prog 0x1000A6 = some (.pop .r12, 0x1000A8) := rfl
@[ode_at] theorem at_1000A8 : prog 0x1000A8 = some (.pop .rbp, 0x1000A9) := rfl
@[ode_at] theorem at_1000A9 : prog 0x1000A9 = some (.pop .rbx, 0x1000AA) := rfl
@[ode_at] theorem at_1000AA : prog 0x1000AA = some (.ret, 0x1000AB) := rfl

end Code_adler32
