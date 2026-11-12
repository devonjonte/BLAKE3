import Machine
import KCode
import Cells
open X86

/-! `merge_sse` as assembled: 85 instructions. Written from the lifter's rows. -/

set_option maxRecDepth 100000
namespace Code_merge_sse

def table : List (Nat × Instr × Nat) := [
  (0x90000, .push .rbx, 0x90001),
  (0x90001, .push .rbp, 0x90002),
  (0x90002, .push .r12, 0x90004),
  (0x90004, .push .r13, 0x90006),
  (0x90006, .push .r14, 0x90008),
  (0x90008, .push .r15, 0x9000A),
  (0x9000A, .sub 64 (.reg .rsp) (.imm 0x78), 0x9000E),
  (0x9000E, .mov 64 (.reg .rbx) (.reg .rdi), 0x90011),
  (0x90011, .mov 64 (.reg .rbp) (.reg .rsi), 0x90014),
  (0x90014, .mov 64 (.reg .r12) (.reg .rdx), 0x90017),
  (0x90017, .mov 64 (.reg .r13) (.reg .rcx), 0x9001A),
  (0x9001A, .mov 64 (.reg .r14) (.reg .r8), 0x9001D),
  (0x9001D, .mov 64 (.reg .rax) (.reg .rbx), 0x90020),
  (0x90020, .mov 64 (.reg .rax) (.mem .rax 0x0), 0x90023),
  (0x90023, .mov 64 (.reg .r15) (.reg .rax), 0x90026),
  (0x90026, .mov 64 (.reg .rax) (.reg .r12), 0x90029),
  (0x90029, .or 64 (.reg .rax) (.imm 0x4), 0x9002D),
  (0x9002D, .mov 64 (.mem .rsp 0x60) (.reg .rax), 0x90032),
  (0x90032, .mov 64 (.reg .rax) (.reg .r14), 0x90035),
  (0x90035, .mov 64 (.reg .rcx) (.reg .r15), 0x90038),
  (0x90038, .cmp 64 (.reg .rax) (.reg .rcx), 0x9003B),
  (0x9003B, .jae 0x900F8, 0x90041),
  (0x90041, .mov 64 (.reg .rax) (.reg .rbx), 0x90044),
  (0x90044, .add 64 (.reg .rax) (.imm 0x20), 0x90048),
  (0x90048, .mov 64 (.reg .rcx) (.reg .r15), 0x9004B),
  (0x9004B, .sub 64 (.reg .rcx) (.imm 0x2), 0x9004F),
  (0x9004F, .shl64 .rcx 5, 0x90053),
  (0x90053, .add 64 (.reg .rax) (.reg .rcx), 0x90056),
  (0x90056, .mov 64 (.mem .rsp 0x68) (.reg .rax), 0x9005B),
  (0x9005B, .mov 64 (.reg .rax) (.mem .rsp 0x68), 0x90060),
  (0x90060, .lea .rcx .rsp 0x0, 0x90064),
  (0x90064, .movv false 0 (.m .rax 0x0), 0x90067),
  (0x90067, .storev false .rcx 0x0 0, 0x9006A),
  (0x9006A, .movv false 0 (.m .rax 0x10), 0x9006E),
  (0x9006E, .storev false .rcx 0x10 0, 0x90072),
  (0x90072, .mov 64 (.reg .rax) (.mem .rsp 0x68), 0x90077),
  (0x90077, .add 64 (.reg .rax) (.imm 0x20), 0x9007B),
  (0x9007B, .lea .rcx .rsp 0x0, 0x9007F),
  (0x9007F, .add 64 (.reg .rcx) (.imm 0x20), 0x90083),
  (0x90083, .movv false 0 (.m .rax 0x0), 0x90086),
  (0x90086, .storev false .rcx 0x0 0, 0x90089),
  (0x90089, .movv false 0 (.m .rax 0x10), 0x9008D),
  (0x9008D, .storev false .rcx 0x10 0, 0x90091),
  (0x90091, .mov 64 (.reg .rax) (.reg .rbp), 0x90094),
  (0x90094, .lea .rcx .rsp 0x40, 0x90099),
  (0x90099, .movv false 0 (.m .rax 0x0), 0x9009C),
  (0x9009C, .storev false .rcx 0x0 0, 0x9009F),
  (0x9009F, .movv false 0 (.m .rax 0x10), 0x900A3),
  (0x900A3, .storev false .rcx 0x10 0, 0x900A7),
  (0x900A7, .lea .rdi .rsp 0x40, 0x900AC),
  (0x900AC, .lea .rsi .rsp 0x0, 0x900B0),
  (0x900B0, .mov 64 (.reg .rdx) (.imm 0x40), 0x900B7),
  (0x900B7, .mov 64 (.reg .rcx) (.imm 0x0), 0x900BE),
  (0x900BE, .mov 64 (.reg .r8) (.mem .rsp 0x60), 0x900C3),
  (0x900C3, .call 0x20000, 0x900C8),
  (0x900C8, .lea .rax .rsp 0x40, 0x900CD),
  (0x900CD, .mov 64 (.reg .rcx) (.mem .rsp 0x68), 0x900D2),
  (0x900D2, .movv false 0 (.m .rax 0x0), 0x900D5),
  (0x900D5, .storev false .rcx 0x0 0, 0x900D8),
  (0x900D8, .movv false 0 (.m .rax 0x10), 0x900DC),
  (0x900DC, .storev false .rcx 0x10 0, 0x900E0),
  (0x900E0, .mov 64 (.reg .rax) (.reg .r15), 0x900E3),
  (0x900E3, .sub 64 (.reg .rax) (.imm 0x1), 0x900E7),
  (0x900E7, .mov 64 (.reg .r15) (.reg .rax), 0x900EA),
  (0x900EA, .mov 64 (.reg .rax) (.reg .r15), 0x900ED),
  (0x900ED, .mov 64 (.reg .rcx) (.reg .rbx), 0x900F0),
  (0x900F0, .mov 64 (.mem .rcx 0x0) (.reg .rax), 0x900F3),
  (0x900F3, .jmp 0x90032, 0x900F8),
  (0x900F8, .mov 64 (.reg .rax) (.reg .r15), 0x900FB),
  (0x900FB, .add 64 (.reg .rsp) (.imm 0x78), 0x900FF),
  (0x900FF, .pop .r15, 0x90101),
  (0x90101, .pop .r14, 0x90103),
  (0x90103, .pop .r13, 0x90105),
  (0x90105, .pop .r12, 0x90107),
  (0x90107, .pop .rbp, 0x90108),
  (0x90108, .pop .rbx, 0x90109),
  (0x90109, .ret, 0x9010A),
  (0x90110, .cmp 64 (.reg .r8) (.imm 0x1), 0x90114),
  (0x90114, .jae 0x90118, 0x90116),
  (0x90116, .jmp 0x90126, 0x90118),
  (0x90118, .cmp 64 (.reg .rdx) (.imm 0x100), 0x9011F),
  (0x9011F, .jae 0x90126, 0x90121),
  (0x90121, .jmp 0x90000, 0x90126),
  (0x90126, .mov 64 (.reg .rax) (.imm 0xFFFFFFFFFFFFFFFF), 0x9012D),
  (0x9012D, .ret, 0x9012E)
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

@[ode_at] theorem at_90000 : prog 0x90000 = some (.push .rbx, 0x90001) := rfl
@[ode_at] theorem at_90001 : prog 0x90001 = some (.push .rbp, 0x90002) := rfl
@[ode_at] theorem at_90002 : prog 0x90002 = some (.push .r12, 0x90004) := rfl
@[ode_at] theorem at_90004 : prog 0x90004 = some (.push .r13, 0x90006) := rfl
@[ode_at] theorem at_90006 : prog 0x90006 = some (.push .r14, 0x90008) := rfl
@[ode_at] theorem at_90008 : prog 0x90008 = some (.push .r15, 0x9000A) := rfl
@[ode_at] theorem at_9000A : prog 0x9000A = some (.sub 64 (.reg .rsp) (.imm 0x78), 0x9000E) := rfl
@[ode_at] theorem at_9000E : prog 0x9000E = some (.mov 64 (.reg .rbx) (.reg .rdi), 0x90011) := rfl
@[ode_at] theorem at_90011 : prog 0x90011 = some (.mov 64 (.reg .rbp) (.reg .rsi), 0x90014) := rfl
@[ode_at] theorem at_90014 : prog 0x90014 = some (.mov 64 (.reg .r12) (.reg .rdx), 0x90017) := rfl
@[ode_at] theorem at_90017 : prog 0x90017 = some (.mov 64 (.reg .r13) (.reg .rcx), 0x9001A) := rfl
@[ode_at] theorem at_9001A : prog 0x9001A = some (.mov 64 (.reg .r14) (.reg .r8), 0x9001D) := rfl
@[ode_at] theorem at_9001D : prog 0x9001D = some (.mov 64 (.reg .rax) (.reg .rbx), 0x90020) := rfl
@[ode_at] theorem at_90020 : prog 0x90020 = some (.mov 64 (.reg .rax) (.mem .rax 0x0), 0x90023) := rfl
@[ode_at] theorem at_90023 : prog 0x90023 = some (.mov 64 (.reg .r15) (.reg .rax), 0x90026) := rfl
@[ode_at] theorem at_90026 : prog 0x90026 = some (.mov 64 (.reg .rax) (.reg .r12), 0x90029) := rfl
@[ode_at] theorem at_90029 : prog 0x90029 = some (.or 64 (.reg .rax) (.imm 0x4), 0x9002D) := rfl
@[ode_at] theorem at_9002D : prog 0x9002D = some (.mov 64 (.mem .rsp 0x60) (.reg .rax), 0x90032) := rfl
@[ode_at] theorem at_90032 : prog 0x90032 = some (.mov 64 (.reg .rax) (.reg .r14), 0x90035) := rfl
@[ode_at] theorem at_90035 : prog 0x90035 = some (.mov 64 (.reg .rcx) (.reg .r15), 0x90038) := rfl
@[ode_at] theorem at_90038 : prog 0x90038 = some (.cmp 64 (.reg .rax) (.reg .rcx), 0x9003B) := rfl
@[ode_at] theorem at_9003B : prog 0x9003B = some (.jae 0x900F8, 0x90041) := rfl
@[ode_at] theorem at_90041 : prog 0x90041 = some (.mov 64 (.reg .rax) (.reg .rbx), 0x90044) := rfl
@[ode_at] theorem at_90044 : prog 0x90044 = some (.add 64 (.reg .rax) (.imm 0x20), 0x90048) := rfl
@[ode_at] theorem at_90048 : prog 0x90048 = some (.mov 64 (.reg .rcx) (.reg .r15), 0x9004B) := rfl
@[ode_at] theorem at_9004B : prog 0x9004B = some (.sub 64 (.reg .rcx) (.imm 0x2), 0x9004F) := rfl
@[ode_at] theorem at_9004F : prog 0x9004F = some (.shl64 .rcx 5, 0x90053) := rfl
@[ode_at] theorem at_90053 : prog 0x90053 = some (.add 64 (.reg .rax) (.reg .rcx), 0x90056) := rfl
@[ode_at] theorem at_90056 : prog 0x90056 = some (.mov 64 (.mem .rsp 0x68) (.reg .rax), 0x9005B) := rfl
@[ode_at] theorem at_9005B : prog 0x9005B = some (.mov 64 (.reg .rax) (.mem .rsp 0x68), 0x90060) := rfl
@[ode_at] theorem at_90060 : prog 0x90060 = some (.lea .rcx .rsp 0x0, 0x90064) := rfl
@[ode_at] theorem at_90064 : prog 0x90064 = some (.movv false 0 (.m .rax 0x0), 0x90067) := rfl
@[ode_at] theorem at_90067 : prog 0x90067 = some (.storev false .rcx 0x0 0, 0x9006A) := rfl
@[ode_at] theorem at_9006A : prog 0x9006A = some (.movv false 0 (.m .rax 0x10), 0x9006E) := rfl
@[ode_at] theorem at_9006E : prog 0x9006E = some (.storev false .rcx 0x10 0, 0x90072) := rfl
@[ode_at] theorem at_90072 : prog 0x90072 = some (.mov 64 (.reg .rax) (.mem .rsp 0x68), 0x90077) := rfl
@[ode_at] theorem at_90077 : prog 0x90077 = some (.add 64 (.reg .rax) (.imm 0x20), 0x9007B) := rfl
@[ode_at] theorem at_9007B : prog 0x9007B = some (.lea .rcx .rsp 0x0, 0x9007F) := rfl
@[ode_at] theorem at_9007F : prog 0x9007F = some (.add 64 (.reg .rcx) (.imm 0x20), 0x90083) := rfl
@[ode_at] theorem at_90083 : prog 0x90083 = some (.movv false 0 (.m .rax 0x0), 0x90086) := rfl
@[ode_at] theorem at_90086 : prog 0x90086 = some (.storev false .rcx 0x0 0, 0x90089) := rfl
@[ode_at] theorem at_90089 : prog 0x90089 = some (.movv false 0 (.m .rax 0x10), 0x9008D) := rfl
@[ode_at] theorem at_9008D : prog 0x9008D = some (.storev false .rcx 0x10 0, 0x90091) := rfl
@[ode_at] theorem at_90091 : prog 0x90091 = some (.mov 64 (.reg .rax) (.reg .rbp), 0x90094) := rfl
@[ode_at] theorem at_90094 : prog 0x90094 = some (.lea .rcx .rsp 0x40, 0x90099) := rfl
@[ode_at] theorem at_90099 : prog 0x90099 = some (.movv false 0 (.m .rax 0x0), 0x9009C) := rfl
@[ode_at] theorem at_9009C : prog 0x9009C = some (.storev false .rcx 0x0 0, 0x9009F) := rfl
@[ode_at] theorem at_9009F : prog 0x9009F = some (.movv false 0 (.m .rax 0x10), 0x900A3) := rfl
@[ode_at] theorem at_900A3 : prog 0x900A3 = some (.storev false .rcx 0x10 0, 0x900A7) := rfl
@[ode_at] theorem at_900A7 : prog 0x900A7 = some (.lea .rdi .rsp 0x40, 0x900AC) := rfl
@[ode_at] theorem at_900AC : prog 0x900AC = some (.lea .rsi .rsp 0x0, 0x900B0) := rfl
@[ode_at] theorem at_900B0 : prog 0x900B0 = some (.mov 64 (.reg .rdx) (.imm 0x40), 0x900B7) := rfl
@[ode_at] theorem at_900B7 : prog 0x900B7 = some (.mov 64 (.reg .rcx) (.imm 0x0), 0x900BE) := rfl
@[ode_at] theorem at_900BE : prog 0x900BE = some (.mov 64 (.reg .r8) (.mem .rsp 0x60), 0x900C3) := rfl
@[ode_at] theorem at_900C3 : prog 0x900C3 = some (.call 0x20000, 0x900C8) := rfl
@[ode_at] theorem at_900C8 : prog 0x900C8 = some (.lea .rax .rsp 0x40, 0x900CD) := rfl
@[ode_at] theorem at_900CD : prog 0x900CD = some (.mov 64 (.reg .rcx) (.mem .rsp 0x68), 0x900D2) := rfl
@[ode_at] theorem at_900D2 : prog 0x900D2 = some (.movv false 0 (.m .rax 0x0), 0x900D5) := rfl
@[ode_at] theorem at_900D5 : prog 0x900D5 = some (.storev false .rcx 0x0 0, 0x900D8) := rfl
@[ode_at] theorem at_900D8 : prog 0x900D8 = some (.movv false 0 (.m .rax 0x10), 0x900DC) := rfl
@[ode_at] theorem at_900DC : prog 0x900DC = some (.storev false .rcx 0x10 0, 0x900E0) := rfl
@[ode_at] theorem at_900E0 : prog 0x900E0 = some (.mov 64 (.reg .rax) (.reg .r15), 0x900E3) := rfl
@[ode_at] theorem at_900E3 : prog 0x900E3 = some (.sub 64 (.reg .rax) (.imm 0x1), 0x900E7) := rfl
@[ode_at] theorem at_900E7 : prog 0x900E7 = some (.mov 64 (.reg .r15) (.reg .rax), 0x900EA) := rfl
@[ode_at] theorem at_900EA : prog 0x900EA = some (.mov 64 (.reg .rax) (.reg .r15), 0x900ED) := rfl
@[ode_at] theorem at_900ED : prog 0x900ED = some (.mov 64 (.reg .rcx) (.reg .rbx), 0x900F0) := rfl
@[ode_at] theorem at_900F0 : prog 0x900F0 = some (.mov 64 (.mem .rcx 0x0) (.reg .rax), 0x900F3) := rfl
@[ode_at] theorem at_900F3 : prog 0x900F3 = some (.jmp 0x90032, 0x900F8) := rfl
@[ode_at] theorem at_900F8 : prog 0x900F8 = some (.mov 64 (.reg .rax) (.reg .r15), 0x900FB) := rfl
@[ode_at] theorem at_900FB : prog 0x900FB = some (.add 64 (.reg .rsp) (.imm 0x78), 0x900FF) := rfl
@[ode_at] theorem at_900FF : prog 0x900FF = some (.pop .r15, 0x90101) := rfl
@[ode_at] theorem at_90101 : prog 0x90101 = some (.pop .r14, 0x90103) := rfl
@[ode_at] theorem at_90103 : prog 0x90103 = some (.pop .r13, 0x90105) := rfl
@[ode_at] theorem at_90105 : prog 0x90105 = some (.pop .r12, 0x90107) := rfl
@[ode_at] theorem at_90107 : prog 0x90107 = some (.pop .rbp, 0x90108) := rfl
@[ode_at] theorem at_90108 : prog 0x90108 = some (.pop .rbx, 0x90109) := rfl
@[ode_at] theorem at_90109 : prog 0x90109 = some (.ret, 0x9010A) := rfl
@[ode_at] theorem at_90110 : prog 0x90110 = some (.cmp 64 (.reg .r8) (.imm 0x1), 0x90114) := rfl
@[ode_at] theorem at_90114 : prog 0x90114 = some (.jae 0x90118, 0x90116) := rfl
@[ode_at] theorem at_90116 : prog 0x90116 = some (.jmp 0x90126, 0x90118) := rfl
@[ode_at] theorem at_90118 : prog 0x90118 = some (.cmp 64 (.reg .rdx) (.imm 0x100), 0x9011F) := rfl
@[ode_at] theorem at_9011F : prog 0x9011F = some (.jae 0x90126, 0x90121) := rfl
@[ode_at] theorem at_90121 : prog 0x90121 = some (.jmp 0x90000, 0x90126) := rfl
@[ode_at] theorem at_90126 : prog 0x90126 = some (.mov 64 (.reg .rax) (.imm 0xFFFFFFFFFFFFFFFF), 0x9012D) := rfl
@[ode_at] theorem at_9012D : prog 0x9012D = some (.ret, 0x9012E) := rfl

end Code_merge_sse
