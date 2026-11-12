import Machine
import KCode
import Cells
open X86

/-! `merge` as assembled: 96 instructions. Written from the lifter's rows. -/

set_option maxRecDepth 100000
namespace Code_merge

def table : List (Nat × Instr × Nat) := [
  (0x60000, .push .rbx, 0x60001),
  (0x60001, .push .rbp, 0x60002),
  (0x60002, .push .r12, 0x60004),
  (0x60004, .push .r13, 0x60006),
  (0x60006, .push .r14, 0x60008),
  (0x60008, .push .r15, 0x6000A),
  (0x6000A, .sub 64 (.reg .rsp) (.imm 0x78), 0x6000E),
  (0x6000E, .mov 64 (.reg .rbx) (.reg .rdi), 0x60011),
  (0x60011, .mov 64 (.reg .rbp) (.reg .rsi), 0x60014),
  (0x60014, .mov 64 (.reg .r12) (.reg .rdx), 0x60017),
  (0x60017, .mov 64 (.reg .r13) (.reg .rcx), 0x6001A),
  (0x6001A, .mov 64 (.reg .r14) (.reg .r8), 0x6001D),
  (0x6001D, .mov 64 (.reg .rax) (.reg .rbx), 0x60020),
  (0x60020, .mov 64 (.reg .rax) (.mem .rax 0x0), 0x60023),
  (0x60023, .mov 64 (.reg .r15) (.reg .rax), 0x60026),
  (0x60026, .mov 64 (.reg .rax) (.reg .r12), 0x60029),
  (0x60029, .or 64 (.reg .rax) (.imm 0x4), 0x6002D),
  (0x6002D, .mov 64 (.mem .rsp 0x60) (.reg .rax), 0x60032),
  (0x60032, .mov 64 (.reg .rax) (.reg .r14), 0x60035),
  (0x60035, .mov 64 (.reg .rcx) (.reg .r15), 0x60038),
  (0x60038, .cmp 64 (.reg .rax) (.reg .rcx), 0x6003B),
  (0x6003B, .jae 0x6012A, 0x60041),
  (0x60041, .mov 64 (.reg .rax) (.reg .rbx), 0x60044),
  (0x60044, .add 64 (.reg .rax) (.imm 0x20), 0x60048),
  (0x60048, .mov 64 (.reg .rcx) (.reg .r15), 0x6004B),
  (0x6004B, .sub 64 (.reg .rcx) (.imm 0x2), 0x6004F),
  (0x6004F, .shl64 .rcx 5, 0x60053),
  (0x60053, .add 64 (.reg .rax) (.reg .rcx), 0x60056),
  (0x60056, .mov 64 (.mem .rsp 0x68) (.reg .rax), 0x6005B),
  (0x6005B, .mov 64 (.reg .rax) (.mem .rsp 0x68), 0x60060),
  (0x60060, .lea .rcx .rsp 0x0, 0x60064),
  (0x60064, .movv false 0 (.m .rax 0x0), 0x60067),
  (0x60067, .storev false .rcx 0x0 0, 0x6006A),
  (0x6006A, .movv false 0 (.m .rax 0x10), 0x6006E),
  (0x6006E, .storev false .rcx 0x10 0, 0x60072),
  (0x60072, .mov 64 (.reg .rax) (.mem .rsp 0x68), 0x60077),
  (0x60077, .add 64 (.reg .rax) (.imm 0x20), 0x6007B),
  (0x6007B, .lea .rcx .rsp 0x0, 0x6007F),
  (0x6007F, .add 64 (.reg .rcx) (.imm 0x20), 0x60083),
  (0x60083, .movv false 0 (.m .rax 0x0), 0x60086),
  (0x60086, .storev false .rcx 0x0 0, 0x60089),
  (0x60089, .movv false 0 (.m .rax 0x10), 0x6008D),
  (0x6008D, .storev false .rcx 0x10 0, 0x60091),
  (0x60091, .mov 64 (.reg .rax) (.reg .rbp), 0x60094),
  (0x60094, .lea .rcx .rsp 0x40, 0x60099),
  (0x60099, .movv false 0 (.m .rax 0x0), 0x6009C),
  (0x6009C, .storev false .rcx 0x0 0, 0x6009F),
  (0x6009F, .movv false 0 (.m .rax 0x10), 0x600A3),
  (0x600A3, .storev false .rcx 0x10 0, 0x600A7),
  (0x600A7, .mov 64 (.reg .rax) (.reg .r13), 0x600AA),
  (0x600AA, .mov 64 (.reg .rcx) (.imm 0x5), 0x600B1),
  (0x600B1, .cmp 64 (.reg .rax) (.reg .rcx), 0x600B4),
  (0x600B4, .jne 0x600D9, 0x600B6),
  (0x600B6, .lea .rdi .rsp 0x40, 0x600BB),
  (0x600BB, .lea .rsi .rsp 0x0, 0x600BF),
  (0x600BF, .mov 64 (.reg .rdx) (.imm 0x40), 0x600C6),
  (0x600C6, .mov 64 (.reg .rcx) (.imm 0x0), 0x600CD),
  (0x600CD, .mov 64 (.reg .r8) (.mem .rsp 0x60), 0x600D2),
  (0x600D2, .call 0x30000, 0x600D7),
  (0x600D7, .jmp 0x600FA, 0x600D9),
  (0x600D9, .lea .rdi .rsp 0x40, 0x600DE),
  (0x600DE, .lea .rsi .rsp 0x0, 0x600E2),
  (0x600E2, .mov 64 (.reg .rdx) (.imm 0x40), 0x600E9),
  (0x600E9, .mov 64 (.reg .rcx) (.imm 0x0), 0x600F0),
  (0x600F0, .mov 64 (.reg .r8) (.mem .rsp 0x60), 0x600F5),
  (0x600F5, .call 0x20000, 0x600FA),
  (0x600FA, .lea .rax .rsp 0x40, 0x600FF),
  (0x600FF, .mov 64 (.reg .rcx) (.mem .rsp 0x68), 0x60104),
  (0x60104, .movv false 0 (.m .rax 0x0), 0x60107),
  (0x60107, .storev false .rcx 0x0 0, 0x6010A),
  (0x6010A, .movv false 0 (.m .rax 0x10), 0x6010E),
  (0x6010E, .storev false .rcx 0x10 0, 0x60112),
  (0x60112, .mov 64 (.reg .rax) (.reg .r15), 0x60115),
  (0x60115, .sub 64 (.reg .rax) (.imm 0x1), 0x60119),
  (0x60119, .mov 64 (.reg .r15) (.reg .rax), 0x6011C),
  (0x6011C, .mov 64 (.reg .rax) (.reg .r15), 0x6011F),
  (0x6011F, .mov 64 (.reg .rcx) (.reg .rbx), 0x60122),
  (0x60122, .mov 64 (.mem .rcx 0x0) (.reg .rax), 0x60125),
  (0x60125, .jmp 0x60032, 0x6012A),
  (0x6012A, .mov 64 (.reg .rax) (.reg .r15), 0x6012D),
  (0x6012D, .add 64 (.reg .rsp) (.imm 0x78), 0x60131),
  (0x60131, .pop .r15, 0x60133),
  (0x60133, .pop .r14, 0x60135),
  (0x60135, .pop .r13, 0x60137),
  (0x60137, .pop .r12, 0x60139),
  (0x60139, .pop .rbp, 0x6013A),
  (0x6013A, .pop .rbx, 0x6013B),
  (0x6013B, .ret, 0x6013C),
  (0x60140, .cmp 64 (.reg .r8) (.imm 0x1), 0x60144),
  (0x60144, .jae 0x60148, 0x60146),
  (0x60146, .jmp 0x60156, 0x60148),
  (0x60148, .cmp 64 (.reg .rdx) (.imm 0x100), 0x6014F),
  (0x6014F, .jae 0x60156, 0x60151),
  (0x60151, .jmp 0x60000, 0x60156),
  (0x60156, .mov 64 (.reg .rax) (.imm 0xFFFFFFFFFFFFFFFF), 0x6015D),
  (0x6015D, .ret, 0x6015E)
]

/-- This function's instructions and the two kernels' (one/KCode.lean) as one program. -/
def prog (pc : Nat) : Option (Instr × Nat) := (KCode.prog pc).or (table.lookup pc)

theorem has_kernels : ∀ pc x, KCode.prog pc = some x → prog pc = some x := by
  intro pc x h; simp only [prog, h, Option.some_or]

@[ode_at] theorem at_60000 : prog 0x60000 = some (.push .rbx, 0x60001) := rfl
@[ode_at] theorem at_60001 : prog 0x60001 = some (.push .rbp, 0x60002) := rfl
@[ode_at] theorem at_60002 : prog 0x60002 = some (.push .r12, 0x60004) := rfl
@[ode_at] theorem at_60004 : prog 0x60004 = some (.push .r13, 0x60006) := rfl
@[ode_at] theorem at_60006 : prog 0x60006 = some (.push .r14, 0x60008) := rfl
@[ode_at] theorem at_60008 : prog 0x60008 = some (.push .r15, 0x6000A) := rfl
@[ode_at] theorem at_6000A : prog 0x6000A = some (.sub 64 (.reg .rsp) (.imm 0x78), 0x6000E) := rfl
@[ode_at] theorem at_6000E : prog 0x6000E = some (.mov 64 (.reg .rbx) (.reg .rdi), 0x60011) := rfl
@[ode_at] theorem at_60011 : prog 0x60011 = some (.mov 64 (.reg .rbp) (.reg .rsi), 0x60014) := rfl
@[ode_at] theorem at_60014 : prog 0x60014 = some (.mov 64 (.reg .r12) (.reg .rdx), 0x60017) := rfl
@[ode_at] theorem at_60017 : prog 0x60017 = some (.mov 64 (.reg .r13) (.reg .rcx), 0x6001A) := rfl
@[ode_at] theorem at_6001A : prog 0x6001A = some (.mov 64 (.reg .r14) (.reg .r8), 0x6001D) := rfl
@[ode_at] theorem at_6001D : prog 0x6001D = some (.mov 64 (.reg .rax) (.reg .rbx), 0x60020) := rfl
@[ode_at] theorem at_60020 : prog 0x60020 = some (.mov 64 (.reg .rax) (.mem .rax 0x0), 0x60023) := rfl
@[ode_at] theorem at_60023 : prog 0x60023 = some (.mov 64 (.reg .r15) (.reg .rax), 0x60026) := rfl
@[ode_at] theorem at_60026 : prog 0x60026 = some (.mov 64 (.reg .rax) (.reg .r12), 0x60029) := rfl
@[ode_at] theorem at_60029 : prog 0x60029 = some (.or 64 (.reg .rax) (.imm 0x4), 0x6002D) := rfl
@[ode_at] theorem at_6002D : prog 0x6002D = some (.mov 64 (.mem .rsp 0x60) (.reg .rax), 0x60032) := rfl
@[ode_at] theorem at_60032 : prog 0x60032 = some (.mov 64 (.reg .rax) (.reg .r14), 0x60035) := rfl
@[ode_at] theorem at_60035 : prog 0x60035 = some (.mov 64 (.reg .rcx) (.reg .r15), 0x60038) := rfl
@[ode_at] theorem at_60038 : prog 0x60038 = some (.cmp 64 (.reg .rax) (.reg .rcx), 0x6003B) := rfl
@[ode_at] theorem at_6003B : prog 0x6003B = some (.jae 0x6012A, 0x60041) := rfl
@[ode_at] theorem at_60041 : prog 0x60041 = some (.mov 64 (.reg .rax) (.reg .rbx), 0x60044) := rfl
@[ode_at] theorem at_60044 : prog 0x60044 = some (.add 64 (.reg .rax) (.imm 0x20), 0x60048) := rfl
@[ode_at] theorem at_60048 : prog 0x60048 = some (.mov 64 (.reg .rcx) (.reg .r15), 0x6004B) := rfl
@[ode_at] theorem at_6004B : prog 0x6004B = some (.sub 64 (.reg .rcx) (.imm 0x2), 0x6004F) := rfl
@[ode_at] theorem at_6004F : prog 0x6004F = some (.shl64 .rcx 5, 0x60053) := rfl
@[ode_at] theorem at_60053 : prog 0x60053 = some (.add 64 (.reg .rax) (.reg .rcx), 0x60056) := rfl
@[ode_at] theorem at_60056 : prog 0x60056 = some (.mov 64 (.mem .rsp 0x68) (.reg .rax), 0x6005B) := rfl
@[ode_at] theorem at_6005B : prog 0x6005B = some (.mov 64 (.reg .rax) (.mem .rsp 0x68), 0x60060) := rfl
@[ode_at] theorem at_60060 : prog 0x60060 = some (.lea .rcx .rsp 0x0, 0x60064) := rfl
@[ode_at] theorem at_60064 : prog 0x60064 = some (.movv false 0 (.m .rax 0x0), 0x60067) := rfl
@[ode_at] theorem at_60067 : prog 0x60067 = some (.storev false .rcx 0x0 0, 0x6006A) := rfl
@[ode_at] theorem at_6006A : prog 0x6006A = some (.movv false 0 (.m .rax 0x10), 0x6006E) := rfl
@[ode_at] theorem at_6006E : prog 0x6006E = some (.storev false .rcx 0x10 0, 0x60072) := rfl
@[ode_at] theorem at_60072 : prog 0x60072 = some (.mov 64 (.reg .rax) (.mem .rsp 0x68), 0x60077) := rfl
@[ode_at] theorem at_60077 : prog 0x60077 = some (.add 64 (.reg .rax) (.imm 0x20), 0x6007B) := rfl
@[ode_at] theorem at_6007B : prog 0x6007B = some (.lea .rcx .rsp 0x0, 0x6007F) := rfl
@[ode_at] theorem at_6007F : prog 0x6007F = some (.add 64 (.reg .rcx) (.imm 0x20), 0x60083) := rfl
@[ode_at] theorem at_60083 : prog 0x60083 = some (.movv false 0 (.m .rax 0x0), 0x60086) := rfl
@[ode_at] theorem at_60086 : prog 0x60086 = some (.storev false .rcx 0x0 0, 0x60089) := rfl
@[ode_at] theorem at_60089 : prog 0x60089 = some (.movv false 0 (.m .rax 0x10), 0x6008D) := rfl
@[ode_at] theorem at_6008D : prog 0x6008D = some (.storev false .rcx 0x10 0, 0x60091) := rfl
@[ode_at] theorem at_60091 : prog 0x60091 = some (.mov 64 (.reg .rax) (.reg .rbp), 0x60094) := rfl
@[ode_at] theorem at_60094 : prog 0x60094 = some (.lea .rcx .rsp 0x40, 0x60099) := rfl
@[ode_at] theorem at_60099 : prog 0x60099 = some (.movv false 0 (.m .rax 0x0), 0x6009C) := rfl
@[ode_at] theorem at_6009C : prog 0x6009C = some (.storev false .rcx 0x0 0, 0x6009F) := rfl
@[ode_at] theorem at_6009F : prog 0x6009F = some (.movv false 0 (.m .rax 0x10), 0x600A3) := rfl
@[ode_at] theorem at_600A3 : prog 0x600A3 = some (.storev false .rcx 0x10 0, 0x600A7) := rfl
@[ode_at] theorem at_600A7 : prog 0x600A7 = some (.mov 64 (.reg .rax) (.reg .r13), 0x600AA) := rfl
@[ode_at] theorem at_600AA : prog 0x600AA = some (.mov 64 (.reg .rcx) (.imm 0x5), 0x600B1) := rfl
@[ode_at] theorem at_600B1 : prog 0x600B1 = some (.cmp 64 (.reg .rax) (.reg .rcx), 0x600B4) := rfl
@[ode_at] theorem at_600B4 : prog 0x600B4 = some (.jne 0x600D9, 0x600B6) := rfl
@[ode_at] theorem at_600B6 : prog 0x600B6 = some (.lea .rdi .rsp 0x40, 0x600BB) := rfl
@[ode_at] theorem at_600BB : prog 0x600BB = some (.lea .rsi .rsp 0x0, 0x600BF) := rfl
@[ode_at] theorem at_600BF : prog 0x600BF = some (.mov 64 (.reg .rdx) (.imm 0x40), 0x600C6) := rfl
@[ode_at] theorem at_600C6 : prog 0x600C6 = some (.mov 64 (.reg .rcx) (.imm 0x0), 0x600CD) := rfl
@[ode_at] theorem at_600CD : prog 0x600CD = some (.mov 64 (.reg .r8) (.mem .rsp 0x60), 0x600D2) := rfl
@[ode_at] theorem at_600D2 : prog 0x600D2 = some (.call 0x30000, 0x600D7) := rfl
@[ode_at] theorem at_600D7 : prog 0x600D7 = some (.jmp 0x600FA, 0x600D9) := rfl
@[ode_at] theorem at_600D9 : prog 0x600D9 = some (.lea .rdi .rsp 0x40, 0x600DE) := rfl
@[ode_at] theorem at_600DE : prog 0x600DE = some (.lea .rsi .rsp 0x0, 0x600E2) := rfl
@[ode_at] theorem at_600E2 : prog 0x600E2 = some (.mov 64 (.reg .rdx) (.imm 0x40), 0x600E9) := rfl
@[ode_at] theorem at_600E9 : prog 0x600E9 = some (.mov 64 (.reg .rcx) (.imm 0x0), 0x600F0) := rfl
@[ode_at] theorem at_600F0 : prog 0x600F0 = some (.mov 64 (.reg .r8) (.mem .rsp 0x60), 0x600F5) := rfl
@[ode_at] theorem at_600F5 : prog 0x600F5 = some (.call 0x20000, 0x600FA) := rfl
@[ode_at] theorem at_600FA : prog 0x600FA = some (.lea .rax .rsp 0x40, 0x600FF) := rfl
@[ode_at] theorem at_600FF : prog 0x600FF = some (.mov 64 (.reg .rcx) (.mem .rsp 0x68), 0x60104) := rfl
@[ode_at] theorem at_60104 : prog 0x60104 = some (.movv false 0 (.m .rax 0x0), 0x60107) := rfl
@[ode_at] theorem at_60107 : prog 0x60107 = some (.storev false .rcx 0x0 0, 0x6010A) := rfl
@[ode_at] theorem at_6010A : prog 0x6010A = some (.movv false 0 (.m .rax 0x10), 0x6010E) := rfl
@[ode_at] theorem at_6010E : prog 0x6010E = some (.storev false .rcx 0x10 0, 0x60112) := rfl
@[ode_at] theorem at_60112 : prog 0x60112 = some (.mov 64 (.reg .rax) (.reg .r15), 0x60115) := rfl
@[ode_at] theorem at_60115 : prog 0x60115 = some (.sub 64 (.reg .rax) (.imm 0x1), 0x60119) := rfl
@[ode_at] theorem at_60119 : prog 0x60119 = some (.mov 64 (.reg .r15) (.reg .rax), 0x6011C) := rfl
@[ode_at] theorem at_6011C : prog 0x6011C = some (.mov 64 (.reg .rax) (.reg .r15), 0x6011F) := rfl
@[ode_at] theorem at_6011F : prog 0x6011F = some (.mov 64 (.reg .rcx) (.reg .rbx), 0x60122) := rfl
@[ode_at] theorem at_60122 : prog 0x60122 = some (.mov 64 (.mem .rcx 0x0) (.reg .rax), 0x60125) := rfl
@[ode_at] theorem at_60125 : prog 0x60125 = some (.jmp 0x60032, 0x6012A) := rfl
@[ode_at] theorem at_6012A : prog 0x6012A = some (.mov 64 (.reg .rax) (.reg .r15), 0x6012D) := rfl
@[ode_at] theorem at_6012D : prog 0x6012D = some (.add 64 (.reg .rsp) (.imm 0x78), 0x60131) := rfl
@[ode_at] theorem at_60131 : prog 0x60131 = some (.pop .r15, 0x60133) := rfl
@[ode_at] theorem at_60133 : prog 0x60133 = some (.pop .r14, 0x60135) := rfl
@[ode_at] theorem at_60135 : prog 0x60135 = some (.pop .r13, 0x60137) := rfl
@[ode_at] theorem at_60137 : prog 0x60137 = some (.pop .r12, 0x60139) := rfl
@[ode_at] theorem at_60139 : prog 0x60139 = some (.pop .rbp, 0x6013A) := rfl
@[ode_at] theorem at_6013A : prog 0x6013A = some (.pop .rbx, 0x6013B) := rfl
@[ode_at] theorem at_6013B : prog 0x6013B = some (.ret, 0x6013C) := rfl
@[ode_at] theorem at_60140 : prog 0x60140 = some (.cmp 64 (.reg .r8) (.imm 0x1), 0x60144) := rfl
@[ode_at] theorem at_60144 : prog 0x60144 = some (.jae 0x60148, 0x60146) := rfl
@[ode_at] theorem at_60146 : prog 0x60146 = some (.jmp 0x60156, 0x60148) := rfl
@[ode_at] theorem at_60148 : prog 0x60148 = some (.cmp 64 (.reg .rdx) (.imm 0x100), 0x6014F) := rfl
@[ode_at] theorem at_6014F : prog 0x6014F = some (.jae 0x60156, 0x60151) := rfl
@[ode_at] theorem at_60151 : prog 0x60151 = some (.jmp 0x60000, 0x60156) := rfl
@[ode_at] theorem at_60156 : prog 0x60156 = some (.mov 64 (.reg .rax) (.imm 0xFFFFFFFFFFFFFFFF), 0x6015D) := rfl
@[ode_at] theorem at_6015D : prog 0x6015D = some (.ret, 0x6015E) := rfl

end Code_merge
