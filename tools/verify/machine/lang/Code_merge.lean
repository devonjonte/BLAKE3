import Machine
import KCode
import Cells
open X86

/-! `merge` as assembled: 93 instructions. Written from the lifter's rows. -/

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
  (0x6003B, .jae 0x6013D, 0x60041),
  (0x60041, .mov 64 (.reg .rax) (.reg .r15), 0x60044),
  (0x60044, .mov 64 (.reg .rcx) (.imm 0x2), 0x6004B),
  (0x6004B, .cmp 64 (.reg .rax) (.reg .rcx), 0x6004E),
  (0x6004E, .jae 0x60054, 0x60050),
  (0x60052, .jmp 0x60054, 0x60054),
  (0x60054, .mov 64 (.reg .rax) (.reg .rbx), 0x60057),
  (0x60057, .add 64 (.reg .rax) (.imm 0x20), 0x6005B),
  (0x6005B, .mov 64 (.reg .rcx) (.reg .r15), 0x6005E),
  (0x6005E, .sub 64 (.reg .rcx) (.imm 0x2), 0x60062),
  (0x60062, .shl64 .rcx 5, 0x60066),
  (0x60066, .add 64 (.reg .rax) (.reg .rcx), 0x60069),
  (0x60069, .mov 64 (.mem .rsp 0x68) (.reg .rax), 0x6006E),
  (0x6006E, .mov 64 (.reg .rax) (.mem .rsp 0x68), 0x60073),
  (0x60073, .lea .rcx .rsp 0x0, 0x60077),
  (0x60077, .movv false 0 (.m .rax 0x0), 0x6007A),
  (0x6007A, .storev false .rcx 0x0 0, 0x6007D),
  (0x6007D, .movv false 0 (.m .rax 0x10), 0x60081),
  (0x60081, .storev false .rcx 0x10 0, 0x60085),
  (0x60085, .mov 64 (.reg .rax) (.mem .rsp 0x68), 0x6008A),
  (0x6008A, .add 64 (.reg .rax) (.imm 0x20), 0x6008E),
  (0x6008E, .lea .rcx .rsp 0x0, 0x60092),
  (0x60092, .add 64 (.reg .rcx) (.imm 0x20), 0x60096),
  (0x60096, .movv false 0 (.m .rax 0x0), 0x60099),
  (0x60099, .storev false .rcx 0x0 0, 0x6009C),
  (0x6009C, .movv false 0 (.m .rax 0x10), 0x600A0),
  (0x600A0, .storev false .rcx 0x10 0, 0x600A4),
  (0x600A4, .mov 64 (.reg .rax) (.reg .rbp), 0x600A7),
  (0x600A7, .lea .rcx .rsp 0x40, 0x600AC),
  (0x600AC, .movv false 0 (.m .rax 0x0), 0x600AF),
  (0x600AF, .storev false .rcx 0x0 0, 0x600B2),
  (0x600B2, .movv false 0 (.m .rax 0x10), 0x600B6),
  (0x600B6, .storev false .rcx 0x10 0, 0x600BA),
  (0x600BA, .mov 64 (.reg .rax) (.reg .r13), 0x600BD),
  (0x600BD, .mov 64 (.reg .rcx) (.imm 0x5), 0x600C4),
  (0x600C4, .cmp 64 (.reg .rax) (.reg .rcx), 0x600C7),
  (0x600C7, .jne 0x600EC, 0x600C9),
  (0x600C9, .lea .rdi .rsp 0x40, 0x600CE),
  (0x600CE, .lea .rsi .rsp 0x0, 0x600D2),
  (0x600D2, .mov 64 (.reg .rdx) (.imm 0x40), 0x600D9),
  (0x600D9, .mov 64 (.reg .rcx) (.imm 0x0), 0x600E0),
  (0x600E0, .mov 64 (.reg .r8) (.mem .rsp 0x60), 0x600E5),
  (0x600E5, .call 0x30000, 0x600EA),
  (0x600EA, .jmp 0x6010D, 0x600EC),
  (0x600EC, .lea .rdi .rsp 0x40, 0x600F1),
  (0x600F1, .lea .rsi .rsp 0x0, 0x600F5),
  (0x600F5, .mov 64 (.reg .rdx) (.imm 0x40), 0x600FC),
  (0x600FC, .mov 64 (.reg .rcx) (.imm 0x0), 0x60103),
  (0x60103, .mov 64 (.reg .r8) (.mem .rsp 0x60), 0x60108),
  (0x60108, .call 0x20000, 0x6010D),
  (0x6010D, .lea .rax .rsp 0x40, 0x60112),
  (0x60112, .mov 64 (.reg .rcx) (.mem .rsp 0x68), 0x60117),
  (0x60117, .movv false 0 (.m .rax 0x0), 0x6011A),
  (0x6011A, .storev false .rcx 0x0 0, 0x6011D),
  (0x6011D, .movv false 0 (.m .rax 0x10), 0x60121),
  (0x60121, .storev false .rcx 0x10 0, 0x60125),
  (0x60125, .mov 64 (.reg .rax) (.reg .r15), 0x60128),
  (0x60128, .sub 64 (.reg .rax) (.imm 0x1), 0x6012C),
  (0x6012C, .mov 64 (.reg .r15) (.reg .rax), 0x6012F),
  (0x6012F, .mov 64 (.reg .rax) (.reg .r15), 0x60132),
  (0x60132, .mov 64 (.reg .rcx) (.reg .rbx), 0x60135),
  (0x60135, .mov 64 (.mem .rcx 0x0) (.reg .rax), 0x60138),
  (0x60138, .jmp 0x60032, 0x6013D),
  (0x6013D, .mov 64 (.reg .rax) (.reg .r15), 0x60140),
  (0x60140, .add 64 (.reg .rsp) (.imm 0x78), 0x60144),
  (0x60144, .pop .r15, 0x60146),
  (0x60146, .pop .r14, 0x60148),
  (0x60148, .pop .r13, 0x6014A),
  (0x6014A, .pop .r12, 0x6014C),
  (0x6014C, .pop .rbp, 0x6014D),
  (0x6014D, .pop .rbx, 0x6014E),
  (0x6014E, .ret, 0x6014F)
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
@[ode_at] theorem at_6003B : prog 0x6003B = some (.jae 0x6013D, 0x60041) := rfl
@[ode_at] theorem at_60041 : prog 0x60041 = some (.mov 64 (.reg .rax) (.reg .r15), 0x60044) := rfl
@[ode_at] theorem at_60044 : prog 0x60044 = some (.mov 64 (.reg .rcx) (.imm 0x2), 0x6004B) := rfl
@[ode_at] theorem at_6004B : prog 0x6004B = some (.cmp 64 (.reg .rax) (.reg .rcx), 0x6004E) := rfl
@[ode_at] theorem at_6004E : prog 0x6004E = some (.jae 0x60054, 0x60050) := rfl
@[ode_at] theorem at_60052 : prog 0x60052 = some (.jmp 0x60054, 0x60054) := rfl
@[ode_at] theorem at_60054 : prog 0x60054 = some (.mov 64 (.reg .rax) (.reg .rbx), 0x60057) := rfl
@[ode_at] theorem at_60057 : prog 0x60057 = some (.add 64 (.reg .rax) (.imm 0x20), 0x6005B) := rfl
@[ode_at] theorem at_6005B : prog 0x6005B = some (.mov 64 (.reg .rcx) (.reg .r15), 0x6005E) := rfl
@[ode_at] theorem at_6005E : prog 0x6005E = some (.sub 64 (.reg .rcx) (.imm 0x2), 0x60062) := rfl
@[ode_at] theorem at_60062 : prog 0x60062 = some (.shl64 .rcx 5, 0x60066) := rfl
@[ode_at] theorem at_60066 : prog 0x60066 = some (.add 64 (.reg .rax) (.reg .rcx), 0x60069) := rfl
@[ode_at] theorem at_60069 : prog 0x60069 = some (.mov 64 (.mem .rsp 0x68) (.reg .rax), 0x6006E) := rfl
@[ode_at] theorem at_6006E : prog 0x6006E = some (.mov 64 (.reg .rax) (.mem .rsp 0x68), 0x60073) := rfl
@[ode_at] theorem at_60073 : prog 0x60073 = some (.lea .rcx .rsp 0x0, 0x60077) := rfl
@[ode_at] theorem at_60077 : prog 0x60077 = some (.movv false 0 (.m .rax 0x0), 0x6007A) := rfl
@[ode_at] theorem at_6007A : prog 0x6007A = some (.storev false .rcx 0x0 0, 0x6007D) := rfl
@[ode_at] theorem at_6007D : prog 0x6007D = some (.movv false 0 (.m .rax 0x10), 0x60081) := rfl
@[ode_at] theorem at_60081 : prog 0x60081 = some (.storev false .rcx 0x10 0, 0x60085) := rfl
@[ode_at] theorem at_60085 : prog 0x60085 = some (.mov 64 (.reg .rax) (.mem .rsp 0x68), 0x6008A) := rfl
@[ode_at] theorem at_6008A : prog 0x6008A = some (.add 64 (.reg .rax) (.imm 0x20), 0x6008E) := rfl
@[ode_at] theorem at_6008E : prog 0x6008E = some (.lea .rcx .rsp 0x0, 0x60092) := rfl
@[ode_at] theorem at_60092 : prog 0x60092 = some (.add 64 (.reg .rcx) (.imm 0x20), 0x60096) := rfl
@[ode_at] theorem at_60096 : prog 0x60096 = some (.movv false 0 (.m .rax 0x0), 0x60099) := rfl
@[ode_at] theorem at_60099 : prog 0x60099 = some (.storev false .rcx 0x0 0, 0x6009C) := rfl
@[ode_at] theorem at_6009C : prog 0x6009C = some (.movv false 0 (.m .rax 0x10), 0x600A0) := rfl
@[ode_at] theorem at_600A0 : prog 0x600A0 = some (.storev false .rcx 0x10 0, 0x600A4) := rfl
@[ode_at] theorem at_600A4 : prog 0x600A4 = some (.mov 64 (.reg .rax) (.reg .rbp), 0x600A7) := rfl
@[ode_at] theorem at_600A7 : prog 0x600A7 = some (.lea .rcx .rsp 0x40, 0x600AC) := rfl
@[ode_at] theorem at_600AC : prog 0x600AC = some (.movv false 0 (.m .rax 0x0), 0x600AF) := rfl
@[ode_at] theorem at_600AF : prog 0x600AF = some (.storev false .rcx 0x0 0, 0x600B2) := rfl
@[ode_at] theorem at_600B2 : prog 0x600B2 = some (.movv false 0 (.m .rax 0x10), 0x600B6) := rfl
@[ode_at] theorem at_600B6 : prog 0x600B6 = some (.storev false .rcx 0x10 0, 0x600BA) := rfl
@[ode_at] theorem at_600BA : prog 0x600BA = some (.mov 64 (.reg .rax) (.reg .r13), 0x600BD) := rfl
@[ode_at] theorem at_600BD : prog 0x600BD = some (.mov 64 (.reg .rcx) (.imm 0x5), 0x600C4) := rfl
@[ode_at] theorem at_600C4 : prog 0x600C4 = some (.cmp 64 (.reg .rax) (.reg .rcx), 0x600C7) := rfl
@[ode_at] theorem at_600C7 : prog 0x600C7 = some (.jne 0x600EC, 0x600C9) := rfl
@[ode_at] theorem at_600C9 : prog 0x600C9 = some (.lea .rdi .rsp 0x40, 0x600CE) := rfl
@[ode_at] theorem at_600CE : prog 0x600CE = some (.lea .rsi .rsp 0x0, 0x600D2) := rfl
@[ode_at] theorem at_600D2 : prog 0x600D2 = some (.mov 64 (.reg .rdx) (.imm 0x40), 0x600D9) := rfl
@[ode_at] theorem at_600D9 : prog 0x600D9 = some (.mov 64 (.reg .rcx) (.imm 0x0), 0x600E0) := rfl
@[ode_at] theorem at_600E0 : prog 0x600E0 = some (.mov 64 (.reg .r8) (.mem .rsp 0x60), 0x600E5) := rfl
@[ode_at] theorem at_600E5 : prog 0x600E5 = some (.call 0x30000, 0x600EA) := rfl
@[ode_at] theorem at_600EA : prog 0x600EA = some (.jmp 0x6010D, 0x600EC) := rfl
@[ode_at] theorem at_600EC : prog 0x600EC = some (.lea .rdi .rsp 0x40, 0x600F1) := rfl
@[ode_at] theorem at_600F1 : prog 0x600F1 = some (.lea .rsi .rsp 0x0, 0x600F5) := rfl
@[ode_at] theorem at_600F5 : prog 0x600F5 = some (.mov 64 (.reg .rdx) (.imm 0x40), 0x600FC) := rfl
@[ode_at] theorem at_600FC : prog 0x600FC = some (.mov 64 (.reg .rcx) (.imm 0x0), 0x60103) := rfl
@[ode_at] theorem at_60103 : prog 0x60103 = some (.mov 64 (.reg .r8) (.mem .rsp 0x60), 0x60108) := rfl
@[ode_at] theorem at_60108 : prog 0x60108 = some (.call 0x20000, 0x6010D) := rfl
@[ode_at] theorem at_6010D : prog 0x6010D = some (.lea .rax .rsp 0x40, 0x60112) := rfl
@[ode_at] theorem at_60112 : prog 0x60112 = some (.mov 64 (.reg .rcx) (.mem .rsp 0x68), 0x60117) := rfl
@[ode_at] theorem at_60117 : prog 0x60117 = some (.movv false 0 (.m .rax 0x0), 0x6011A) := rfl
@[ode_at] theorem at_6011A : prog 0x6011A = some (.storev false .rcx 0x0 0, 0x6011D) := rfl
@[ode_at] theorem at_6011D : prog 0x6011D = some (.movv false 0 (.m .rax 0x10), 0x60121) := rfl
@[ode_at] theorem at_60121 : prog 0x60121 = some (.storev false .rcx 0x10 0, 0x60125) := rfl
@[ode_at] theorem at_60125 : prog 0x60125 = some (.mov 64 (.reg .rax) (.reg .r15), 0x60128) := rfl
@[ode_at] theorem at_60128 : prog 0x60128 = some (.sub 64 (.reg .rax) (.imm 0x1), 0x6012C) := rfl
@[ode_at] theorem at_6012C : prog 0x6012C = some (.mov 64 (.reg .r15) (.reg .rax), 0x6012F) := rfl
@[ode_at] theorem at_6012F : prog 0x6012F = some (.mov 64 (.reg .rax) (.reg .r15), 0x60132) := rfl
@[ode_at] theorem at_60132 : prog 0x60132 = some (.mov 64 (.reg .rcx) (.reg .rbx), 0x60135) := rfl
@[ode_at] theorem at_60135 : prog 0x60135 = some (.mov 64 (.mem .rcx 0x0) (.reg .rax), 0x60138) := rfl
@[ode_at] theorem at_60138 : prog 0x60138 = some (.jmp 0x60032, 0x6013D) := rfl
@[ode_at] theorem at_6013D : prog 0x6013D = some (.mov 64 (.reg .rax) (.reg .r15), 0x60140) := rfl
@[ode_at] theorem at_60140 : prog 0x60140 = some (.add 64 (.reg .rsp) (.imm 0x78), 0x60144) := rfl
@[ode_at] theorem at_60144 : prog 0x60144 = some (.pop .r15, 0x60146) := rfl
@[ode_at] theorem at_60146 : prog 0x60146 = some (.pop .r14, 0x60148) := rfl
@[ode_at] theorem at_60148 : prog 0x60148 = some (.pop .r13, 0x6014A) := rfl
@[ode_at] theorem at_6014A : prog 0x6014A = some (.pop .r12, 0x6014C) := rfl
@[ode_at] theorem at_6014C : prog 0x6014C = some (.pop .rbp, 0x6014D) := rfl
@[ode_at] theorem at_6014D : prog 0x6014D = some (.pop .rbx, 0x6014E) := rfl
@[ode_at] theorem at_6014E : prog 0x6014E = some (.ret, 0x6014F) := rfl

end Code_merge
