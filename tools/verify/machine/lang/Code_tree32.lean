import Machine
import KCode
import Cells
import Code_fillp
open X86

/-! `tree32` as assembled: 85 instructions. Written from the lifter's rows. -/

set_option maxRecDepth 100000
namespace Code_tree32

def table : List (Nat × Instr × Nat) := [
  (0x120000, .push .rbx, 0x120001),
  (0x120001, .push .rbp, 0x120002),
  (0x120002, .push .r12, 0x120004),
  (0x120004, .push .r13, 0x120006),
  (0x120006, .push .r14, 0x120008),
  (0x120008, .sub 64 (.reg .rsp) (.imm 0x500), 0x12000F),
  (0x12000F, .mov 64 (.reg .rbx) (.reg .rdi), 0x120012),
  (0x120012, .mov 64 (.reg .rbp) (.reg .rsi), 0x120015),
  (0x120015, .mov 64 (.reg .r12) (.reg .rdx), 0x120018),
  (0x120018, .mov 64 (.reg .r13) (.reg .rcx), 0x12001B),
  (0x12001B, .mov 64 (.reg .rax) (.reg .r13), 0x12001E),
  (0x12001E, .or 64 (.reg .rax) (.imm 0x40000004), 0x120024),
  (0x120024, .mov 64 (.reg .r14) (.reg .rax), 0x120027),
  (0x120027, .lea .rdi .rsp 0x0, 0x12002B),
  (0x12002B, .mov 64 (.reg .rsi) (.reg .rbp), 0x12002E),
  (0x12002E, .mov 64 (.reg .rdx) (.imm 0x10), 0x120035),
  (0x120035, .mov 64 (.reg .rcx) (.imm 0x40), 0x12003C),
  (0x12003C, .call 0x110000, 0x120041),
  (0x120041, .lea .rdi .rsp 0x0, 0x120045),
  (0x120045, .mov 64 (.reg .rsi) (.imm 0x1), 0x12004C),
  (0x12004C, .mov 64 (.reg .rdx) (.reg .r12), 0x12004F),
  (0x12004F, .mov 64 (.reg .rcx) (.imm 0x0), 0x120056),
  (0x120056, .mov 64 (.reg .r8) (.reg .r14), 0x120059),
  (0x120059, .lea .r9 .rsp 0x100, 0x120061),
  (0x120061, .call 0x18000, 0x120066),
  (0x120066, .lea .rdi .rsp 0x0, 0x12006A),
  (0x12006A, .lea .rsi .rsp 0x100, 0x120072),
  (0x120072, .mov 64 (.reg .rdx) (.imm 0x8), 0x120079),
  (0x120079, .mov 64 (.reg .rcx) (.imm 0x40), 0x120080),
  (0x120080, .call 0x110000, 0x120085),
  (0x120085, .lea .rdi .rsp 0x0, 0x120089),
  (0x120089, .mov 64 (.reg .rsi) (.imm 0x1), 0x120090),
  (0x120090, .mov 64 (.reg .rdx) (.reg .r12), 0x120093),
  (0x120093, .mov 64 (.reg .rcx) (.imm 0x0), 0x12009A),
  (0x12009A, .mov 64 (.reg .r8) (.reg .r14), 0x12009D),
  (0x12009D, .lea .r9 .rsp 0x300, 0x1200A5),
  (0x1200A5, .call 0x18000, 0x1200AA),
  (0x1200AA, .lea .rdi .rsp 0x0, 0x1200AE),
  (0x1200AE, .lea .rsi .rsp 0x300, 0x1200B6),
  (0x1200B6, .mov 64 (.reg .rdx) (.imm 0x4), 0x1200BD),
  (0x1200BD, .mov 64 (.reg .rcx) (.imm 0x40), 0x1200C4),
  (0x1200C4, .call 0x110000, 0x1200C9),
  (0x1200C9, .lea .rdi .rsp 0x0, 0x1200CD),
  (0x1200CD, .mov 64 (.reg .rsi) (.imm 0x1), 0x1200D4),
  (0x1200D4, .mov 64 (.reg .rdx) (.reg .r12), 0x1200D7),
  (0x1200D7, .mov 64 (.reg .rcx) (.imm 0x0), 0x1200DE),
  (0x1200DE, .mov 64 (.reg .r8) (.reg .r14), 0x1200E1),
  (0x1200E1, .lea .r9 .rsp 0x100, 0x1200E9),
  (0x1200E9, .call 0x18000, 0x1200EE),
  (0x1200EE, .lea .rdi .rsp 0x0, 0x1200F2),
  (0x1200F2, .lea .rsi .rsp 0x100, 0x1200FA),
  (0x1200FA, .mov 64 (.reg .rdx) (.imm 0x2), 0x120101),
  (0x120101, .mov 64 (.reg .rcx) (.imm 0x40), 0x120108),
  (0x120108, .call 0x110000, 0x12010D),
  (0x12010D, .lea .rdi .rsp 0x0, 0x120111),
  (0x120111, .mov 64 (.reg .rsi) (.imm 0x1), 0x120118),
  (0x120118, .mov 64 (.reg .rdx) (.reg .r12), 0x12011B),
  (0x12011B, .mov 64 (.reg .rcx) (.imm 0x0), 0x120122),
  (0x120122, .mov 64 (.reg .r8) (.reg .r14), 0x120125),
  (0x120125, .lea .r9 .rsp 0x300, 0x12012D),
  (0x12012D, .call 0x18000, 0x120132),
  (0x120132, .lea .rdi .rsp 0x0, 0x120136),
  (0x120136, .lea .rsi .rsp 0x300, 0x12013E),
  (0x12013E, .mov 64 (.reg .rdx) (.imm 0x1), 0x120145),
  (0x120145, .mov 64 (.reg .rcx) (.imm 0x40), 0x12014C),
  (0x12014C, .call 0x110000, 0x120151),
  (0x120151, .lea .rdi .rsp 0x0, 0x120155),
  (0x120155, .mov 64 (.reg .rsi) (.imm 0x1), 0x12015C),
  (0x12015C, .mov 64 (.reg .rdx) (.reg .r12), 0x12015F),
  (0x12015F, .mov 64 (.reg .rcx) (.imm 0x0), 0x120166),
  (0x120166, .mov 64 (.reg .r8) (.reg .r14), 0x120169),
  (0x120169, .mov 64 (.reg .r9) (.reg .rbx), 0x12016C),
  (0x12016C, .call 0x18000, 0x120171),
  (0x120171, .add 64 (.reg .rsp) (.imm 0x500), 0x120178),
  (0x120178, .pop .r14, 0x12017A),
  (0x12017A, .pop .r13, 0x12017C),
  (0x12017C, .pop .r12, 0x12017E),
  (0x12017E, .pop .rbp, 0x12017F),
  (0x12017F, .pop .rbx, 0x120180),
  (0x120180, .ret, 0x120181),
  (0x120190, .cmp 64 (.reg .rcx) (.imm 0x100), 0x120197),
  (0x120197, .jae 0x12019E, 0x120199),
  (0x120199, .jmp 0x120000, 0x12019E),
  (0x12019E, .mov 64 (.reg .rax) (.imm 0xFFFFFFFFFFFFFFFF), 0x1201A5),
  (0x1201A5, .ret, 0x1201A6)
]

def pre0 : List (Nat × Instr × Nat) := KCode.table
def pre1 : List (Nat × Instr × Nat) := pre0 ++ Code_fillp.table

/-- Every instruction of the program: the two kernels' (one/KCode.lean), `fillp`'s, then this function's. -/
def whole : List (Nat × Instr × Nat) := pre1 ++ table

def prog (ext : Nat → Option (Instr × Nat)) (pc : Nat) : Option (Instr × Nat) := (whole.lookup pc).or (ext pc)

/-- What this table holds, the program holds, whatever else it holds. -/
theorem prog_of (ext : Nat → Option (Instr × Nat)) : ∀ pc x, whole.lookup pc = some x → prog ext pc = some x := by
  intro pc x h; simp only [prog, h, Option.some_or]

theorem has_kernels (ext : Nat → Option (Instr × Nat)) : ∀ pc x, KCode.prog pc = some x → prog ext pc = some x := by
  intro pc x h
  exact prog_of ext pc x (lookup_append_left pre1 table pc x (lookup_append_left pre0 Code_fillp.table pc x (h)))

/-- `fillp`'s own instructions are in this program: no table before them has one at any of their addresses. -/
theorem in1 (ext : Nat → Option (Instr × Nat)) : ∀ pc x, Code_fillp.table.lookup pc = some x → prog ext pc = some x := by
  intro pc x h
  have apart : ∀ p ∈ Code_fillp.table.map (·.1), ((pre0.lookup p).isNone) = true := by decide +kernel
  have none := Option.isNone_iff_eq_none.mp (apart pc (lookup_mem_keys _ pc x h))
  have here : pre1.lookup pc = some x := by
    show (pre0 ++ Code_fillp.table).lookup pc = some x
    rw [lookup_append_or, none]; exact h
  exact prog_of ext pc x (lookup_append_left pre1 table pc x (here))

/-- The tables of `fillp`'s program (its own instructions and those of what it calls) are in this one, unchanged. -/
theorem tables_fillp (ext : Nat → Option (Instr × Nat)) : ∀ pc x, (Code_fillp.table).lookup pc = some x → prog ext pc = some x := by
  intro pc x h'
  exact in1 ext pc x h'

/-- `fillp`'s program (its own instructions and those of what it calls) is part of this one, unchanged. -/
theorem has_fillp (ext : Nat → Option (Instr × Nat)) : ∀ pc x, Code_fillp.prog pc = some x → prog ext pc = some x :=
  fun pc x h => tables_fillp ext pc x h

@[ode_at] theorem at_120000 (ext : Nat → Option (Instr × Nat)) : prog ext 0x120000 = some (.push .rbx, 0x120001) := rfl
@[ode_at] theorem at_120001 (ext : Nat → Option (Instr × Nat)) : prog ext 0x120001 = some (.push .rbp, 0x120002) := rfl
@[ode_at] theorem at_120002 (ext : Nat → Option (Instr × Nat)) : prog ext 0x120002 = some (.push .r12, 0x120004) := rfl
@[ode_at] theorem at_120004 (ext : Nat → Option (Instr × Nat)) : prog ext 0x120004 = some (.push .r13, 0x120006) := rfl
@[ode_at] theorem at_120006 (ext : Nat → Option (Instr × Nat)) : prog ext 0x120006 = some (.push .r14, 0x120008) := rfl
@[ode_at] theorem at_120008 (ext : Nat → Option (Instr × Nat)) : prog ext 0x120008 = some (.sub 64 (.reg .rsp) (.imm 0x500), 0x12000F) := rfl
@[ode_at] theorem at_12000F (ext : Nat → Option (Instr × Nat)) : prog ext 0x12000F = some (.mov 64 (.reg .rbx) (.reg .rdi), 0x120012) := rfl
@[ode_at] theorem at_120012 (ext : Nat → Option (Instr × Nat)) : prog ext 0x120012 = some (.mov 64 (.reg .rbp) (.reg .rsi), 0x120015) := rfl
@[ode_at] theorem at_120015 (ext : Nat → Option (Instr × Nat)) : prog ext 0x120015 = some (.mov 64 (.reg .r12) (.reg .rdx), 0x120018) := rfl
@[ode_at] theorem at_120018 (ext : Nat → Option (Instr × Nat)) : prog ext 0x120018 = some (.mov 64 (.reg .r13) (.reg .rcx), 0x12001B) := rfl
@[ode_at] theorem at_12001B (ext : Nat → Option (Instr × Nat)) : prog ext 0x12001B = some (.mov 64 (.reg .rax) (.reg .r13), 0x12001E) := rfl
@[ode_at] theorem at_12001E (ext : Nat → Option (Instr × Nat)) : prog ext 0x12001E = some (.or 64 (.reg .rax) (.imm 0x40000004), 0x120024) := rfl
@[ode_at] theorem at_120024 (ext : Nat → Option (Instr × Nat)) : prog ext 0x120024 = some (.mov 64 (.reg .r14) (.reg .rax), 0x120027) := rfl
@[ode_at] theorem at_120027 (ext : Nat → Option (Instr × Nat)) : prog ext 0x120027 = some (.lea .rdi .rsp 0x0, 0x12002B) := rfl
@[ode_at] theorem at_12002B (ext : Nat → Option (Instr × Nat)) : prog ext 0x12002B = some (.mov 64 (.reg .rsi) (.reg .rbp), 0x12002E) := rfl
@[ode_at] theorem at_12002E (ext : Nat → Option (Instr × Nat)) : prog ext 0x12002E = some (.mov 64 (.reg .rdx) (.imm 0x10), 0x120035) := rfl
@[ode_at] theorem at_120035 (ext : Nat → Option (Instr × Nat)) : prog ext 0x120035 = some (.mov 64 (.reg .rcx) (.imm 0x40), 0x12003C) := rfl
@[ode_at] theorem at_12003C (ext : Nat → Option (Instr × Nat)) : prog ext 0x12003C = some (.call 0x110000, 0x120041) := rfl
@[ode_at] theorem at_120041 (ext : Nat → Option (Instr × Nat)) : prog ext 0x120041 = some (.lea .rdi .rsp 0x0, 0x120045) := rfl
@[ode_at] theorem at_120045 (ext : Nat → Option (Instr × Nat)) : prog ext 0x120045 = some (.mov 64 (.reg .rsi) (.imm 0x1), 0x12004C) := rfl
@[ode_at] theorem at_12004C (ext : Nat → Option (Instr × Nat)) : prog ext 0x12004C = some (.mov 64 (.reg .rdx) (.reg .r12), 0x12004F) := rfl
@[ode_at] theorem at_12004F (ext : Nat → Option (Instr × Nat)) : prog ext 0x12004F = some (.mov 64 (.reg .rcx) (.imm 0x0), 0x120056) := rfl
@[ode_at] theorem at_120056 (ext : Nat → Option (Instr × Nat)) : prog ext 0x120056 = some (.mov 64 (.reg .r8) (.reg .r14), 0x120059) := rfl
@[ode_at] theorem at_120059 (ext : Nat → Option (Instr × Nat)) : prog ext 0x120059 = some (.lea .r9 .rsp 0x100, 0x120061) := rfl
@[ode_at] theorem at_120061 (ext : Nat → Option (Instr × Nat)) : prog ext 0x120061 = some (.call 0x18000, 0x120066) := rfl
@[ode_at] theorem at_120066 (ext : Nat → Option (Instr × Nat)) : prog ext 0x120066 = some (.lea .rdi .rsp 0x0, 0x12006A) := rfl
@[ode_at] theorem at_12006A (ext : Nat → Option (Instr × Nat)) : prog ext 0x12006A = some (.lea .rsi .rsp 0x100, 0x120072) := rfl
@[ode_at] theorem at_120072 (ext : Nat → Option (Instr × Nat)) : prog ext 0x120072 = some (.mov 64 (.reg .rdx) (.imm 0x8), 0x120079) := rfl
@[ode_at] theorem at_120079 (ext : Nat → Option (Instr × Nat)) : prog ext 0x120079 = some (.mov 64 (.reg .rcx) (.imm 0x40), 0x120080) := rfl
@[ode_at] theorem at_120080 (ext : Nat → Option (Instr × Nat)) : prog ext 0x120080 = some (.call 0x110000, 0x120085) := rfl
@[ode_at] theorem at_120085 (ext : Nat → Option (Instr × Nat)) : prog ext 0x120085 = some (.lea .rdi .rsp 0x0, 0x120089) := rfl
@[ode_at] theorem at_120089 (ext : Nat → Option (Instr × Nat)) : prog ext 0x120089 = some (.mov 64 (.reg .rsi) (.imm 0x1), 0x120090) := rfl
@[ode_at] theorem at_120090 (ext : Nat → Option (Instr × Nat)) : prog ext 0x120090 = some (.mov 64 (.reg .rdx) (.reg .r12), 0x120093) := rfl
@[ode_at] theorem at_120093 (ext : Nat → Option (Instr × Nat)) : prog ext 0x120093 = some (.mov 64 (.reg .rcx) (.imm 0x0), 0x12009A) := rfl
@[ode_at] theorem at_12009A (ext : Nat → Option (Instr × Nat)) : prog ext 0x12009A = some (.mov 64 (.reg .r8) (.reg .r14), 0x12009D) := rfl
@[ode_at] theorem at_12009D (ext : Nat → Option (Instr × Nat)) : prog ext 0x12009D = some (.lea .r9 .rsp 0x300, 0x1200A5) := rfl
@[ode_at] theorem at_1200A5 (ext : Nat → Option (Instr × Nat)) : prog ext 0x1200A5 = some (.call 0x18000, 0x1200AA) := rfl
@[ode_at] theorem at_1200AA (ext : Nat → Option (Instr × Nat)) : prog ext 0x1200AA = some (.lea .rdi .rsp 0x0, 0x1200AE) := rfl
@[ode_at] theorem at_1200AE (ext : Nat → Option (Instr × Nat)) : prog ext 0x1200AE = some (.lea .rsi .rsp 0x300, 0x1200B6) := rfl
@[ode_at] theorem at_1200B6 (ext : Nat → Option (Instr × Nat)) : prog ext 0x1200B6 = some (.mov 64 (.reg .rdx) (.imm 0x4), 0x1200BD) := rfl
@[ode_at] theorem at_1200BD (ext : Nat → Option (Instr × Nat)) : prog ext 0x1200BD = some (.mov 64 (.reg .rcx) (.imm 0x40), 0x1200C4) := rfl
@[ode_at] theorem at_1200C4 (ext : Nat → Option (Instr × Nat)) : prog ext 0x1200C4 = some (.call 0x110000, 0x1200C9) := rfl
@[ode_at] theorem at_1200C9 (ext : Nat → Option (Instr × Nat)) : prog ext 0x1200C9 = some (.lea .rdi .rsp 0x0, 0x1200CD) := rfl
@[ode_at] theorem at_1200CD (ext : Nat → Option (Instr × Nat)) : prog ext 0x1200CD = some (.mov 64 (.reg .rsi) (.imm 0x1), 0x1200D4) := rfl
@[ode_at] theorem at_1200D4 (ext : Nat → Option (Instr × Nat)) : prog ext 0x1200D4 = some (.mov 64 (.reg .rdx) (.reg .r12), 0x1200D7) := rfl
@[ode_at] theorem at_1200D7 (ext : Nat → Option (Instr × Nat)) : prog ext 0x1200D7 = some (.mov 64 (.reg .rcx) (.imm 0x0), 0x1200DE) := rfl
@[ode_at] theorem at_1200DE (ext : Nat → Option (Instr × Nat)) : prog ext 0x1200DE = some (.mov 64 (.reg .r8) (.reg .r14), 0x1200E1) := rfl
@[ode_at] theorem at_1200E1 (ext : Nat → Option (Instr × Nat)) : prog ext 0x1200E1 = some (.lea .r9 .rsp 0x100, 0x1200E9) := rfl
@[ode_at] theorem at_1200E9 (ext : Nat → Option (Instr × Nat)) : prog ext 0x1200E9 = some (.call 0x18000, 0x1200EE) := rfl
@[ode_at] theorem at_1200EE (ext : Nat → Option (Instr × Nat)) : prog ext 0x1200EE = some (.lea .rdi .rsp 0x0, 0x1200F2) := rfl
@[ode_at] theorem at_1200F2 (ext : Nat → Option (Instr × Nat)) : prog ext 0x1200F2 = some (.lea .rsi .rsp 0x100, 0x1200FA) := rfl
@[ode_at] theorem at_1200FA (ext : Nat → Option (Instr × Nat)) : prog ext 0x1200FA = some (.mov 64 (.reg .rdx) (.imm 0x2), 0x120101) := rfl
@[ode_at] theorem at_120101 (ext : Nat → Option (Instr × Nat)) : prog ext 0x120101 = some (.mov 64 (.reg .rcx) (.imm 0x40), 0x120108) := rfl
@[ode_at] theorem at_120108 (ext : Nat → Option (Instr × Nat)) : prog ext 0x120108 = some (.call 0x110000, 0x12010D) := rfl
@[ode_at] theorem at_12010D (ext : Nat → Option (Instr × Nat)) : prog ext 0x12010D = some (.lea .rdi .rsp 0x0, 0x120111) := rfl
@[ode_at] theorem at_120111 (ext : Nat → Option (Instr × Nat)) : prog ext 0x120111 = some (.mov 64 (.reg .rsi) (.imm 0x1), 0x120118) := rfl
@[ode_at] theorem at_120118 (ext : Nat → Option (Instr × Nat)) : prog ext 0x120118 = some (.mov 64 (.reg .rdx) (.reg .r12), 0x12011B) := rfl
@[ode_at] theorem at_12011B (ext : Nat → Option (Instr × Nat)) : prog ext 0x12011B = some (.mov 64 (.reg .rcx) (.imm 0x0), 0x120122) := rfl
@[ode_at] theorem at_120122 (ext : Nat → Option (Instr × Nat)) : prog ext 0x120122 = some (.mov 64 (.reg .r8) (.reg .r14), 0x120125) := rfl
@[ode_at] theorem at_120125 (ext : Nat → Option (Instr × Nat)) : prog ext 0x120125 = some (.lea .r9 .rsp 0x300, 0x12012D) := rfl
@[ode_at] theorem at_12012D (ext : Nat → Option (Instr × Nat)) : prog ext 0x12012D = some (.call 0x18000, 0x120132) := rfl
@[ode_at] theorem at_120132 (ext : Nat → Option (Instr × Nat)) : prog ext 0x120132 = some (.lea .rdi .rsp 0x0, 0x120136) := rfl
@[ode_at] theorem at_120136 (ext : Nat → Option (Instr × Nat)) : prog ext 0x120136 = some (.lea .rsi .rsp 0x300, 0x12013E) := rfl
@[ode_at] theorem at_12013E (ext : Nat → Option (Instr × Nat)) : prog ext 0x12013E = some (.mov 64 (.reg .rdx) (.imm 0x1), 0x120145) := rfl
@[ode_at] theorem at_120145 (ext : Nat → Option (Instr × Nat)) : prog ext 0x120145 = some (.mov 64 (.reg .rcx) (.imm 0x40), 0x12014C) := rfl
@[ode_at] theorem at_12014C (ext : Nat → Option (Instr × Nat)) : prog ext 0x12014C = some (.call 0x110000, 0x120151) := rfl
@[ode_at] theorem at_120151 (ext : Nat → Option (Instr × Nat)) : prog ext 0x120151 = some (.lea .rdi .rsp 0x0, 0x120155) := rfl
@[ode_at] theorem at_120155 (ext : Nat → Option (Instr × Nat)) : prog ext 0x120155 = some (.mov 64 (.reg .rsi) (.imm 0x1), 0x12015C) := rfl
@[ode_at] theorem at_12015C (ext : Nat → Option (Instr × Nat)) : prog ext 0x12015C = some (.mov 64 (.reg .rdx) (.reg .r12), 0x12015F) := rfl
@[ode_at] theorem at_12015F (ext : Nat → Option (Instr × Nat)) : prog ext 0x12015F = some (.mov 64 (.reg .rcx) (.imm 0x0), 0x120166) := rfl
@[ode_at] theorem at_120166 (ext : Nat → Option (Instr × Nat)) : prog ext 0x120166 = some (.mov 64 (.reg .r8) (.reg .r14), 0x120169) := rfl
@[ode_at] theorem at_120169 (ext : Nat → Option (Instr × Nat)) : prog ext 0x120169 = some (.mov 64 (.reg .r9) (.reg .rbx), 0x12016C) := rfl
@[ode_at] theorem at_12016C (ext : Nat → Option (Instr × Nat)) : prog ext 0x12016C = some (.call 0x18000, 0x120171) := rfl
@[ode_at] theorem at_120171 (ext : Nat → Option (Instr × Nat)) : prog ext 0x120171 = some (.add 64 (.reg .rsp) (.imm 0x500), 0x120178) := rfl
@[ode_at] theorem at_120178 (ext : Nat → Option (Instr × Nat)) : prog ext 0x120178 = some (.pop .r14, 0x12017A) := rfl
@[ode_at] theorem at_12017A (ext : Nat → Option (Instr × Nat)) : prog ext 0x12017A = some (.pop .r13, 0x12017C) := rfl
@[ode_at] theorem at_12017C (ext : Nat → Option (Instr × Nat)) : prog ext 0x12017C = some (.pop .r12, 0x12017E) := rfl
@[ode_at] theorem at_12017E (ext : Nat → Option (Instr × Nat)) : prog ext 0x12017E = some (.pop .rbp, 0x12017F) := rfl
@[ode_at] theorem at_12017F (ext : Nat → Option (Instr × Nat)) : prog ext 0x12017F = some (.pop .rbx, 0x120180) := rfl
@[ode_at] theorem at_120180 (ext : Nat → Option (Instr × Nat)) : prog ext 0x120180 = some (.ret, 0x120181) := rfl
@[ode_at] theorem at_120190 (ext : Nat → Option (Instr × Nat)) : prog ext 0x120190 = some (.cmp 64 (.reg .rcx) (.imm 0x100), 0x120197) := rfl
@[ode_at] theorem at_120197 (ext : Nat → Option (Instr × Nat)) : prog ext 0x120197 = some (.jae 0x12019E, 0x120199) := rfl
@[ode_at] theorem at_120199 (ext : Nat → Option (Instr × Nat)) : prog ext 0x120199 = some (.jmp 0x120000, 0x12019E) := rfl
@[ode_at] theorem at_12019E (ext : Nat → Option (Instr × Nat)) : prog ext 0x12019E = some (.mov 64 (.reg .rax) (.imm 0xFFFFFFFFFFFFFFFF), 0x1201A5) := rfl
@[ode_at] theorem at_1201A5 (ext : Nat → Option (Instr × Nat)) : prog ext 0x1201A5 = some (.ret, 0x1201A6) := rfl

end Code_tree32
