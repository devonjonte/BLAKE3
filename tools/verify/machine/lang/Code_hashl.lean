import Machine
import KCode
import Cells
import Code_pad
import Code_chunk_node
import Code_node_out
import Code_ladd
import Code_lroot
open X86

/-! `hashl` as assembled: 108 instructions. Written from the lifter's rows. -/

set_option maxRecDepth 100000
namespace Code_hashl

def table : List (Nat × Instr × Nat) := [
  (0x40000, .push .rbx, 0x40001),
  (0x40001, .push .rbp, 0x40002),
  (0x40002, .push .r12, 0x40004),
  (0x40004, .push .r13, 0x40006),
  (0x40006, .push .r14, 0x40008),
  (0x40008, .push .r15, 0x4000A),
  (0x4000A, .sub 64 (.reg .rsp) (.imm 0xE78), 0x40011),
  (0x40011, .mov 64 (.mem .rsp 0xE60) (.reg .rdi), 0x40019),
  (0x40019, .mov 64 (.mem .rsp 0xE68) (.reg .rsi), 0x40021),
  (0x40021, .mov 64 (.mem .rsp 0xE70) (.reg .rdx), 0x40029),
  (0x40029, .mov 64 (.reg .r13) (.reg .rcx), 0x4002C),
  (0x4002C, .mov 64 (.reg .r14) (.reg .r8), 0x4002F),
  (0x4002F, .mov 64 (.reg .r15) (.reg .r9), 0x40032),
  (0x40032, .mov 64 (.reg .rax) (.imm 0x0), 0x40039),
  (0x40039, .lea .rcx .rsp 0x0, 0x4003D),
  (0x4003D, .mov 64 (.mem .rcx 0x0) (.reg .rax), 0x40040),
  (0x40040, .mov 64 (.reg .rax) (.mem .rsp 0xE68), 0x40048),
  (0x40048, .mov 64 (.reg .rbx) (.reg .rax), 0x4004B),
  (0x4004B, .mov 64 (.reg .rax) (.mem .rsp 0xE70), 0x40053),
  (0x40053, .mov 64 (.reg .rbp) (.reg .rax), 0x40056),
  (0x40056, .mov 64 (.reg .rax) (.imm 0x0), 0x4005D),
  (0x4005D, .mov 64 (.reg .r12) (.reg .rax), 0x40060),
  (0x40060, .mov 64 (.reg .rax) (.imm 0x400), 0x40067),
  (0x40067, .mov 64 (.reg .rcx) (.reg .rbp), 0x4006A),
  (0x4006A, .cmp 64 (.reg .rax) (.reg .rcx), 0x4006D),
  (0x4006D, .jae 0x4010C, 0x40073),
  (0x40073, .mov 64 (.reg .rax) (.reg .r13), 0x40076),
  (0x40076, .lea .rcx .rsp 0xDC0, 0x4007E),
  (0x4007E, .movv false 0 (.m .rax 0x0), 0x40081),
  (0x40081, .storev false .rcx 0x0 0, 0x40084),
  (0x40084, .movv false 0 (.m .rax 0x10), 0x40088),
  (0x40088, .storev false .rcx 0x10 0, 0x4008C),
  (0x4008C, .lea .rdi .rsp 0xDC0, 0x40094),
  (0x40094, .mov 64 (.reg .rsi) (.reg .rbx), 0x40097),
  (0x40097, .mov 64 (.reg .rdx) (.imm 0x400), 0x4009E),
  (0x4009E, .mov 64 (.reg .rcx) (.reg .r12), 0x400A1),
  (0x400A1, .mov 64 (.reg .r8) (.reg .r14), 0x400A4),
  (0x400A4, .mov 64 (.reg .r9) (.reg .r15), 0x400A7),
  (0x400A7, .call 0xF0000, 0x400AC),
  (0x400AC, .lea .rdi .rsp 0xE40, 0x400B4),
  (0x400B4, .lea .rsi .rsp 0xDC0, 0x400BC),
  (0x400BC, .mov 64 (.reg .rdx) (.imm 0x0), 0x400C3),
  (0x400C3, .mov 64 (.reg .rcx) (.reg .r15), 0x400C6),
  (0x400C6, .call 0xD0000, 0x400CB),
  (0x400CB, .lea .rdi .rsp 0x0, 0x400CF),
  (0x400CF, .mov 64 (.reg .rsi) (.reg .r13), 0x400D2),
  (0x400D2, .mov 64 (.reg .rdx) (.reg .r14), 0x400D5),
  (0x400D5, .mov 64 (.reg .rcx) (.reg .r15), 0x400D8),
  (0x400D8, .lea .r8 .rsp 0xE40, 0x400E0),
  (0x400E0, .call 0xB0000, 0x400E5),
  (0x400E5, .mov 64 (.reg .rax) (.reg .rbx), 0x400E8),
  (0x400E8, .add 64 (.reg .rax) (.imm 0x400), 0x400EE),
  (0x400EE, .mov 64 (.reg .rbx) (.reg .rax), 0x400F1),
  (0x400F1, .mov 64 (.reg .rax) (.reg .rbp), 0x400F4),
  (0x400F4, .sub 64 (.reg .rax) (.imm 0x400), 0x400FA),
  (0x400FA, .mov 64 (.reg .rbp) (.reg .rax), 0x400FD),
  (0x400FD, .mov 64 (.reg .rax) (.reg .r12), 0x40100),
  (0x40100, .add 64 (.reg .rax) (.imm 0x1), 0x40104),
  (0x40104, .mov 64 (.reg .r12) (.reg .rax), 0x40107),
  (0x40107, .jmp 0x40060, 0x4010C),
  (0x4010C, .mov 64 (.reg .rax) (.reg .r13), 0x4010F),
  (0x4010F, .lea .rcx .rsp 0xDC0, 0x40117),
  (0x40117, .movv false 0 (.m .rax 0x0), 0x4011A),
  (0x4011A, .storev false .rcx 0x0 0, 0x4011D),
  (0x4011D, .movv false 0 (.m .rax 0x10), 0x40121),
  (0x40121, .storev false .rcx 0x10 0, 0x40125),
  (0x40125, .lea .rdi .rsp 0xDC0, 0x4012D),
  (0x4012D, .mov 64 (.reg .rsi) (.reg .rbx), 0x40130),
  (0x40130, .mov 64 (.reg .rdx) (.reg .rbp), 0x40133),
  (0x40133, .mov 64 (.reg .rcx) (.reg .r12), 0x40136),
  (0x40136, .mov 64 (.reg .r8) (.reg .r14), 0x40139),
  (0x40139, .mov 64 (.reg .r9) (.reg .r15), 0x4013C),
  (0x4013C, .call 0xF0000, 0x40141),
  (0x40141, .mov 64 (.reg .rax) (.reg .r12), 0x40144),
  (0x40144, .mov 64 (.reg .rcx) (.imm 0x0), 0x4014B),
  (0x4014B, .cmp 64 (.reg .rax) (.reg .rcx), 0x4014E),
  (0x4014E, .jne 0x40171, 0x40150),
  (0x40150, .mov 64 (.reg .rdi) (.mem .rsp 0xE60), 0x40158),
  (0x40158, .lea .rsi .rsp 0xDC0, 0x40160),
  (0x40160, .mov 64 (.reg .rdx) (.imm 0x8), 0x40167),
  (0x40167, .mov 64 (.reg .rcx) (.reg .r15), 0x4016A),
  (0x4016A, .call 0xD0000, 0x4016F),
  (0x4016F, .jmp 0x401C4, 0x40171),
  (0x40171, .lea .rdi .rsp 0xE40, 0x40179),
  (0x40179, .lea .rsi .rsp 0xDC0, 0x40181),
  (0x40181, .mov 64 (.reg .rdx) (.imm 0x0), 0x40188),
  (0x40188, .mov 64 (.reg .rcx) (.reg .r15), 0x4018B),
  (0x4018B, .call 0xD0000, 0x40190),
  (0x40190, .lea .rdi .rsp 0x0, 0x40194),
  (0x40194, .mov 64 (.reg .rsi) (.reg .r13), 0x40197),
  (0x40197, .mov 64 (.reg .rdx) (.reg .r14), 0x4019A),
  (0x4019A, .mov 64 (.reg .rcx) (.reg .r15), 0x4019D),
  (0x4019D, .lea .r8 .rsp 0xE40, 0x401A5),
  (0x401A5, .call 0xB0000, 0x401AA),
  (0x401AA, .mov 64 (.reg .rdi) (.mem .rsp 0xE60), 0x401B2),
  (0x401B2, .lea .rsi .rsp 0x0, 0x401B6),
  (0x401B6, .mov 64 (.reg .rdx) (.reg .r13), 0x401B9),
  (0x401B9, .mov 64 (.reg .rcx) (.reg .r14), 0x401BC),
  (0x401BC, .mov 64 (.reg .r8) (.reg .r15), 0x401BF),
  (0x401BF, .call 0xC0000, 0x401C4),
  (0x401C4, .add 64 (.reg .rsp) (.imm 0xE78), 0x401CB),
  (0x401CB, .pop .r15, 0x401CD),
  (0x401CD, .pop .r14, 0x401CF),
  (0x401CF, .pop .r13, 0x401D1),
  (0x401D1, .pop .r12, 0x401D3),
  (0x401D3, .pop .rbp, 0x401D4),
  (0x401D4, .pop .rbx, 0x401D5),
  (0x401D5, .ret, 0x401D6)
]

def pre0 : List (Nat × Instr × Nat) := KCode.table
def pre1 : List (Nat × Instr × Nat) := pre0 ++ Code_pad.table
def pre2 : List (Nat × Instr × Nat) := pre1 ++ Code_chunk_node.table
def pre3 : List (Nat × Instr × Nat) := pre2 ++ Code_node_out.table
def pre4 : List (Nat × Instr × Nat) := pre3 ++ Code_ladd.table
def pre5 : List (Nat × Instr × Nat) := pre4 ++ Code_lroot.table

/-- Every instruction of the program: the two kernels' (one/KCode.lean), `pad`'s, `chunk_node`'s, `node_out`'s, `ladd`'s, `lroot`'s, then this function's. -/
def whole : List (Nat × Instr × Nat) := pre5 ++ table

def prog (pc : Nat) : Option (Instr × Nat) := whole.lookup pc

/-- The addresses the program has an instruction at. -/
def keys : List Nat := whole.map (·.1)

theorem keys_of : ∀ pc x, prog pc = some x → pc ∈ keys := fun pc x h => lookup_mem_keys whole pc x h

theorem has_kernels : ∀ pc x, KCode.prog pc = some x → prog pc = some x := by
  intro pc x h
  exact lookup_append_left pre5 table pc x (lookup_append_left pre4 Code_lroot.table pc x (lookup_append_left pre3 Code_ladd.table pc x (lookup_append_left pre2 Code_node_out.table pc x (lookup_append_left pre1 Code_chunk_node.table pc x (lookup_append_left pre0 Code_pad.table pc x (h))))))

/-- `pad`'s own instructions are in this program: no table before them has one at any of their addresses. -/
theorem in1 : ∀ pc x, Code_pad.table.lookup pc = some x → prog pc = some x := by
  intro pc x h
  have apart : ∀ p ∈ Code_pad.table.map (·.1), ((pre0.lookup p).isNone) = true := by decide +kernel
  have none := Option.isNone_iff_eq_none.mp (apart pc (lookup_mem_keys _ pc x h))
  have here : pre1.lookup pc = some x := by
    show (pre0 ++ Code_pad.table).lookup pc = some x
    rw [lookup_append_or, none]; exact h
  exact lookup_append_left pre5 table pc x (lookup_append_left pre4 Code_lroot.table pc x (lookup_append_left pre3 Code_ladd.table pc x (lookup_append_left pre2 Code_node_out.table pc x (lookup_append_left pre1 Code_chunk_node.table pc x (here)))))

/-- `chunk_node`'s own instructions are in this program: no table before them has one at any of their addresses. -/
theorem in2 : ∀ pc x, Code_chunk_node.table.lookup pc = some x → prog pc = some x := by
  intro pc x h
  have apart : ∀ p ∈ Code_chunk_node.table.map (·.1), ((pre1.lookup p).isNone) = true := by decide +kernel
  have none := Option.isNone_iff_eq_none.mp (apart pc (lookup_mem_keys _ pc x h))
  have here : pre2.lookup pc = some x := by
    show (pre1 ++ Code_chunk_node.table).lookup pc = some x
    rw [lookup_append_or, none]; exact h
  exact lookup_append_left pre5 table pc x (lookup_append_left pre4 Code_lroot.table pc x (lookup_append_left pre3 Code_ladd.table pc x (lookup_append_left pre2 Code_node_out.table pc x (here))))

/-- `node_out`'s own instructions are in this program: no table before them has one at any of their addresses. -/
theorem in3 : ∀ pc x, Code_node_out.table.lookup pc = some x → prog pc = some x := by
  intro pc x h
  have apart : ∀ p ∈ Code_node_out.table.map (·.1), ((pre2.lookup p).isNone) = true := by decide +kernel
  have none := Option.isNone_iff_eq_none.mp (apart pc (lookup_mem_keys _ pc x h))
  have here : pre3.lookup pc = some x := by
    show (pre2 ++ Code_node_out.table).lookup pc = some x
    rw [lookup_append_or, none]; exact h
  exact lookup_append_left pre5 table pc x (lookup_append_left pre4 Code_lroot.table pc x (lookup_append_left pre3 Code_ladd.table pc x (here)))

/-- `ladd`'s own instructions are in this program: no table before them has one at any of their addresses. -/
theorem in4 : ∀ pc x, Code_ladd.table.lookup pc = some x → prog pc = some x := by
  intro pc x h
  have apart : ∀ p ∈ Code_ladd.table.map (·.1), ((pre3.lookup p).isNone) = true := by decide +kernel
  have none := Option.isNone_iff_eq_none.mp (apart pc (lookup_mem_keys _ pc x h))
  have here : pre4.lookup pc = some x := by
    show (pre3 ++ Code_ladd.table).lookup pc = some x
    rw [lookup_append_or, none]; exact h
  exact lookup_append_left pre5 table pc x (lookup_append_left pre4 Code_lroot.table pc x (here))

/-- `lroot`'s own instructions are in this program: no table before them has one at any of their addresses. -/
theorem in5 : ∀ pc x, Code_lroot.table.lookup pc = some x → prog pc = some x := by
  intro pc x h
  have apart : ∀ p ∈ Code_lroot.table.map (·.1), ((pre4.lookup p).isNone) = true := by decide +kernel
  have none := Option.isNone_iff_eq_none.mp (apart pc (lookup_mem_keys _ pc x h))
  have here : pre5.lookup pc = some x := by
    show (pre4 ++ Code_lroot.table).lookup pc = some x
    rw [lookup_append_or, none]; exact h
  exact lookup_append_left pre5 table pc x (here)

/-- `chunk_node`'s program (its own instructions and those of what it calls) is part of this one, unchanged. -/
theorem has_chunk_node : ∀ pc x, Code_chunk_node.prog pc = some x → prog pc = some x := by
  intro pc x h
  have h' : (KCode.table ++ Code_pad.table ++ Code_chunk_node.table).lookup pc = some x := h
  simp only [lookup_append_or] at h'
  cases h0 : KCode.table.lookup pc with
  | some y =>
    rw [h0] at h'; simp only [Option.some_or, Option.some.injEq] at h'; subst h'
    exact has_kernels pc y h0
  | none =>
    rw [h0] at h'; simp only [Option.none_or] at h'
    cases h1 : Code_pad.table.lookup pc with
    | some y =>
      rw [h1] at h'; simp only [Option.some_or, Option.some.injEq] at h'; subst h'
      exact in1 pc y h1
    | none =>
      rw [h1] at h'; simp only [Option.none_or] at h'
      exact in2 pc x h'

/-- `node_out`'s program (its own instructions and those of what it calls) is part of this one, unchanged. -/
theorem has_node_out : ∀ pc x, Code_node_out.prog pc = some x → prog pc = some x := by
  intro pc x h
  have h' : (KCode.table ++ Code_node_out.table).lookup pc = some x := h
  simp only [lookup_append_or] at h'
  cases h0 : KCode.table.lookup pc with
  | some y =>
    rw [h0] at h'; simp only [Option.some_or, Option.some.injEq] at h'; subst h'
    exact has_kernels pc y h0
  | none =>
    rw [h0] at h'; simp only [Option.none_or] at h'
    exact in3 pc x h'

/-- `ladd`'s program (its own instructions and those of what it calls) is part of this one, unchanged. -/
theorem has_ladd : ∀ pc x, Code_ladd.prog pc = some x → prog pc = some x := by
  intro pc x h
  have h' : (KCode.table ++ Code_ladd.table).lookup pc = some x := h
  simp only [lookup_append_or] at h'
  cases h0 : KCode.table.lookup pc with
  | some y =>
    rw [h0] at h'; simp only [Option.some_or, Option.some.injEq] at h'; subst h'
    exact has_kernels pc y h0
  | none =>
    rw [h0] at h'; simp only [Option.none_or] at h'
    exact in4 pc x h'

/-- `lroot`'s program (its own instructions and those of what it calls) is part of this one, unchanged. -/
theorem has_lroot : ∀ pc x, Code_lroot.prog pc = some x → prog pc = some x := by
  intro pc x h
  have h' : (KCode.table ++ Code_lroot.table).lookup pc = some x := h
  simp only [lookup_append_or] at h'
  cases h0 : KCode.table.lookup pc with
  | some y =>
    rw [h0] at h'; simp only [Option.some_or, Option.some.injEq] at h'; subst h'
    exact has_kernels pc y h0
  | none =>
    rw [h0] at h'; simp only [Option.none_or] at h'
    exact in5 pc x h'

@[ode_at] theorem at_40000 : prog 0x40000 = some (.push .rbx, 0x40001) := rfl
@[ode_at] theorem at_40001 : prog 0x40001 = some (.push .rbp, 0x40002) := rfl
@[ode_at] theorem at_40002 : prog 0x40002 = some (.push .r12, 0x40004) := rfl
@[ode_at] theorem at_40004 : prog 0x40004 = some (.push .r13, 0x40006) := rfl
@[ode_at] theorem at_40006 : prog 0x40006 = some (.push .r14, 0x40008) := rfl
@[ode_at] theorem at_40008 : prog 0x40008 = some (.push .r15, 0x4000A) := rfl
@[ode_at] theorem at_4000A : prog 0x4000A = some (.sub 64 (.reg .rsp) (.imm 0xE78), 0x40011) := rfl
@[ode_at] theorem at_40011 : prog 0x40011 = some (.mov 64 (.mem .rsp 0xE60) (.reg .rdi), 0x40019) := rfl
@[ode_at] theorem at_40019 : prog 0x40019 = some (.mov 64 (.mem .rsp 0xE68) (.reg .rsi), 0x40021) := rfl
@[ode_at] theorem at_40021 : prog 0x40021 = some (.mov 64 (.mem .rsp 0xE70) (.reg .rdx), 0x40029) := rfl
@[ode_at] theorem at_40029 : prog 0x40029 = some (.mov 64 (.reg .r13) (.reg .rcx), 0x4002C) := rfl
@[ode_at] theorem at_4002C : prog 0x4002C = some (.mov 64 (.reg .r14) (.reg .r8), 0x4002F) := rfl
@[ode_at] theorem at_4002F : prog 0x4002F = some (.mov 64 (.reg .r15) (.reg .r9), 0x40032) := rfl
@[ode_at] theorem at_40032 : prog 0x40032 = some (.mov 64 (.reg .rax) (.imm 0x0), 0x40039) := rfl
@[ode_at] theorem at_40039 : prog 0x40039 = some (.lea .rcx .rsp 0x0, 0x4003D) := rfl
@[ode_at] theorem at_4003D : prog 0x4003D = some (.mov 64 (.mem .rcx 0x0) (.reg .rax), 0x40040) := rfl
@[ode_at] theorem at_40040 : prog 0x40040 = some (.mov 64 (.reg .rax) (.mem .rsp 0xE68), 0x40048) := rfl
@[ode_at] theorem at_40048 : prog 0x40048 = some (.mov 64 (.reg .rbx) (.reg .rax), 0x4004B) := rfl
@[ode_at] theorem at_4004B : prog 0x4004B = some (.mov 64 (.reg .rax) (.mem .rsp 0xE70), 0x40053) := rfl
@[ode_at] theorem at_40053 : prog 0x40053 = some (.mov 64 (.reg .rbp) (.reg .rax), 0x40056) := rfl
@[ode_at] theorem at_40056 : prog 0x40056 = some (.mov 64 (.reg .rax) (.imm 0x0), 0x4005D) := rfl
@[ode_at] theorem at_4005D : prog 0x4005D = some (.mov 64 (.reg .r12) (.reg .rax), 0x40060) := rfl
@[ode_at] theorem at_40060 : prog 0x40060 = some (.mov 64 (.reg .rax) (.imm 0x400), 0x40067) := rfl
@[ode_at] theorem at_40067 : prog 0x40067 = some (.mov 64 (.reg .rcx) (.reg .rbp), 0x4006A) := rfl
@[ode_at] theorem at_4006A : prog 0x4006A = some (.cmp 64 (.reg .rax) (.reg .rcx), 0x4006D) := rfl
@[ode_at] theorem at_4006D : prog 0x4006D = some (.jae 0x4010C, 0x40073) := rfl
@[ode_at] theorem at_40073 : prog 0x40073 = some (.mov 64 (.reg .rax) (.reg .r13), 0x40076) := rfl
@[ode_at] theorem at_40076 : prog 0x40076 = some (.lea .rcx .rsp 0xDC0, 0x4007E) := rfl
@[ode_at] theorem at_4007E : prog 0x4007E = some (.movv false 0 (.m .rax 0x0), 0x40081) := rfl
@[ode_at] theorem at_40081 : prog 0x40081 = some (.storev false .rcx 0x0 0, 0x40084) := rfl
@[ode_at] theorem at_40084 : prog 0x40084 = some (.movv false 0 (.m .rax 0x10), 0x40088) := rfl
@[ode_at] theorem at_40088 : prog 0x40088 = some (.storev false .rcx 0x10 0, 0x4008C) := rfl
@[ode_at] theorem at_4008C : prog 0x4008C = some (.lea .rdi .rsp 0xDC0, 0x40094) := rfl
@[ode_at] theorem at_40094 : prog 0x40094 = some (.mov 64 (.reg .rsi) (.reg .rbx), 0x40097) := rfl
@[ode_at] theorem at_40097 : prog 0x40097 = some (.mov 64 (.reg .rdx) (.imm 0x400), 0x4009E) := rfl
@[ode_at] theorem at_4009E : prog 0x4009E = some (.mov 64 (.reg .rcx) (.reg .r12), 0x400A1) := rfl
@[ode_at] theorem at_400A1 : prog 0x400A1 = some (.mov 64 (.reg .r8) (.reg .r14), 0x400A4) := rfl
@[ode_at] theorem at_400A4 : prog 0x400A4 = some (.mov 64 (.reg .r9) (.reg .r15), 0x400A7) := rfl
@[ode_at] theorem at_400A7 : prog 0x400A7 = some (.call 0xF0000, 0x400AC) := rfl
@[ode_at] theorem at_400AC : prog 0x400AC = some (.lea .rdi .rsp 0xE40, 0x400B4) := rfl
@[ode_at] theorem at_400B4 : prog 0x400B4 = some (.lea .rsi .rsp 0xDC0, 0x400BC) := rfl
@[ode_at] theorem at_400BC : prog 0x400BC = some (.mov 64 (.reg .rdx) (.imm 0x0), 0x400C3) := rfl
@[ode_at] theorem at_400C3 : prog 0x400C3 = some (.mov 64 (.reg .rcx) (.reg .r15), 0x400C6) := rfl
@[ode_at] theorem at_400C6 : prog 0x400C6 = some (.call 0xD0000, 0x400CB) := rfl
@[ode_at] theorem at_400CB : prog 0x400CB = some (.lea .rdi .rsp 0x0, 0x400CF) := rfl
@[ode_at] theorem at_400CF : prog 0x400CF = some (.mov 64 (.reg .rsi) (.reg .r13), 0x400D2) := rfl
@[ode_at] theorem at_400D2 : prog 0x400D2 = some (.mov 64 (.reg .rdx) (.reg .r14), 0x400D5) := rfl
@[ode_at] theorem at_400D5 : prog 0x400D5 = some (.mov 64 (.reg .rcx) (.reg .r15), 0x400D8) := rfl
@[ode_at] theorem at_400D8 : prog 0x400D8 = some (.lea .r8 .rsp 0xE40, 0x400E0) := rfl
@[ode_at] theorem at_400E0 : prog 0x400E0 = some (.call 0xB0000, 0x400E5) := rfl
@[ode_at] theorem at_400E5 : prog 0x400E5 = some (.mov 64 (.reg .rax) (.reg .rbx), 0x400E8) := rfl
@[ode_at] theorem at_400E8 : prog 0x400E8 = some (.add 64 (.reg .rax) (.imm 0x400), 0x400EE) := rfl
@[ode_at] theorem at_400EE : prog 0x400EE = some (.mov 64 (.reg .rbx) (.reg .rax), 0x400F1) := rfl
@[ode_at] theorem at_400F1 : prog 0x400F1 = some (.mov 64 (.reg .rax) (.reg .rbp), 0x400F4) := rfl
@[ode_at] theorem at_400F4 : prog 0x400F4 = some (.sub 64 (.reg .rax) (.imm 0x400), 0x400FA) := rfl
@[ode_at] theorem at_400FA : prog 0x400FA = some (.mov 64 (.reg .rbp) (.reg .rax), 0x400FD) := rfl
@[ode_at] theorem at_400FD : prog 0x400FD = some (.mov 64 (.reg .rax) (.reg .r12), 0x40100) := rfl
@[ode_at] theorem at_40100 : prog 0x40100 = some (.add 64 (.reg .rax) (.imm 0x1), 0x40104) := rfl
@[ode_at] theorem at_40104 : prog 0x40104 = some (.mov 64 (.reg .r12) (.reg .rax), 0x40107) := rfl
@[ode_at] theorem at_40107 : prog 0x40107 = some (.jmp 0x40060, 0x4010C) := rfl
@[ode_at] theorem at_4010C : prog 0x4010C = some (.mov 64 (.reg .rax) (.reg .r13), 0x4010F) := rfl
@[ode_at] theorem at_4010F : prog 0x4010F = some (.lea .rcx .rsp 0xDC0, 0x40117) := rfl
@[ode_at] theorem at_40117 : prog 0x40117 = some (.movv false 0 (.m .rax 0x0), 0x4011A) := rfl
@[ode_at] theorem at_4011A : prog 0x4011A = some (.storev false .rcx 0x0 0, 0x4011D) := rfl
@[ode_at] theorem at_4011D : prog 0x4011D = some (.movv false 0 (.m .rax 0x10), 0x40121) := rfl
@[ode_at] theorem at_40121 : prog 0x40121 = some (.storev false .rcx 0x10 0, 0x40125) := rfl
@[ode_at] theorem at_40125 : prog 0x40125 = some (.lea .rdi .rsp 0xDC0, 0x4012D) := rfl
@[ode_at] theorem at_4012D : prog 0x4012D = some (.mov 64 (.reg .rsi) (.reg .rbx), 0x40130) := rfl
@[ode_at] theorem at_40130 : prog 0x40130 = some (.mov 64 (.reg .rdx) (.reg .rbp), 0x40133) := rfl
@[ode_at] theorem at_40133 : prog 0x40133 = some (.mov 64 (.reg .rcx) (.reg .r12), 0x40136) := rfl
@[ode_at] theorem at_40136 : prog 0x40136 = some (.mov 64 (.reg .r8) (.reg .r14), 0x40139) := rfl
@[ode_at] theorem at_40139 : prog 0x40139 = some (.mov 64 (.reg .r9) (.reg .r15), 0x4013C) := rfl
@[ode_at] theorem at_4013C : prog 0x4013C = some (.call 0xF0000, 0x40141) := rfl
@[ode_at] theorem at_40141 : prog 0x40141 = some (.mov 64 (.reg .rax) (.reg .r12), 0x40144) := rfl
@[ode_at] theorem at_40144 : prog 0x40144 = some (.mov 64 (.reg .rcx) (.imm 0x0), 0x4014B) := rfl
@[ode_at] theorem at_4014B : prog 0x4014B = some (.cmp 64 (.reg .rax) (.reg .rcx), 0x4014E) := rfl
@[ode_at] theorem at_4014E : prog 0x4014E = some (.jne 0x40171, 0x40150) := rfl
@[ode_at] theorem at_40150 : prog 0x40150 = some (.mov 64 (.reg .rdi) (.mem .rsp 0xE60), 0x40158) := rfl
@[ode_at] theorem at_40158 : prog 0x40158 = some (.lea .rsi .rsp 0xDC0, 0x40160) := rfl
@[ode_at] theorem at_40160 : prog 0x40160 = some (.mov 64 (.reg .rdx) (.imm 0x8), 0x40167) := rfl
@[ode_at] theorem at_40167 : prog 0x40167 = some (.mov 64 (.reg .rcx) (.reg .r15), 0x4016A) := rfl
@[ode_at] theorem at_4016A : prog 0x4016A = some (.call 0xD0000, 0x4016F) := rfl
@[ode_at] theorem at_4016F : prog 0x4016F = some (.jmp 0x401C4, 0x40171) := rfl
@[ode_at] theorem at_40171 : prog 0x40171 = some (.lea .rdi .rsp 0xE40, 0x40179) := rfl
@[ode_at] theorem at_40179 : prog 0x40179 = some (.lea .rsi .rsp 0xDC0, 0x40181) := rfl
@[ode_at] theorem at_40181 : prog 0x40181 = some (.mov 64 (.reg .rdx) (.imm 0x0), 0x40188) := rfl
@[ode_at] theorem at_40188 : prog 0x40188 = some (.mov 64 (.reg .rcx) (.reg .r15), 0x4018B) := rfl
@[ode_at] theorem at_4018B : prog 0x4018B = some (.call 0xD0000, 0x40190) := rfl
@[ode_at] theorem at_40190 : prog 0x40190 = some (.lea .rdi .rsp 0x0, 0x40194) := rfl
@[ode_at] theorem at_40194 : prog 0x40194 = some (.mov 64 (.reg .rsi) (.reg .r13), 0x40197) := rfl
@[ode_at] theorem at_40197 : prog 0x40197 = some (.mov 64 (.reg .rdx) (.reg .r14), 0x4019A) := rfl
@[ode_at] theorem at_4019A : prog 0x4019A = some (.mov 64 (.reg .rcx) (.reg .r15), 0x4019D) := rfl
@[ode_at] theorem at_4019D : prog 0x4019D = some (.lea .r8 .rsp 0xE40, 0x401A5) := rfl
@[ode_at] theorem at_401A5 : prog 0x401A5 = some (.call 0xB0000, 0x401AA) := rfl
@[ode_at] theorem at_401AA : prog 0x401AA = some (.mov 64 (.reg .rdi) (.mem .rsp 0xE60), 0x401B2) := rfl
@[ode_at] theorem at_401B2 : prog 0x401B2 = some (.lea .rsi .rsp 0x0, 0x401B6) := rfl
@[ode_at] theorem at_401B6 : prog 0x401B6 = some (.mov 64 (.reg .rdx) (.reg .r13), 0x401B9) := rfl
@[ode_at] theorem at_401B9 : prog 0x401B9 = some (.mov 64 (.reg .rcx) (.reg .r14), 0x401BC) := rfl
@[ode_at] theorem at_401BC : prog 0x401BC = some (.mov 64 (.reg .r8) (.reg .r15), 0x401BF) := rfl
@[ode_at] theorem at_401BF : prog 0x401BF = some (.call 0xC0000, 0x401C4) := rfl
@[ode_at] theorem at_401C4 : prog 0x401C4 = some (.add 64 (.reg .rsp) (.imm 0xE78), 0x401CB) := rfl
@[ode_at] theorem at_401CB : prog 0x401CB = some (.pop .r15, 0x401CD) := rfl
@[ode_at] theorem at_401CD : prog 0x401CD = some (.pop .r14, 0x401CF) := rfl
@[ode_at] theorem at_401CF : prog 0x401CF = some (.pop .r13, 0x401D1) := rfl
@[ode_at] theorem at_401D1 : prog 0x401D1 = some (.pop .r12, 0x401D3) := rfl
@[ode_at] theorem at_401D3 : prog 0x401D3 = some (.pop .rbp, 0x401D4) := rfl
@[ode_at] theorem at_401D4 : prog 0x401D4 = some (.pop .rbx, 0x401D5) := rfl
@[ode_at] theorem at_401D5 : prog 0x401D5 = some (.ret, 0x401D6) := rfl

end Code_hashl
