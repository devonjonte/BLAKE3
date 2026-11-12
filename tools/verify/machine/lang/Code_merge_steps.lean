import Machine
import KCode
import Cells
import Code_merge
open X86

/-! `merge_steps` as assembled: 46 instructions. Written from the lifter's rows. -/

set_option maxRecDepth 100000
namespace Code_merge_steps

def table : List (Nat × Instr × Nat) := [
  (0xA0000, .push .rbx, 0xA0001),
  (0xA0001, .push .rbp, 0xA0002),
  (0xA0002, .push .r12, 0xA0004),
  (0xA0004, .push .r13, 0xA0006),
  (0xA0006, .push .r14, 0xA0008),
  (0xA0008, .push .r15, 0xA000A),
  (0xA000A, .sub 64 (.reg .rsp) (.imm 0x8), 0xA000E),
  (0xA000E, .mov 64 (.reg .rbx) (.reg .rdi), 0xA0011),
  (0xA0011, .mov 64 (.reg .rbp) (.reg .rsi), 0xA0014),
  (0xA0014, .mov 64 (.reg .r12) (.reg .rdx), 0xA0017),
  (0xA0017, .mov 64 (.reg .r13) (.reg .rcx), 0xA001A),
  (0xA001A, .mov 64 (.reg .r14) (.reg .r8), 0xA001D),
  (0xA001D, .mov 64 (.reg .rax) (.reg .rbx), 0xA0020),
  (0xA0020, .mov 64 (.reg .rax) (.mem .rax 0x0), 0xA0023),
  (0xA0023, .mov 64 (.reg .r15) (.reg .rax), 0xA0026),
  (0xA0026, .mov 64 (.reg .rax) (.reg .r14), 0xA0029),
  (0xA0029, .mov 64 (.reg .rcx) (.reg .r15), 0xA002C),
  (0xA002C, .cmp 64 (.reg .rax) (.reg .rcx), 0xA002F),
  (0xA002F, .jae 0xA0051, 0xA0031),
  (0xA0031, .mov 64 (.reg .rax) (.reg .r15), 0xA0034),
  (0xA0034, .sub 64 (.reg .rax) (.imm 0x1), 0xA0038),
  (0xA0038, .mov 64 (.reg .r15) (.reg .rax), 0xA003B),
  (0xA003B, .mov 64 (.reg .rdi) (.reg .rbx), 0xA003E),
  (0xA003E, .mov 64 (.reg .rsi) (.reg .rbp), 0xA0041),
  (0xA0041, .mov 64 (.reg .rdx) (.reg .r12), 0xA0044),
  (0xA0044, .mov 64 (.reg .rcx) (.reg .r13), 0xA0047),
  (0xA0047, .mov 64 (.reg .r8) (.reg .r15), 0xA004A),
  (0xA004A, .call 0x60000, 0xA004F),
  (0xA004F, .jmp 0xA0026, 0xA0051),
  (0xA0051, .mov 64 (.reg .rax) (.reg .r15), 0xA0054),
  (0xA0054, .add 64 (.reg .rsp) (.imm 0x8), 0xA0058),
  (0xA0058, .pop .r15, 0xA005A),
  (0xA005A, .pop .r14, 0xA005C),
  (0xA005C, .pop .r13, 0xA005E),
  (0xA005E, .pop .r12, 0xA0060),
  (0xA0060, .pop .rbp, 0xA0061),
  (0xA0061, .pop .rbx, 0xA0062),
  (0xA0062, .ret, 0xA0063),
  (0xA0070, .cmp 64 (.reg .r8) (.imm 0x1), 0xA0074),
  (0xA0074, .jae 0xA0078, 0xA0076),
  (0xA0076, .jmp 0xA0086, 0xA0078),
  (0xA0078, .cmp 64 (.reg .rdx) (.imm 0x100), 0xA007F),
  (0xA007F, .jae 0xA0086, 0xA0081),
  (0xA0081, .jmp 0xA0000, 0xA0086),
  (0xA0086, .mov 64 (.reg .rax) (.imm 0xFFFFFFFFFFFFFFFF), 0xA008D),
  (0xA008D, .ret, 0xA008E)
]

def pre0 : List (Nat × Instr × Nat) := KCode.table
def pre1 : List (Nat × Instr × Nat) := pre0 ++ Code_merge.table

/-- Every instruction of the program: the two kernels' (one/KCode.lean), `merge`'s, then this function's. -/
def whole : List (Nat × Instr × Nat) := pre1 ++ table

def prog (pc : Nat) : Option (Instr × Nat) := whole.lookup pc

/-- The addresses the program has an instruction at. -/
def keys : List Nat := whole.map (·.1)

theorem keys_of : ∀ pc x, prog pc = some x → pc ∈ keys := fun pc x h => lookup_mem_keys whole pc x h

theorem has_kernels : ∀ pc x, KCode.prog pc = some x → prog pc = some x := by
  intro pc x h
  exact lookup_append_left pre1 table pc x (lookup_append_left pre0 Code_merge.table pc x (h))

/-- `merge`'s program is part of this one, unchanged. -/
theorem has_merge : ∀ pc x, Code_merge.prog pc = some x → prog pc = some x := by
  intro pc x h
  have h' : (KCode.table ++ Code_merge.table).lookup pc = some x := h
  rw [lookup_append_or] at h'
  cases hk : KCode.table.lookup pc with
  | some y =>
    rw [hk] at h'; simp only [Option.some_or, Option.some.injEq] at h'; subst h'
    exact has_kernels pc y hk
  | none =>
    rw [hk] at h'; simp only [Option.none_or] at h'
    have apart : ∀ p ∈ Code_merge.table.map (·.1), ((pre0.lookup p).isNone) = true := by decide +kernel
    have none := Option.isNone_iff_eq_none.mp (apart pc (lookup_mem_keys _ pc x h'))
    have here : pre1.lookup pc = some x := by
      show (pre0 ++ Code_merge.table).lookup pc = some x
      rw [lookup_append_or, none]; exact h'
    exact lookup_append_left pre1 table pc x (here)

@[ode_at] theorem at_A0000 : prog 0xA0000 = some (.push .rbx, 0xA0001) := rfl
@[ode_at] theorem at_A0001 : prog 0xA0001 = some (.push .rbp, 0xA0002) := rfl
@[ode_at] theorem at_A0002 : prog 0xA0002 = some (.push .r12, 0xA0004) := rfl
@[ode_at] theorem at_A0004 : prog 0xA0004 = some (.push .r13, 0xA0006) := rfl
@[ode_at] theorem at_A0006 : prog 0xA0006 = some (.push .r14, 0xA0008) := rfl
@[ode_at] theorem at_A0008 : prog 0xA0008 = some (.push .r15, 0xA000A) := rfl
@[ode_at] theorem at_A000A : prog 0xA000A = some (.sub 64 (.reg .rsp) (.imm 0x8), 0xA000E) := rfl
@[ode_at] theorem at_A000E : prog 0xA000E = some (.mov 64 (.reg .rbx) (.reg .rdi), 0xA0011) := rfl
@[ode_at] theorem at_A0011 : prog 0xA0011 = some (.mov 64 (.reg .rbp) (.reg .rsi), 0xA0014) := rfl
@[ode_at] theorem at_A0014 : prog 0xA0014 = some (.mov 64 (.reg .r12) (.reg .rdx), 0xA0017) := rfl
@[ode_at] theorem at_A0017 : prog 0xA0017 = some (.mov 64 (.reg .r13) (.reg .rcx), 0xA001A) := rfl
@[ode_at] theorem at_A001A : prog 0xA001A = some (.mov 64 (.reg .r14) (.reg .r8), 0xA001D) := rfl
@[ode_at] theorem at_A001D : prog 0xA001D = some (.mov 64 (.reg .rax) (.reg .rbx), 0xA0020) := rfl
@[ode_at] theorem at_A0020 : prog 0xA0020 = some (.mov 64 (.reg .rax) (.mem .rax 0x0), 0xA0023) := rfl
@[ode_at] theorem at_A0023 : prog 0xA0023 = some (.mov 64 (.reg .r15) (.reg .rax), 0xA0026) := rfl
@[ode_at] theorem at_A0026 : prog 0xA0026 = some (.mov 64 (.reg .rax) (.reg .r14), 0xA0029) := rfl
@[ode_at] theorem at_A0029 : prog 0xA0029 = some (.mov 64 (.reg .rcx) (.reg .r15), 0xA002C) := rfl
@[ode_at] theorem at_A002C : prog 0xA002C = some (.cmp 64 (.reg .rax) (.reg .rcx), 0xA002F) := rfl
@[ode_at] theorem at_A002F : prog 0xA002F = some (.jae 0xA0051, 0xA0031) := rfl
@[ode_at] theorem at_A0031 : prog 0xA0031 = some (.mov 64 (.reg .rax) (.reg .r15), 0xA0034) := rfl
@[ode_at] theorem at_A0034 : prog 0xA0034 = some (.sub 64 (.reg .rax) (.imm 0x1), 0xA0038) := rfl
@[ode_at] theorem at_A0038 : prog 0xA0038 = some (.mov 64 (.reg .r15) (.reg .rax), 0xA003B) := rfl
@[ode_at] theorem at_A003B : prog 0xA003B = some (.mov 64 (.reg .rdi) (.reg .rbx), 0xA003E) := rfl
@[ode_at] theorem at_A003E : prog 0xA003E = some (.mov 64 (.reg .rsi) (.reg .rbp), 0xA0041) := rfl
@[ode_at] theorem at_A0041 : prog 0xA0041 = some (.mov 64 (.reg .rdx) (.reg .r12), 0xA0044) := rfl
@[ode_at] theorem at_A0044 : prog 0xA0044 = some (.mov 64 (.reg .rcx) (.reg .r13), 0xA0047) := rfl
@[ode_at] theorem at_A0047 : prog 0xA0047 = some (.mov 64 (.reg .r8) (.reg .r15), 0xA004A) := rfl
@[ode_at] theorem at_A004A : prog 0xA004A = some (.call 0x60000, 0xA004F) := rfl
@[ode_at] theorem at_A004F : prog 0xA004F = some (.jmp 0xA0026, 0xA0051) := rfl
@[ode_at] theorem at_A0051 : prog 0xA0051 = some (.mov 64 (.reg .rax) (.reg .r15), 0xA0054) := rfl
@[ode_at] theorem at_A0054 : prog 0xA0054 = some (.add 64 (.reg .rsp) (.imm 0x8), 0xA0058) := rfl
@[ode_at] theorem at_A0058 : prog 0xA0058 = some (.pop .r15, 0xA005A) := rfl
@[ode_at] theorem at_A005A : prog 0xA005A = some (.pop .r14, 0xA005C) := rfl
@[ode_at] theorem at_A005C : prog 0xA005C = some (.pop .r13, 0xA005E) := rfl
@[ode_at] theorem at_A005E : prog 0xA005E = some (.pop .r12, 0xA0060) := rfl
@[ode_at] theorem at_A0060 : prog 0xA0060 = some (.pop .rbp, 0xA0061) := rfl
@[ode_at] theorem at_A0061 : prog 0xA0061 = some (.pop .rbx, 0xA0062) := rfl
@[ode_at] theorem at_A0062 : prog 0xA0062 = some (.ret, 0xA0063) := rfl
@[ode_at] theorem at_A0070 : prog 0xA0070 = some (.cmp 64 (.reg .r8) (.imm 0x1), 0xA0074) := rfl
@[ode_at] theorem at_A0074 : prog 0xA0074 = some (.jae 0xA0078, 0xA0076) := rfl
@[ode_at] theorem at_A0076 : prog 0xA0076 = some (.jmp 0xA0086, 0xA0078) := rfl
@[ode_at] theorem at_A0078 : prog 0xA0078 = some (.cmp 64 (.reg .rdx) (.imm 0x100), 0xA007F) := rfl
@[ode_at] theorem at_A007F : prog 0xA007F = some (.jae 0xA0086, 0xA0081) := rfl
@[ode_at] theorem at_A0081 : prog 0xA0081 = some (.jmp 0xA0000, 0xA0086) := rfl
@[ode_at] theorem at_A0086 : prog 0xA0086 = some (.mov 64 (.reg .rax) (.imm 0xFFFFFFFFFFFFFFFF), 0xA008D) := rfl
@[ode_at] theorem at_A008D : prog 0xA008D = some (.ret, 0xA008E) := rfl

end Code_merge_steps
