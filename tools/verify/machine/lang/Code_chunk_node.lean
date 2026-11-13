import Machine
import KCode
import Cells
import Code_pad
open X86

/-! `chunk_node` as assembled: 81 instructions. Written from the lifter's rows. -/

set_option maxRecDepth 100000
namespace Code_chunk_node

def table : List (Nat × Instr × Nat) := [
  (0xF0000, .push .rbx, 0xF0001),
  (0xF0001, .push .rbp, 0xF0002),
  (0xF0002, .push .r12, 0xF0004),
  (0xF0004, .push .r13, 0xF0006),
  (0xF0006, .push .r14, 0xF0008),
  (0xF0008, .push .r15, 0xF000A),
  (0xF000A, .sub 64 (.reg .rsp) (.imm 0x28), 0xF000E),
  (0xF000E, .mov 64 (.reg .r13) (.reg .rdi), 0xF0011),
  (0xF0011, .mov 64 (.mem .rsp 0x0) (.reg .rsi), 0xF0015),
  (0xF0015, .mov 64 (.mem .rsp 0x8) (.reg .rdx), 0xF001A),
  (0xF001A, .mov 64 (.reg .r14) (.reg .rcx), 0xF001D),
  (0xF001D, .mov 64 (.mem .rsp 0x10) (.reg .r8), 0xF0022),
  (0xF0022, .mov 64 (.reg .r15) (.reg .r9), 0xF0025),
  (0xF0025, .mov 64 (.reg .rax) (.imm 0x1), 0xF002C),
  (0xF002C, .mov 64 (.reg .r12) (.reg .rax), 0xF002F),
  (0xF002F, .mov 64 (.reg .rax) (.mem .rsp 0x0), 0xF0033),
  (0xF0033, .mov 64 (.reg .rbx) (.reg .rax), 0xF0036),
  (0xF0036, .mov 64 (.reg .rax) (.mem .rsp 0x8), 0xF003B),
  (0xF003B, .mov 64 (.reg .rbp) (.reg .rax), 0xF003E),
  (0xF003E, .mov 64 (.reg .rax) (.imm 0x40), 0xF0045),
  (0xF0045, .mov 64 (.reg .rcx) (.reg .rbp), 0xF0048),
  (0xF0048, .cmp 64 (.reg .rax) (.reg .rcx), 0xF004B),
  (0xF004B, .jae 0xF00C2, 0xF004D),
  (0xF004D, .mov 64 (.reg .rax) (.mem .rsp 0x10), 0xF0052),
  (0xF0052, .or 64 (.reg .rax) (.reg .r12), 0xF0055),
  (0xF0055, .mov 64 (.mem .rsp 0x18) (.reg .rax), 0xF005A),
  (0xF005A, .mov 64 (.reg .rax) (.reg .r15), 0xF005D),
  (0xF005D, .mov 64 (.reg .rcx) (.imm 0x5), 0xF0064),
  (0xF0064, .cmp 64 (.reg .rax) (.reg .rcx), 0xF0067),
  (0xF0067, .jne 0xF0085, 0xF0069),
  (0xF0069, .mov 64 (.reg .rdi) (.reg .r13), 0xF006C),
  (0xF006C, .mov 64 (.reg .rsi) (.reg .rbx), 0xF006F),
  (0xF006F, .mov 64 (.reg .rdx) (.imm 0x40), 0xF0076),
  (0xF0076, .mov 64 (.reg .rcx) (.reg .r14), 0xF0079),
  (0xF0079, .mov 64 (.reg .r8) (.mem .rsp 0x18), 0xF007E),
  (0xF007E, .call 0x30000, 0xF0083),
  (0xF0083, .jmp 0xF009F, 0xF0085),
  (0xF0085, .mov 64 (.reg .rdi) (.reg .r13), 0xF0088),
  (0xF0088, .mov 64 (.reg .rsi) (.reg .rbx), 0xF008B),
  (0xF008B, .mov 64 (.reg .rdx) (.imm 0x40), 0xF0092),
  (0xF0092, .mov 64 (.reg .rcx) (.reg .r14), 0xF0095),
  (0xF0095, .mov 64 (.reg .r8) (.mem .rsp 0x18), 0xF009A),
  (0xF009A, .call 0x20000, 0xF009F),
  (0xF009F, .mov 64 (.reg .rax) (.imm 0x0), 0xF00A6),
  (0xF00A6, .mov 64 (.reg .r12) (.reg .rax), 0xF00A9),
  (0xF00A9, .mov 64 (.reg .rax) (.reg .rbx), 0xF00AC),
  (0xF00AC, .add 64 (.reg .rax) (.imm 0x40), 0xF00B0),
  (0xF00B0, .mov 64 (.reg .rbx) (.reg .rax), 0xF00B3),
  (0xF00B3, .mov 64 (.reg .rax) (.reg .rbp), 0xF00B6),
  (0xF00B6, .sub 64 (.reg .rax) (.imm 0x40), 0xF00BA),
  (0xF00BA, .mov 64 (.reg .rbp) (.reg .rax), 0xF00BD),
  (0xF00BD, .jmp 0xF003E, 0xF00C2),
  (0xF00C2, .mov 64 (.reg .rax) (.reg .r13), 0xF00C5),
  (0xF00C5, .add 64 (.reg .rax) (.imm 0x20), 0xF00C9),
  (0xF00C9, .mov 64 (.mem .rsp 0x20) (.reg .rax), 0xF00CE),
  (0xF00CE, .mov 64 (.reg .rdi) (.mem .rsp 0x20), 0xF00D3),
  (0xF00D3, .mov 64 (.reg .rsi) (.reg .rbx), 0xF00D6),
  (0xF00D6, .mov 64 (.reg .rdx) (.reg .rbp), 0xF00D9),
  (0xF00D9, .call 0xE0000, 0xF00DE),
  (0xF00DE, .mov 64 (.reg .rax) (.reg .r14), 0xF00E1),
  (0xF00E1, .mov 64 (.reg .rcx) (.reg .r13), 0xF00E4),
  (0xF00E4, .add 64 (.reg .rcx) (.imm 0x60), 0xF00E8),
  (0xF00E8, .mov 64 (.mem .rcx 0x0) (.reg .rax), 0xF00EB),
  (0xF00EB, .mov 64 (.reg .rax) (.reg .rbp), 0xF00EE),
  (0xF00EE, .mov 64 (.reg .rcx) (.reg .r13), 0xF00F1),
  (0xF00F1, .add 64 (.reg .rcx) (.imm 0x68), 0xF00F5),
  (0xF00F5, .mov 64 (.mem .rcx 0x0) (.reg .rax), 0xF00F8),
  (0xF00F8, .mov 64 (.reg .rax) (.mem .rsp 0x10), 0xF00FD),
  (0xF00FD, .or 64 (.reg .rax) (.reg .r12), 0xF0100),
  (0xF0100, .or 64 (.reg .rax) (.imm 0x2), 0xF0104),
  (0xF0104, .mov 64 (.reg .rcx) (.reg .r13), 0xF0107),
  (0xF0107, .add 64 (.reg .rcx) (.imm 0x70), 0xF010B),
  (0xF010B, .mov 64 (.mem .rcx 0x0) (.reg .rax), 0xF010E),
  (0xF010E, .add 64 (.reg .rsp) (.imm 0x28), 0xF0112),
  (0xF0112, .pop .r15, 0xF0114),
  (0xF0114, .pop .r14, 0xF0116),
  (0xF0116, .pop .r13, 0xF0118),
  (0xF0118, .pop .r12, 0xF011A),
  (0xF011A, .pop .rbp, 0xF011B),
  (0xF011B, .pop .rbx, 0xF011C),
  (0xF011C, .ret, 0xF011D)
]

def pre0 : List (Nat × Instr × Nat) := KCode.table
def pre1 : List (Nat × Instr × Nat) := pre0 ++ Code_pad.table

/-- Every instruction of the program: the two kernels' (one/KCode.lean), `pad`'s, then this function's. -/
def whole : List (Nat × Instr × Nat) := pre1 ++ table

def prog (pc : Nat) : Option (Instr × Nat) := whole.lookup pc

/-- The addresses the program has an instruction at. -/
def keys : List Nat := whole.map (·.1)

theorem keys_of : ∀ pc x, prog pc = some x → pc ∈ keys := fun pc x h => lookup_mem_keys whole pc x h

theorem has_kernels : ∀ pc x, KCode.prog pc = some x → prog pc = some x := by
  intro pc x h
  exact lookup_append_left pre1 table pc x (lookup_append_left pre0 Code_pad.table pc x (h))

/-- `pad`'s program is part of this one, unchanged. -/
theorem has_pad : ∀ pc x, Code_pad.prog pc = some x → prog pc = some x := by
  intro pc x h
  have h' : Code_pad.table.lookup pc = some x := h
  have apart : ∀ p ∈ Code_pad.table.map (·.1), ((pre0.lookup p).isNone) = true := by decide +kernel
  have none := Option.isNone_iff_eq_none.mp (apart pc (lookup_mem_keys _ pc x h'))
  have here : pre1.lookup pc = some x := by
    show (pre0 ++ Code_pad.table).lookup pc = some x
    rw [lookup_append_or, none]; exact h'
  exact lookup_append_left pre1 table pc x (here)

@[ode_at] theorem at_F0000 : prog 0xF0000 = some (.push .rbx, 0xF0001) := rfl
@[ode_at] theorem at_F0001 : prog 0xF0001 = some (.push .rbp, 0xF0002) := rfl
@[ode_at] theorem at_F0002 : prog 0xF0002 = some (.push .r12, 0xF0004) := rfl
@[ode_at] theorem at_F0004 : prog 0xF0004 = some (.push .r13, 0xF0006) := rfl
@[ode_at] theorem at_F0006 : prog 0xF0006 = some (.push .r14, 0xF0008) := rfl
@[ode_at] theorem at_F0008 : prog 0xF0008 = some (.push .r15, 0xF000A) := rfl
@[ode_at] theorem at_F000A : prog 0xF000A = some (.sub 64 (.reg .rsp) (.imm 0x28), 0xF000E) := rfl
@[ode_at] theorem at_F000E : prog 0xF000E = some (.mov 64 (.reg .r13) (.reg .rdi), 0xF0011) := rfl
@[ode_at] theorem at_F0011 : prog 0xF0011 = some (.mov 64 (.mem .rsp 0x0) (.reg .rsi), 0xF0015) := rfl
@[ode_at] theorem at_F0015 : prog 0xF0015 = some (.mov 64 (.mem .rsp 0x8) (.reg .rdx), 0xF001A) := rfl
@[ode_at] theorem at_F001A : prog 0xF001A = some (.mov 64 (.reg .r14) (.reg .rcx), 0xF001D) := rfl
@[ode_at] theorem at_F001D : prog 0xF001D = some (.mov 64 (.mem .rsp 0x10) (.reg .r8), 0xF0022) := rfl
@[ode_at] theorem at_F0022 : prog 0xF0022 = some (.mov 64 (.reg .r15) (.reg .r9), 0xF0025) := rfl
@[ode_at] theorem at_F0025 : prog 0xF0025 = some (.mov 64 (.reg .rax) (.imm 0x1), 0xF002C) := rfl
@[ode_at] theorem at_F002C : prog 0xF002C = some (.mov 64 (.reg .r12) (.reg .rax), 0xF002F) := rfl
@[ode_at] theorem at_F002F : prog 0xF002F = some (.mov 64 (.reg .rax) (.mem .rsp 0x0), 0xF0033) := rfl
@[ode_at] theorem at_F0033 : prog 0xF0033 = some (.mov 64 (.reg .rbx) (.reg .rax), 0xF0036) := rfl
@[ode_at] theorem at_F0036 : prog 0xF0036 = some (.mov 64 (.reg .rax) (.mem .rsp 0x8), 0xF003B) := rfl
@[ode_at] theorem at_F003B : prog 0xF003B = some (.mov 64 (.reg .rbp) (.reg .rax), 0xF003E) := rfl
@[ode_at] theorem at_F003E : prog 0xF003E = some (.mov 64 (.reg .rax) (.imm 0x40), 0xF0045) := rfl
@[ode_at] theorem at_F0045 : prog 0xF0045 = some (.mov 64 (.reg .rcx) (.reg .rbp), 0xF0048) := rfl
@[ode_at] theorem at_F0048 : prog 0xF0048 = some (.cmp 64 (.reg .rax) (.reg .rcx), 0xF004B) := rfl
@[ode_at] theorem at_F004B : prog 0xF004B = some (.jae 0xF00C2, 0xF004D) := rfl
@[ode_at] theorem at_F004D : prog 0xF004D = some (.mov 64 (.reg .rax) (.mem .rsp 0x10), 0xF0052) := rfl
@[ode_at] theorem at_F0052 : prog 0xF0052 = some (.or 64 (.reg .rax) (.reg .r12), 0xF0055) := rfl
@[ode_at] theorem at_F0055 : prog 0xF0055 = some (.mov 64 (.mem .rsp 0x18) (.reg .rax), 0xF005A) := rfl
@[ode_at] theorem at_F005A : prog 0xF005A = some (.mov 64 (.reg .rax) (.reg .r15), 0xF005D) := rfl
@[ode_at] theorem at_F005D : prog 0xF005D = some (.mov 64 (.reg .rcx) (.imm 0x5), 0xF0064) := rfl
@[ode_at] theorem at_F0064 : prog 0xF0064 = some (.cmp 64 (.reg .rax) (.reg .rcx), 0xF0067) := rfl
@[ode_at] theorem at_F0067 : prog 0xF0067 = some (.jne 0xF0085, 0xF0069) := rfl
@[ode_at] theorem at_F0069 : prog 0xF0069 = some (.mov 64 (.reg .rdi) (.reg .r13), 0xF006C) := rfl
@[ode_at] theorem at_F006C : prog 0xF006C = some (.mov 64 (.reg .rsi) (.reg .rbx), 0xF006F) := rfl
@[ode_at] theorem at_F006F : prog 0xF006F = some (.mov 64 (.reg .rdx) (.imm 0x40), 0xF0076) := rfl
@[ode_at] theorem at_F0076 : prog 0xF0076 = some (.mov 64 (.reg .rcx) (.reg .r14), 0xF0079) := rfl
@[ode_at] theorem at_F0079 : prog 0xF0079 = some (.mov 64 (.reg .r8) (.mem .rsp 0x18), 0xF007E) := rfl
@[ode_at] theorem at_F007E : prog 0xF007E = some (.call 0x30000, 0xF0083) := rfl
@[ode_at] theorem at_F0083 : prog 0xF0083 = some (.jmp 0xF009F, 0xF0085) := rfl
@[ode_at] theorem at_F0085 : prog 0xF0085 = some (.mov 64 (.reg .rdi) (.reg .r13), 0xF0088) := rfl
@[ode_at] theorem at_F0088 : prog 0xF0088 = some (.mov 64 (.reg .rsi) (.reg .rbx), 0xF008B) := rfl
@[ode_at] theorem at_F008B : prog 0xF008B = some (.mov 64 (.reg .rdx) (.imm 0x40), 0xF0092) := rfl
@[ode_at] theorem at_F0092 : prog 0xF0092 = some (.mov 64 (.reg .rcx) (.reg .r14), 0xF0095) := rfl
@[ode_at] theorem at_F0095 : prog 0xF0095 = some (.mov 64 (.reg .r8) (.mem .rsp 0x18), 0xF009A) := rfl
@[ode_at] theorem at_F009A : prog 0xF009A = some (.call 0x20000, 0xF009F) := rfl
@[ode_at] theorem at_F009F : prog 0xF009F = some (.mov 64 (.reg .rax) (.imm 0x0), 0xF00A6) := rfl
@[ode_at] theorem at_F00A6 : prog 0xF00A6 = some (.mov 64 (.reg .r12) (.reg .rax), 0xF00A9) := rfl
@[ode_at] theorem at_F00A9 : prog 0xF00A9 = some (.mov 64 (.reg .rax) (.reg .rbx), 0xF00AC) := rfl
@[ode_at] theorem at_F00AC : prog 0xF00AC = some (.add 64 (.reg .rax) (.imm 0x40), 0xF00B0) := rfl
@[ode_at] theorem at_F00B0 : prog 0xF00B0 = some (.mov 64 (.reg .rbx) (.reg .rax), 0xF00B3) := rfl
@[ode_at] theorem at_F00B3 : prog 0xF00B3 = some (.mov 64 (.reg .rax) (.reg .rbp), 0xF00B6) := rfl
@[ode_at] theorem at_F00B6 : prog 0xF00B6 = some (.sub 64 (.reg .rax) (.imm 0x40), 0xF00BA) := rfl
@[ode_at] theorem at_F00BA : prog 0xF00BA = some (.mov 64 (.reg .rbp) (.reg .rax), 0xF00BD) := rfl
@[ode_at] theorem at_F00BD : prog 0xF00BD = some (.jmp 0xF003E, 0xF00C2) := rfl
@[ode_at] theorem at_F00C2 : prog 0xF00C2 = some (.mov 64 (.reg .rax) (.reg .r13), 0xF00C5) := rfl
@[ode_at] theorem at_F00C5 : prog 0xF00C5 = some (.add 64 (.reg .rax) (.imm 0x20), 0xF00C9) := rfl
@[ode_at] theorem at_F00C9 : prog 0xF00C9 = some (.mov 64 (.mem .rsp 0x20) (.reg .rax), 0xF00CE) := rfl
@[ode_at] theorem at_F00CE : prog 0xF00CE = some (.mov 64 (.reg .rdi) (.mem .rsp 0x20), 0xF00D3) := rfl
@[ode_at] theorem at_F00D3 : prog 0xF00D3 = some (.mov 64 (.reg .rsi) (.reg .rbx), 0xF00D6) := rfl
@[ode_at] theorem at_F00D6 : prog 0xF00D6 = some (.mov 64 (.reg .rdx) (.reg .rbp), 0xF00D9) := rfl
@[ode_at] theorem at_F00D9 : prog 0xF00D9 = some (.call 0xE0000, 0xF00DE) := rfl
@[ode_at] theorem at_F00DE : prog 0xF00DE = some (.mov 64 (.reg .rax) (.reg .r14), 0xF00E1) := rfl
@[ode_at] theorem at_F00E1 : prog 0xF00E1 = some (.mov 64 (.reg .rcx) (.reg .r13), 0xF00E4) := rfl
@[ode_at] theorem at_F00E4 : prog 0xF00E4 = some (.add 64 (.reg .rcx) (.imm 0x60), 0xF00E8) := rfl
@[ode_at] theorem at_F00E8 : prog 0xF00E8 = some (.mov 64 (.mem .rcx 0x0) (.reg .rax), 0xF00EB) := rfl
@[ode_at] theorem at_F00EB : prog 0xF00EB = some (.mov 64 (.reg .rax) (.reg .rbp), 0xF00EE) := rfl
@[ode_at] theorem at_F00EE : prog 0xF00EE = some (.mov 64 (.reg .rcx) (.reg .r13), 0xF00F1) := rfl
@[ode_at] theorem at_F00F1 : prog 0xF00F1 = some (.add 64 (.reg .rcx) (.imm 0x68), 0xF00F5) := rfl
@[ode_at] theorem at_F00F5 : prog 0xF00F5 = some (.mov 64 (.mem .rcx 0x0) (.reg .rax), 0xF00F8) := rfl
@[ode_at] theorem at_F00F8 : prog 0xF00F8 = some (.mov 64 (.reg .rax) (.mem .rsp 0x10), 0xF00FD) := rfl
@[ode_at] theorem at_F00FD : prog 0xF00FD = some (.or 64 (.reg .rax) (.reg .r12), 0xF0100) := rfl
@[ode_at] theorem at_F0100 : prog 0xF0100 = some (.or 64 (.reg .rax) (.imm 0x2), 0xF0104) := rfl
@[ode_at] theorem at_F0104 : prog 0xF0104 = some (.mov 64 (.reg .rcx) (.reg .r13), 0xF0107) := rfl
@[ode_at] theorem at_F0107 : prog 0xF0107 = some (.add 64 (.reg .rcx) (.imm 0x70), 0xF010B) := rfl
@[ode_at] theorem at_F010B : prog 0xF010B = some (.mov 64 (.mem .rcx 0x0) (.reg .rax), 0xF010E) := rfl
@[ode_at] theorem at_F010E : prog 0xF010E = some (.add 64 (.reg .rsp) (.imm 0x28), 0xF0112) := rfl
@[ode_at] theorem at_F0112 : prog 0xF0112 = some (.pop .r15, 0xF0114) := rfl
@[ode_at] theorem at_F0114 : prog 0xF0114 = some (.pop .r14, 0xF0116) := rfl
@[ode_at] theorem at_F0116 : prog 0xF0116 = some (.pop .r13, 0xF0118) := rfl
@[ode_at] theorem at_F0118 : prog 0xF0118 = some (.pop .r12, 0xF011A) := rfl
@[ode_at] theorem at_F011A : prog 0xF011A = some (.pop .rbp, 0xF011B) := rfl
@[ode_at] theorem at_F011B : prog 0xF011B = some (.pop .rbx, 0xF011C) := rfl
@[ode_at] theorem at_F011C : prog 0xF011C = some (.ret, 0xF011D) := rfl

end Code_chunk_node
