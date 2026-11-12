import Machine
import KCode
import Cells
import Code_merge
import Code_push
open X86

/-! `add` as assembled: 30 instructions. Written from the lifter's rows. -/

set_option maxRecDepth 100000
namespace Code_add

def table : List (Nat × Instr × Nat) := [
  (0x80000, .push .rbx, 0x80001),
  (0x80001, .push .rbp, 0x80002),
  (0x80002, .push .r12, 0x80004),
  (0x80004, .push .r13, 0x80006),
  (0x80006, .push .r14, 0x80008),
  (0x80008, .push .r15, 0x8000A),
  (0x8000A, .sub 64 (.reg .rsp) (.imm 0x8), 0x8000E),
  (0x8000E, .mov 64 (.reg .rbx) (.reg .rdi), 0x80011),
  (0x80011, .mov 64 (.reg .rbp) (.reg .rsi), 0x80014),
  (0x80014, .mov 64 (.reg .r12) (.reg .rdx), 0x80017),
  (0x80017, .mov 64 (.reg .r13) (.reg .rcx), 0x8001A),
  (0x8001A, .mov 64 (.reg .r14) (.reg .r8), 0x8001D),
  (0x8001D, .mov 64 (.reg .r15) (.reg .r9), 0x80020),
  (0x80020, .mov 64 (.reg .rdi) (.reg .rbx), 0x80023),
  (0x80023, .mov 64 (.reg .rsi) (.reg .r14), 0x80026),
  (0x80026, .call 0x70000, 0x8002B),
  (0x8002B, .mov 64 (.reg .rdi) (.reg .rbx), 0x8002E),
  (0x8002E, .mov 64 (.reg .rsi) (.reg .rbp), 0x80031),
  (0x80031, .mov 64 (.reg .rdx) (.reg .r12), 0x80034),
  (0x80034, .mov 64 (.reg .rcx) (.reg .r13), 0x80037),
  (0x80037, .mov 64 (.reg .r8) (.reg .r15), 0x8003A),
  (0x8003A, .call 0x60000, 0x8003F),
  (0x8003F, .add 64 (.reg .rsp) (.imm 0x8), 0x80043),
  (0x80043, .pop .r15, 0x80045),
  (0x80045, .pop .r14, 0x80047),
  (0x80047, .pop .r13, 0x80049),
  (0x80049, .pop .r12, 0x8004B),
  (0x8004B, .pop .rbp, 0x8004C),
  (0x8004C, .pop .rbx, 0x8004D),
  (0x8004D, .ret, 0x8004E)
]

def pre0 : List (Nat × Instr × Nat) := KCode.table
def pre1 : List (Nat × Instr × Nat) := pre0 ++ Code_merge.table
def pre2 : List (Nat × Instr × Nat) := pre1 ++ Code_push.table

/-- Every instruction of the program: the two kernels' (one/KCode.lean), `merge`'s, `push`'s, then this function's. -/
def whole : List (Nat × Instr × Nat) := pre2 ++ table

def prog (pc : Nat) : Option (Instr × Nat) := whole.lookup pc

/-- The addresses the program has an instruction at. -/
def keys : List Nat := whole.map (·.1)

theorem keys_of : ∀ pc x, prog pc = some x → pc ∈ keys := fun pc x h => lookup_mem_keys whole pc x h

theorem has_kernels : ∀ pc x, KCode.prog pc = some x → prog pc = some x := by
  intro pc x h
  exact lookup_append_left pre2 table pc x (lookup_append_left pre1 Code_push.table pc x (lookup_append_left pre0 Code_merge.table pc x (h)))

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
    exact lookup_append_left pre2 table pc x (lookup_append_left pre1 Code_push.table pc x (here))

/-- `push`'s program is part of this one, unchanged. -/
theorem has_push : ∀ pc x, Code_push.prog pc = some x → prog pc = some x := by
  intro pc x h
  have h' : Code_push.table.lookup pc = some x := h
  have apart : ∀ p ∈ Code_push.table.map (·.1), ((pre1.lookup p).isNone) = true := by decide +kernel
  have none := Option.isNone_iff_eq_none.mp (apart pc (lookup_mem_keys _ pc x h'))
  have here : pre2.lookup pc = some x := by
    show (pre1 ++ Code_push.table).lookup pc = some x
    rw [lookup_append_or, none]; exact h'
  exact lookup_append_left pre2 table pc x (here)

@[ode_at] theorem at_80000 : prog 0x80000 = some (.push .rbx, 0x80001) := rfl
@[ode_at] theorem at_80001 : prog 0x80001 = some (.push .rbp, 0x80002) := rfl
@[ode_at] theorem at_80002 : prog 0x80002 = some (.push .r12, 0x80004) := rfl
@[ode_at] theorem at_80004 : prog 0x80004 = some (.push .r13, 0x80006) := rfl
@[ode_at] theorem at_80006 : prog 0x80006 = some (.push .r14, 0x80008) := rfl
@[ode_at] theorem at_80008 : prog 0x80008 = some (.push .r15, 0x8000A) := rfl
@[ode_at] theorem at_8000A : prog 0x8000A = some (.sub 64 (.reg .rsp) (.imm 0x8), 0x8000E) := rfl
@[ode_at] theorem at_8000E : prog 0x8000E = some (.mov 64 (.reg .rbx) (.reg .rdi), 0x80011) := rfl
@[ode_at] theorem at_80011 : prog 0x80011 = some (.mov 64 (.reg .rbp) (.reg .rsi), 0x80014) := rfl
@[ode_at] theorem at_80014 : prog 0x80014 = some (.mov 64 (.reg .r12) (.reg .rdx), 0x80017) := rfl
@[ode_at] theorem at_80017 : prog 0x80017 = some (.mov 64 (.reg .r13) (.reg .rcx), 0x8001A) := rfl
@[ode_at] theorem at_8001A : prog 0x8001A = some (.mov 64 (.reg .r14) (.reg .r8), 0x8001D) := rfl
@[ode_at] theorem at_8001D : prog 0x8001D = some (.mov 64 (.reg .r15) (.reg .r9), 0x80020) := rfl
@[ode_at] theorem at_80020 : prog 0x80020 = some (.mov 64 (.reg .rdi) (.reg .rbx), 0x80023) := rfl
@[ode_at] theorem at_80023 : prog 0x80023 = some (.mov 64 (.reg .rsi) (.reg .r14), 0x80026) := rfl
@[ode_at] theorem at_80026 : prog 0x80026 = some (.call 0x70000, 0x8002B) := rfl
@[ode_at] theorem at_8002B : prog 0x8002B = some (.mov 64 (.reg .rdi) (.reg .rbx), 0x8002E) := rfl
@[ode_at] theorem at_8002E : prog 0x8002E = some (.mov 64 (.reg .rsi) (.reg .rbp), 0x80031) := rfl
@[ode_at] theorem at_80031 : prog 0x80031 = some (.mov 64 (.reg .rdx) (.reg .r12), 0x80034) := rfl
@[ode_at] theorem at_80034 : prog 0x80034 = some (.mov 64 (.reg .rcx) (.reg .r13), 0x80037) := rfl
@[ode_at] theorem at_80037 : prog 0x80037 = some (.mov 64 (.reg .r8) (.reg .r15), 0x8003A) := rfl
@[ode_at] theorem at_8003A : prog 0x8003A = some (.call 0x60000, 0x8003F) := rfl
@[ode_at] theorem at_8003F : prog 0x8003F = some (.add 64 (.reg .rsp) (.imm 0x8), 0x80043) := rfl
@[ode_at] theorem at_80043 : prog 0x80043 = some (.pop .r15, 0x80045) := rfl
@[ode_at] theorem at_80045 : prog 0x80045 = some (.pop .r14, 0x80047) := rfl
@[ode_at] theorem at_80047 : prog 0x80047 = some (.pop .r13, 0x80049) := rfl
@[ode_at] theorem at_80049 : prog 0x80049 = some (.pop .r12, 0x8004B) := rfl
@[ode_at] theorem at_8004B : prog 0x8004B = some (.pop .rbp, 0x8004C) := rfl
@[ode_at] theorem at_8004C : prog 0x8004C = some (.pop .rbx, 0x8004D) := rfl
@[ode_at] theorem at_8004D : prog 0x8004D = some (.ret, 0x8004E) := rfl

end Code_add
