import Machine
import Cells
open X86

/-! `fillp` as assembled: 51 instructions. Written from the lifter's rows. -/

set_option maxRecDepth 100000
namespace Code_fillp

def table : List (Nat × Instr × Nat) := [
  (0x110000, .push .rbx, 0x110001),
  (0x110001, .push .rbp, 0x110002),
  (0x110002, .push .r12, 0x110004),
  (0x110004, .push .r13, 0x110006),
  (0x110006, .push .r14, 0x110008),
  (0x110008, .push .r15, 0x11000A),
  (0x11000A, .sub 64 (.reg .rsp) (.imm 0x8), 0x11000E),
  (0x11000E, .mov 64 (.reg .rbx) (.reg .rdi), 0x110011),
  (0x110011, .mov 64 (.reg .rbp) (.reg .rsi), 0x110014),
  (0x110014, .mov 64 (.reg .r12) (.reg .rdx), 0x110017),
  (0x110017, .mov 64 (.reg .r13) (.reg .rcx), 0x11001A),
  (0x11001A, .mov 64 (.reg .rax) (.imm 0x0), 0x110021),
  (0x110021, .mov 64 (.reg .r14) (.reg .rax), 0x110024),
  (0x110024, .mov 64 (.reg .rax) (.reg .rbp), 0x110027),
  (0x110027, .mov 64 (.reg .r15) (.reg .rax), 0x11002A),
  (0x11002A, .mov 64 (.reg .rax) (.reg .r14), 0x11002D),
  (0x11002D, .mov 64 (.reg .rcx) (.imm 0x20), 0x110034),
  (0x110034, .cmp 64 (.reg .rax) (.reg .rcx), 0x110037),
  (0x110037, .jae 0x110081, 0x110039),
  (0x110039, .mov 64 (.reg .rax) (.reg .r14), 0x11003C),
  (0x11003C, .mov 64 (.reg .rcx) (.reg .r12), 0x11003F),
  (0x11003F, .cmp 64 (.reg .rax) (.reg .rcx), 0x110042),
  (0x110042, .jae 0x110059, 0x110044),
  (0x110044, .mov 64 (.reg .rax) (.reg .r15), 0x110047),
  (0x110047, .mov 64 (.reg .rcx) (.reg .rbx), 0x11004A),
  (0x11004A, .mov 64 (.reg .rdx) (.reg .r14), 0x11004D),
  (0x11004D, .shl64 .rdx 3, 0x110051),
  (0x110051, .add 64 (.reg .rcx) (.reg .rdx), 0x110054),
  (0x110054, .mov 64 (.mem .rcx 0x0) (.reg .rax), 0x110057),
  (0x110057, .jmp 0x11006C, 0x110059),
  (0x110059, .mov 64 (.reg .rax) (.reg .rbp), 0x11005C),
  (0x11005C, .mov 64 (.reg .rcx) (.reg .rbx), 0x11005F),
  (0x11005F, .mov 64 (.reg .rdx) (.reg .r14), 0x110062),
  (0x110062, .shl64 .rdx 3, 0x110066),
  (0x110066, .add 64 (.reg .rcx) (.reg .rdx), 0x110069),
  (0x110069, .mov 64 (.mem .rcx 0x0) (.reg .rax), 0x11006C),
  (0x11006C, .mov 64 (.reg .rax) (.reg .r15), 0x11006F),
  (0x11006F, .add 64 (.reg .rax) (.reg .r13), 0x110072),
  (0x110072, .mov 64 (.reg .r15) (.reg .rax), 0x110075),
  (0x110075, .mov 64 (.reg .rax) (.reg .r14), 0x110078),
  (0x110078, .add 64 (.reg .rax) (.imm 0x1), 0x11007C),
  (0x11007C, .mov 64 (.reg .r14) (.reg .rax), 0x11007F),
  (0x11007F, .jmp 0x11002A, 0x110081),
  (0x110081, .add 64 (.reg .rsp) (.imm 0x8), 0x110085),
  (0x110085, .pop .r15, 0x110087),
  (0x110087, .pop .r14, 0x110089),
  (0x110089, .pop .r13, 0x11008B),
  (0x11008B, .pop .r12, 0x11008D),
  (0x11008D, .pop .rbp, 0x11008E),
  (0x11008E, .pop .rbx, 0x11008F),
  (0x11008F, .ret, 0x110090)
]

/-- Every instruction of the program: this function's (it calls nothing). -/
def whole : List (Nat × Instr × Nat) := table

def prog (pc : Nat) : Option (Instr × Nat) := whole.lookup pc

/-- The addresses the program has an instruction at. -/
def keys : List Nat := whole.map (·.1)

theorem keys_of : ∀ pc x, prog pc = some x → pc ∈ keys := fun pc x h => lookup_mem_keys whole pc x h

@[ode_at] theorem at_110000 : prog 0x110000 = some (.push .rbx, 0x110001) := rfl
@[ode_at] theorem at_110001 : prog 0x110001 = some (.push .rbp, 0x110002) := rfl
@[ode_at] theorem at_110002 : prog 0x110002 = some (.push .r12, 0x110004) := rfl
@[ode_at] theorem at_110004 : prog 0x110004 = some (.push .r13, 0x110006) := rfl
@[ode_at] theorem at_110006 : prog 0x110006 = some (.push .r14, 0x110008) := rfl
@[ode_at] theorem at_110008 : prog 0x110008 = some (.push .r15, 0x11000A) := rfl
@[ode_at] theorem at_11000A : prog 0x11000A = some (.sub 64 (.reg .rsp) (.imm 0x8), 0x11000E) := rfl
@[ode_at] theorem at_11000E : prog 0x11000E = some (.mov 64 (.reg .rbx) (.reg .rdi), 0x110011) := rfl
@[ode_at] theorem at_110011 : prog 0x110011 = some (.mov 64 (.reg .rbp) (.reg .rsi), 0x110014) := rfl
@[ode_at] theorem at_110014 : prog 0x110014 = some (.mov 64 (.reg .r12) (.reg .rdx), 0x110017) := rfl
@[ode_at] theorem at_110017 : prog 0x110017 = some (.mov 64 (.reg .r13) (.reg .rcx), 0x11001A) := rfl
@[ode_at] theorem at_11001A : prog 0x11001A = some (.mov 64 (.reg .rax) (.imm 0x0), 0x110021) := rfl
@[ode_at] theorem at_110021 : prog 0x110021 = some (.mov 64 (.reg .r14) (.reg .rax), 0x110024) := rfl
@[ode_at] theorem at_110024 : prog 0x110024 = some (.mov 64 (.reg .rax) (.reg .rbp), 0x110027) := rfl
@[ode_at] theorem at_110027 : prog 0x110027 = some (.mov 64 (.reg .r15) (.reg .rax), 0x11002A) := rfl
@[ode_at] theorem at_11002A : prog 0x11002A = some (.mov 64 (.reg .rax) (.reg .r14), 0x11002D) := rfl
@[ode_at] theorem at_11002D : prog 0x11002D = some (.mov 64 (.reg .rcx) (.imm 0x20), 0x110034) := rfl
@[ode_at] theorem at_110034 : prog 0x110034 = some (.cmp 64 (.reg .rax) (.reg .rcx), 0x110037) := rfl
@[ode_at] theorem at_110037 : prog 0x110037 = some (.jae 0x110081, 0x110039) := rfl
@[ode_at] theorem at_110039 : prog 0x110039 = some (.mov 64 (.reg .rax) (.reg .r14), 0x11003C) := rfl
@[ode_at] theorem at_11003C : prog 0x11003C = some (.mov 64 (.reg .rcx) (.reg .r12), 0x11003F) := rfl
@[ode_at] theorem at_11003F : prog 0x11003F = some (.cmp 64 (.reg .rax) (.reg .rcx), 0x110042) := rfl
@[ode_at] theorem at_110042 : prog 0x110042 = some (.jae 0x110059, 0x110044) := rfl
@[ode_at] theorem at_110044 : prog 0x110044 = some (.mov 64 (.reg .rax) (.reg .r15), 0x110047) := rfl
@[ode_at] theorem at_110047 : prog 0x110047 = some (.mov 64 (.reg .rcx) (.reg .rbx), 0x11004A) := rfl
@[ode_at] theorem at_11004A : prog 0x11004A = some (.mov 64 (.reg .rdx) (.reg .r14), 0x11004D) := rfl
@[ode_at] theorem at_11004D : prog 0x11004D = some (.shl64 .rdx 3, 0x110051) := rfl
@[ode_at] theorem at_110051 : prog 0x110051 = some (.add 64 (.reg .rcx) (.reg .rdx), 0x110054) := rfl
@[ode_at] theorem at_110054 : prog 0x110054 = some (.mov 64 (.mem .rcx 0x0) (.reg .rax), 0x110057) := rfl
@[ode_at] theorem at_110057 : prog 0x110057 = some (.jmp 0x11006C, 0x110059) := rfl
@[ode_at] theorem at_110059 : prog 0x110059 = some (.mov 64 (.reg .rax) (.reg .rbp), 0x11005C) := rfl
@[ode_at] theorem at_11005C : prog 0x11005C = some (.mov 64 (.reg .rcx) (.reg .rbx), 0x11005F) := rfl
@[ode_at] theorem at_11005F : prog 0x11005F = some (.mov 64 (.reg .rdx) (.reg .r14), 0x110062) := rfl
@[ode_at] theorem at_110062 : prog 0x110062 = some (.shl64 .rdx 3, 0x110066) := rfl
@[ode_at] theorem at_110066 : prog 0x110066 = some (.add 64 (.reg .rcx) (.reg .rdx), 0x110069) := rfl
@[ode_at] theorem at_110069 : prog 0x110069 = some (.mov 64 (.mem .rcx 0x0) (.reg .rax), 0x11006C) := rfl
@[ode_at] theorem at_11006C : prog 0x11006C = some (.mov 64 (.reg .rax) (.reg .r15), 0x11006F) := rfl
@[ode_at] theorem at_11006F : prog 0x11006F = some (.add 64 (.reg .rax) (.reg .r13), 0x110072) := rfl
@[ode_at] theorem at_110072 : prog 0x110072 = some (.mov 64 (.reg .r15) (.reg .rax), 0x110075) := rfl
@[ode_at] theorem at_110075 : prog 0x110075 = some (.mov 64 (.reg .rax) (.reg .r14), 0x110078) := rfl
@[ode_at] theorem at_110078 : prog 0x110078 = some (.add 64 (.reg .rax) (.imm 0x1), 0x11007C) := rfl
@[ode_at] theorem at_11007C : prog 0x11007C = some (.mov 64 (.reg .r14) (.reg .rax), 0x11007F) := rfl
@[ode_at] theorem at_11007F : prog 0x11007F = some (.jmp 0x11002A, 0x110081) := rfl
@[ode_at] theorem at_110081 : prog 0x110081 = some (.add 64 (.reg .rsp) (.imm 0x8), 0x110085) := rfl
@[ode_at] theorem at_110085 : prog 0x110085 = some (.pop .r15, 0x110087) := rfl
@[ode_at] theorem at_110087 : prog 0x110087 = some (.pop .r14, 0x110089) := rfl
@[ode_at] theorem at_110089 : prog 0x110089 = some (.pop .r13, 0x11008B) := rfl
@[ode_at] theorem at_11008B : prog 0x11008B = some (.pop .r12, 0x11008D) := rfl
@[ode_at] theorem at_11008D : prog 0x11008D = some (.pop .rbp, 0x11008E) := rfl
@[ode_at] theorem at_11008E : prog 0x11008E = some (.pop .rbx, 0x11008F) := rfl
@[ode_at] theorem at_11008F : prog 0x11008F = some (.ret, 0x110090) := rfl

end Code_fillp
