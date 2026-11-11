import X86
open X86

/-! Written by mk_cross_table.py: every instruction of the proved programs, once, with its bytes. -/

def crossTable : List (Instr × String) := [
  (.push .rbp, "55"),
  (.mov 64 (.reg .rbp) (.reg .rsp), "4889e5"),
  (.loadv 0 (.mem .rdi 0x0), "0f1007"),
  (.loadv 1 (.mem .rdi 0x10), "0f104f10"),
  (.loadv 2 (.mem .rsi 0x0), "0f1016"),
  (.loadv 3 (.mem .rsi 0x10), "0f105e10"),
  (.pcmpeqb 0 2, "660f74c2"),
  (.pcmpeqb 1 3, "660f74cb"),
  (.pand 0 1, "660fdbc1"),
  (.pmovmskb .rax 0, "660fd7c0"),
  (.cmp 32 (.reg .rax) (.imm 0xFFFF), "3dffff0000"),
  (.sete .rax, "0f94c0"),
  (.pop .rbp, "5d"),
  (.ret, "c3")
]
