import X86
import Decode

/-! The compiled functions' bytes, as the linker places them (a call's displacement filled in), and what
the decoder makes of each instruction. Written by lift.py from llvm-objdump's listing; the listing is a hint:
each line below is checked by Lean against `Decode.lean`. -/

set_option maxRecDepth 100000
namespace Code
open X86

def base : Nat := 0x1000

/-- The bytes, from `base` on. -/
def image : List Nat := [
  0x89, 0xD0, 0x48, 0x85, 0xF6, 0x74, 0x1D, 0x55, 0x48, 0x89, 0xE5, 0x48, 0xC1, 0xE6, 0x02, 0x31,
  0xC9, 0xC1, 0xC0, 0x05, 0x33, 0x04, 0x0F, 0x89, 0x04, 0x0F, 0x48, 0x83, 0xC1, 0x04, 0x48, 0x39,
  0xCE, 0x75, 0xEE, 0x5D, 0xC3, 0x55, 0x48, 0x89, 0xE5, 0x41, 0x56, 0x53, 0x48, 0x89, 0xCB, 0x49,
  0x89, 0xD6, 0x44, 0x89, 0xC2, 0xE8, 0xC6, 0xFF, 0xFF, 0xFF, 0x4C, 0x89, 0xF7, 0x48, 0x89, 0xDE,
  0x89, 0xC2, 0x5B, 0x41, 0x5E, 0x5D, 0xE9, 0xB5, 0xFF, 0xFF, 0xFF
]

/-- The instruction at an address, and the address after it: the decoder on the bytes from there. -/
def prog (pc : Nat) : Option (Instr × Nat) := if base ≤ pc then decode pc (image.drop (pc - base)) else none

theorem at_1000 : prog 0x1000 = some (.mov 32 (.reg .rax) (.reg .rdx), 0x1002) := by decide  -- mov eax, edx
theorem at_1002 : prog 0x1002 = some (.test 64 (.reg .rsi) (.reg .rsi), 0x1005) := by decide  -- test rsi, rsi
theorem at_1005 : prog 0x1005 = some (.jcc .e 0x1024, 0x1007) := by decide  -- je 0x24 <_scan+0x24>
theorem at_1007 : prog 0x1007 = some (.push .rbp, 0x1008) := by decide  -- push rbp
theorem at_1008 : prog 0x1008 = some (.mov 64 (.reg .rbp) (.reg .rsp), 0x100B) := by decide  -- mov rbp, rsp
theorem at_100B : prog 0x100B = some (.shl 64 (.reg .rsi) 2, 0x100F) := by decide  -- shl rsi, 0x2
theorem at_100F : prog 0x100F = some (.xor 32 (.reg .rcx) (.reg .rcx), 0x1011) := by decide  -- xor ecx, ecx
theorem at_1011 : prog 0x1011 = some (.rol32 .rax 5, 0x1014) := by decide  -- rol eax, 0x5
theorem at_1014 : prog 0x1014 = some (.xor 32 (.reg .rax) (.memi .rdi .rcx), 0x1017) := by decide  -- xor eax, dword ptr [rdi + rcx]
theorem at_1017 : prog 0x1017 = some (.mov 32 (.memi .rdi .rcx) (.reg .rax), 0x101A) := by decide  -- mov dword ptr [rdi + rcx], eax
theorem at_101A : prog 0x101A = some (.add 64 (.reg .rcx) (.imm 0x4), 0x101E) := by decide  -- add rcx, 0x4
theorem at_101E : prog 0x101E = some (.cmp 64 (.reg .rsi) (.reg .rcx), 0x1021) := by decide  -- cmp rsi, rcx
theorem at_1021 : prog 0x1021 = some (.jcc .ne 0x1011, 0x1023) := by decide  -- jne 0x11 <_scan+0x11>
theorem at_1023 : prog 0x1023 = some (.pop .rbp, 0x1024) := by decide  -- pop rbp
theorem at_1024 : prog 0x1024 = some (.ret, 0x1025) := by decide  -- ret
theorem at_1025 : prog 0x1025 = some (.push .rbp, 0x1026) := by decide  -- push rbp
theorem at_1026 : prog 0x1026 = some (.mov 64 (.reg .rbp) (.reg .rsp), 0x1029) := by decide  -- mov rbp, rsp
theorem at_1029 : prog 0x1029 = some (.push .r14, 0x102B) := by decide  -- push r14
theorem at_102B : prog 0x102B = some (.push .rbx, 0x102C) := by decide  -- push rbx
theorem at_102C : prog 0x102C = some (.mov 64 (.reg .rbx) (.reg .rcx), 0x102F) := by decide  -- mov rbx, rcx
theorem at_102F : prog 0x102F = some (.mov 64 (.reg .r14) (.reg .rdx), 0x1032) := by decide  -- mov r14, rdx
theorem at_1032 : prog 0x1032 = some (.mov 32 (.reg .rdx) (.reg .r8), 0x1035) := by decide  -- mov edx, r8d
theorem at_1035 : prog 0x1035 = some (.call 0x1000, 0x103A) := by decide  -- call 0x3a <_scan2+0x15>
theorem at_103A : prog 0x103A = some (.mov 64 (.reg .rdi) (.reg .r14), 0x103D) := by decide  -- mov rdi, r14
theorem at_103D : prog 0x103D = some (.mov 64 (.reg .rsi) (.reg .rbx), 0x1040) := by decide  -- mov rsi, rbx
theorem at_1040 : prog 0x1040 = some (.mov 32 (.reg .rdx) (.reg .rax), 0x1042) := by decide  -- mov edx, eax
theorem at_1042 : prog 0x1042 = some (.pop .rbx, 0x1043) := by decide  -- pop rbx
theorem at_1043 : prog 0x1043 = some (.pop .r14, 0x1045) := by decide  -- pop r14
theorem at_1045 : prog 0x1045 = some (.pop .rbp, 0x1046) := by decide  -- pop rbp
theorem at_1046 : prog 0x1046 = some (.jmp 0x1000, 0x104B) := by decide  -- jmp 0x4b <_scan2+0x26>

end Code
