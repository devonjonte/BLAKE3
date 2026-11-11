import X86
import Attr

/-! `blake3_servil_core::Hash::to_hex` as rustc 1.99.1 compiled it (the two-crate trial, release) and
llvm-objdump reads it. Written by lift_hex.py; not edited by hand. `T` is the address of the table. -/

namespace Code
open X86

def table (T : BitVec 64) : List (Nat × Instr × Nat) := [
  (0x1000, .mov 64 (.reg .rax) (.reg .rdi), 0x1003),  -- 48 89 f8                 mov rax, rdi
  (0x1003, .mov 32 (.reg .rcx) (.imm 0x2), 0x1008),  -- b9 02 00 00 00           mov ecx, 0x2
  (0x1008, .mov 64 (.reg .rdx) (.imm T), 0x100F),  -- 48 8d 15 00 00 00 00     lea rdx, [rip]
  (0x100F, .nop, 0x1010),  -- 90                       nop 
  (0x1010, .movzx8 .rdi (.mems .rsi .rcx 1 0xFFFFFFFFFFFFFFFE), 0x1015),  -- 0f b6 7c 0e fe           movzx edi, byte ptr [rsi + rcx - 0x2]
  (0x1015, .mov 32 (.reg .r8) (.reg .rdi), 0x1018),  -- 41 89 f8                 mov r8d, edi
  (0x1018, .shr 32 (.reg .r8) 4, 0x101C),  -- 41 c1 e8 04              shr r8d, 0x4
  (0x101C, .movzx8 .r8 (.memi .r8 .rdx), 0x1021),  -- 45 0f b6 04 10           movzx r8d, byte ptr [r8 + rdx]
  (0x1021, .mov 8 (.mems .rsp .rcx 2 0xFFFFFFFFFFFFFFBC) (.reg .r8), 0x1026),  -- 44 88 44 4c bc           mov byte ptr [rsp + 2*rcx - 0x44], r8b
  (0x1026, .and 32 (.reg .rdi) (.imm 0xF), 0x1029),  -- 83 e7 0f                 and edi, 0xf
  (0x1029, .movzx8 .rdi (.memi .rdi .rdx), 0x102D),  -- 0f b6 3c 17              movzx edi, byte ptr [rdi + rdx]
  (0x102D, .mov 8 (.mems .rsp .rcx 2 0xFFFFFFFFFFFFFFBD) (.reg .rdi), 0x1032),  -- 40 88 7c 4c bd           mov byte ptr [rsp + 2*rcx - 0x43], dil
  (0x1032, .movzx8 .rdi (.mems .rsi .rcx 1 0xFFFFFFFFFFFFFFFF), 0x1037),  -- 0f b6 7c 0e ff           movzx edi, byte ptr [rsi + rcx - 0x1]
  (0x1037, .mov 32 (.reg .r8) (.reg .rdi), 0x103A),  -- 41 89 f8                 mov r8d, edi
  (0x103A, .shr 32 (.reg .r8) 4, 0x103E),  -- 41 c1 e8 04              shr r8d, 0x4
  (0x103E, .movzx8 .r8 (.memi .r8 .rdx), 0x1043),  -- 45 0f b6 04 10           movzx r8d, byte ptr [r8 + rdx]
  (0x1043, .mov 8 (.mems .rsp .rcx 2 0xFFFFFFFFFFFFFFBE) (.reg .r8), 0x1048),  -- 44 88 44 4c be           mov byte ptr [rsp + 2*rcx - 0x42], r8b
  (0x1048, .and 32 (.reg .rdi) (.imm 0xF), 0x104B),  -- 83 e7 0f                 and edi, 0xf
  (0x104B, .movzx8 .rdi (.memi .rdi .rdx), 0x104F),  -- 0f b6 3c 17              movzx edi, byte ptr [rdi + rdx]
  (0x104F, .mov 8 (.mems .rsp .rcx 2 0xFFFFFFFFFFFFFFBF) (.reg .rdi), 0x1054),  -- 40 88 7c 4c bf           mov byte ptr [rsp + 2*rcx - 0x41], dil
  (0x1054, .add 64 (.reg .rcx) (.imm 0x2), 0x1058),  -- 48 83 c1 02              add rcx, 0x2
  (0x1058, .cmp 64 (.reg .rcx) (.imm 0x22), 0x105C),  -- 48 83 f9 22              cmp rcx, 0x22
  (0x105C, .jcc .ne 0x1010, 0x105E),  -- 75 b2                    jne 0x10 <<blake3_servil_core::Hash>::to_hex+0x10>
  (0x105E, .mov 32 (.mem .rsp 0xFFFFFFFFFFFFFFBC) (.imm 0x40), 0x1066),  -- c7 44 24 bc 40 00 00 00  mov dword ptr [rsp - 0x44], 0x40
  (0x1066, .mov 32 (.reg .rcx) (.mem .rsp 0xFFFFFFFFFFFFFFFC), 0x106A),  -- 8b 4c 24 fc              mov ecx, dword ptr [rsp - 0x4]
  (0x106A, .mov 32 (.mem .rax 0x40) (.reg .rcx), 0x106D),  -- 89 48 40                 mov dword ptr [rax + 0x40], ecx
  (0x106D, .loadv 0 (.mem .rsp 0xFFFFFFFFFFFFFFCC), 0x1072),  -- 0f 10 44 24 cc           movups xmm0, xmmword ptr [rsp - 0x34]
  (0x1072, .loadv 1 (.mem .rsp 0xFFFFFFFFFFFFFFDC), 0x1077),  -- 0f 10 4c 24 dc           movups xmm1, xmmword ptr [rsp - 0x24]
  (0x1077, .loadv 2 (.mem .rsp 0xFFFFFFFFFFFFFFEC), 0x107C),  -- 0f 10 54 24 ec           movups xmm2, xmmword ptr [rsp - 0x14]
  (0x107C, .storev (.mem .rax 0x30) 2, 0x1080),  -- 0f 11 50 30              movups xmmword ptr [rax + 0x30], xmm2
  (0x1080, .storev (.mem .rax 0x20) 1, 0x1084),  -- 0f 11 48 20              movups xmmword ptr [rax + 0x20], xmm1
  (0x1084, .storev (.mem .rax 0x10) 0, 0x1088),  -- 0f 11 40 10              movups xmmword ptr [rax + 0x10], xmm0
  (0x1088, .mov 32 (.reg .rcx) (.mem .rsp 0xFFFFFFFFFFFFFFBC), 0x108C),  -- 8b 4c 24 bc              mov ecx, dword ptr [rsp - 0x44]
  (0x108C, .mov 32 (.mem .rax 0x0) (.reg .rcx), 0x108E),  -- 89 08                    mov dword ptr [rax], ecx
  (0x108E, .mov 64 (.reg .rcx) (.mem .rsp 0xFFFFFFFFFFFFFFC0), 0x1093),  -- 48 8b 4c 24 c0           mov rcx, qword ptr [rsp - 0x40]
  (0x1093, .mov 64 (.mem .rax 0x4) (.reg .rcx), 0x1097),  -- 48 89 48 04              mov qword ptr [rax + 0x4], rcx
  (0x1097, .mov 32 (.reg .rcx) (.mem .rsp 0xFFFFFFFFFFFFFFC8), 0x109B),  -- 8b 4c 24 c8              mov ecx, dword ptr [rsp - 0x38]
  (0x109B, .mov 32 (.mem .rax 0xC) (.reg .rcx), 0x109E),  -- 89 48 0c                 mov dword ptr [rax + 0xc], ecx
  (0x109E, .ret, 0x109F)   -- c3                       ret 
]

def prog (T : BitVec 64) (pc : Nat) : Option (Instr × Nat) := (table T).lookup pc

@[code_at] theorem at_1000 (T : BitVec 64) : prog T 0x1000 = some (.mov 64 (.reg .rax) (.reg .rdi), 0x1003) := rfl
@[code_at] theorem at_1003 (T : BitVec 64) : prog T 0x1003 = some (.mov 32 (.reg .rcx) (.imm 0x2), 0x1008) := rfl
@[code_at] theorem at_1008 (T : BitVec 64) : prog T 0x1008 = some (.mov 64 (.reg .rdx) (.imm T), 0x100F) := rfl
@[code_at] theorem at_100F (T : BitVec 64) : prog T 0x100F = some (.nop, 0x1010) := rfl
@[code_at] theorem at_1010 (T : BitVec 64) : prog T 0x1010 = some (.movzx8 .rdi (.mems .rsi .rcx 1 0xFFFFFFFFFFFFFFFE), 0x1015) := rfl
@[code_at] theorem at_1015 (T : BitVec 64) : prog T 0x1015 = some (.mov 32 (.reg .r8) (.reg .rdi), 0x1018) := rfl
@[code_at] theorem at_1018 (T : BitVec 64) : prog T 0x1018 = some (.shr 32 (.reg .r8) 4, 0x101C) := rfl
@[code_at] theorem at_101C (T : BitVec 64) : prog T 0x101C = some (.movzx8 .r8 (.memi .r8 .rdx), 0x1021) := rfl
@[code_at] theorem at_1021 (T : BitVec 64) : prog T 0x1021 = some (.mov 8 (.mems .rsp .rcx 2 0xFFFFFFFFFFFFFFBC) (.reg .r8), 0x1026) := rfl
@[code_at] theorem at_1026 (T : BitVec 64) : prog T 0x1026 = some (.and 32 (.reg .rdi) (.imm 0xF), 0x1029) := rfl
@[code_at] theorem at_1029 (T : BitVec 64) : prog T 0x1029 = some (.movzx8 .rdi (.memi .rdi .rdx), 0x102D) := rfl
@[code_at] theorem at_102D (T : BitVec 64) : prog T 0x102D = some (.mov 8 (.mems .rsp .rcx 2 0xFFFFFFFFFFFFFFBD) (.reg .rdi), 0x1032) := rfl
@[code_at] theorem at_1032 (T : BitVec 64) : prog T 0x1032 = some (.movzx8 .rdi (.mems .rsi .rcx 1 0xFFFFFFFFFFFFFFFF), 0x1037) := rfl
@[code_at] theorem at_1037 (T : BitVec 64) : prog T 0x1037 = some (.mov 32 (.reg .r8) (.reg .rdi), 0x103A) := rfl
@[code_at] theorem at_103A (T : BitVec 64) : prog T 0x103A = some (.shr 32 (.reg .r8) 4, 0x103E) := rfl
@[code_at] theorem at_103E (T : BitVec 64) : prog T 0x103E = some (.movzx8 .r8 (.memi .r8 .rdx), 0x1043) := rfl
@[code_at] theorem at_1043 (T : BitVec 64) : prog T 0x1043 = some (.mov 8 (.mems .rsp .rcx 2 0xFFFFFFFFFFFFFFBE) (.reg .r8), 0x1048) := rfl
@[code_at] theorem at_1048 (T : BitVec 64) : prog T 0x1048 = some (.and 32 (.reg .rdi) (.imm 0xF), 0x104B) := rfl
@[code_at] theorem at_104B (T : BitVec 64) : prog T 0x104B = some (.movzx8 .rdi (.memi .rdi .rdx), 0x104F) := rfl
@[code_at] theorem at_104F (T : BitVec 64) : prog T 0x104F = some (.mov 8 (.mems .rsp .rcx 2 0xFFFFFFFFFFFFFFBF) (.reg .rdi), 0x1054) := rfl
@[code_at] theorem at_1054 (T : BitVec 64) : prog T 0x1054 = some (.add 64 (.reg .rcx) (.imm 0x2), 0x1058) := rfl
@[code_at] theorem at_1058 (T : BitVec 64) : prog T 0x1058 = some (.cmp 64 (.reg .rcx) (.imm 0x22), 0x105C) := rfl
@[code_at] theorem at_105C (T : BitVec 64) : prog T 0x105C = some (.jcc .ne 0x1010, 0x105E) := rfl
@[code_at] theorem at_105E (T : BitVec 64) : prog T 0x105E = some (.mov 32 (.mem .rsp 0xFFFFFFFFFFFFFFBC) (.imm 0x40), 0x1066) := rfl
@[code_at] theorem at_1066 (T : BitVec 64) : prog T 0x1066 = some (.mov 32 (.reg .rcx) (.mem .rsp 0xFFFFFFFFFFFFFFFC), 0x106A) := rfl
@[code_at] theorem at_106A (T : BitVec 64) : prog T 0x106A = some (.mov 32 (.mem .rax 0x40) (.reg .rcx), 0x106D) := rfl
@[code_at] theorem at_106D (T : BitVec 64) : prog T 0x106D = some (.loadv 0 (.mem .rsp 0xFFFFFFFFFFFFFFCC), 0x1072) := rfl
@[code_at] theorem at_1072 (T : BitVec 64) : prog T 0x1072 = some (.loadv 1 (.mem .rsp 0xFFFFFFFFFFFFFFDC), 0x1077) := rfl
@[code_at] theorem at_1077 (T : BitVec 64) : prog T 0x1077 = some (.loadv 2 (.mem .rsp 0xFFFFFFFFFFFFFFEC), 0x107C) := rfl
@[code_at] theorem at_107C (T : BitVec 64) : prog T 0x107C = some (.storev (.mem .rax 0x30) 2, 0x1080) := rfl
@[code_at] theorem at_1080 (T : BitVec 64) : prog T 0x1080 = some (.storev (.mem .rax 0x20) 1, 0x1084) := rfl
@[code_at] theorem at_1084 (T : BitVec 64) : prog T 0x1084 = some (.storev (.mem .rax 0x10) 0, 0x1088) := rfl
@[code_at] theorem at_1088 (T : BitVec 64) : prog T 0x1088 = some (.mov 32 (.reg .rcx) (.mem .rsp 0xFFFFFFFFFFFFFFBC), 0x108C) := rfl
@[code_at] theorem at_108C (T : BitVec 64) : prog T 0x108C = some (.mov 32 (.mem .rax 0x0) (.reg .rcx), 0x108E) := rfl
@[code_at] theorem at_108E (T : BitVec 64) : prog T 0x108E = some (.mov 64 (.reg .rcx) (.mem .rsp 0xFFFFFFFFFFFFFFC0), 0x1093) := rfl
@[code_at] theorem at_1093 (T : BitVec 64) : prog T 0x1093 = some (.mov 64 (.mem .rax 0x4) (.reg .rcx), 0x1097) := rfl
@[code_at] theorem at_1097 (T : BitVec 64) : prog T 0x1097 = some (.mov 32 (.reg .rcx) (.mem .rsp 0xFFFFFFFFFFFFFFC8), 0x109B) := rfl
@[code_at] theorem at_109B (T : BitVec 64) : prog T 0x109B = some (.mov 32 (.mem .rax 0xC) (.reg .rcx), 0x109E) := rfl
@[code_at] theorem at_109E (T : BitVec 64) : prog T 0x109E = some (.ret, 0x109F) := rfl

end Code
