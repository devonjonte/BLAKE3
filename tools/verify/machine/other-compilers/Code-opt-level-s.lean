import X86
import Attr

/-! The compiled functions, as llvm-objdump reads them. Written by lift.py; not edited by hand. -/

namespace Code
open X86

def table : List (Nat × Instr × Nat) := [
  -- _RNvNtCsbZEd7oTQFCq_13blake3_servil8platform17read_x86_features
  (0x1000, .push .rbx, 0x1001),  -- 53                       push rbx
  (0x1001, .sub 64 (.reg .rsp) (.imm 0x20), 0x1005),  -- 48 83 ec 20              sub rsp, 0x20
  (0x1005, .lea .rbx .rsp 0xC, 0x100A),  -- 48 8d 5c 24 0c           lea rbx, [rsp + 0xc]
  (0x100A, .mov 64 (.reg .rdi) (.reg .rbx), 0x100D),  -- 48 89 df                 mov rdi, rbx
  (0x100D, .call 0x2000, 0x1012),  -- e8 00 00 00 00           call 0x12 <_RNvNtCsbZEd7oTQFCq_13blake3_servil8platform17read_x86_features+0x12>
  (0x1012, .mov 32 (.reg .rax) (.mem .rbx 0x4), 0x1015),  -- 8b 43 04                 mov eax, dword ptr [rbx + 0x4]
  (0x1015, .mov 32 (.reg .rcx) (.reg .rax), 0x1017),  -- 89 c1                    mov ecx, eax
  (0x1017, .not 32 (.reg .rcx), 0x1019),  -- f7 d1                    not ecx
  (0x1019, .shr 32 (.reg .rax) 19, 0x101C),  -- c1 e8 13                 shr eax, 0x13
  (0x101C, .and 32 (.reg .rax) (.imm 0x1), 0x101F),  -- 83 e0 01                 and eax, 0x1
  (0x101F, .add 8 (.reg .rax) (.reg .rax), 0x1021),  -- 00 c0                    add al, al
  (0x1021, .or 8 (.reg .rax) (.imm 0xFFFFFFFFFFFFFF80), 0x1023),  -- 0c 80                    or al, -0x80
  (0x1023, .test 32 (.reg .rcx) (.imm 0x1C000000), 0x1029),  -- f7 c1 00 00 00 1c        test ecx, 0x1c000000
  (0x1029, .jcc .ne 0x1090, 0x102B),  -- 75 65                    jne 0x90 <_RNvNtCsbZEd7oTQFCq_13blake3_servil8platform17read_x86_features+0x90>
  (0x102B, .mov 32 (.reg .rcx) (.mem .rsp 0x14), 0x102F),  -- 8b 4c 24 14              mov ecx, dword ptr [rsp + 0x14]
  (0x102F, .mov 32 (.reg .rdx) (.mem .rsp 0x18), 0x1033),  -- 8b 54 24 18              mov edx, dword ptr [rsp + 0x18]
  (0x1033, .not 32 (.reg .rcx), 0x1035),  -- f7 d1                    not ecx
  (0x1035, .mov 32 (.reg .rsi) (.reg .rdx), 0x1037),  -- 89 d6                    mov esi, edx
  (0x1037, .shr 8 (.reg .rsi) 3, 0x103B),  -- 40 c0 ee 03              shr sil, 0x3
  (0x103B, .and 8 (.reg .rsi) (.imm 0x4), 0x103F),  -- 40 80 e6 04              and sil, 0x4
  (0x103F, .xor 32 (.reg .rdi) (.reg .rdi), 0x1041),  -- 31 ff                    xor edi, edi
  (0x1041, .test 8 (.reg .rcx) (.imm 0x6), 0x1044),  -- f6 c1 06                 test cl, 0x6
  (0x1044, .not 32 (.reg .rdx), 0x1046),  -- f7 d2                    not edx
  (0x1046, .movzx 8 .rsi (.reg .rsi), 0x104A),  -- 40 0f b6 f6              movzx esi, sil
  (0x104A, .cmovcc .ne .rsi (.reg .rdi), 0x104D),  -- 0f 45 f7                 cmovne esi, edi
  (0x104D, .or 8 (.reg .rax) (.reg .rsi), 0x1050),  -- 40 08 f0                 or al, sil
  (0x1050, .and 32 (.reg .rcx) (.imm 0xE6), 0x1056),  -- 81 e1 e6 00 00 00        and ecx, 0xe6
  (0x1056, .and 32 (.reg .rdx) (.imm 0x80010000), 0x105C),  -- 81 e2 00 00 01 80        and edx, 0x80010000
  (0x105C, .or 32 (.reg .rdx) (.reg .rcx), 0x105E),  -- 09 ca                    or edx, ecx
  (0x105E, .jcc .ne 0x1090, 0x1060),  -- 75 30                    jne 0x90 <_RNvNtCsbZEd7oTQFCq_13blake3_servil8platform17read_x86_features+0x90>
  (0x1060, .mov 32 (.reg .rcx) (.mem .rsp 0xC), 0x1064),  -- 8b 4c 24 0c              mov ecx, dword ptr [rsp + 0xc]
  (0x1064, .mov 32 (.reg .rdx) (.reg .rcx), 0x1066),  -- 89 ca                    mov edx, ecx
  (0x1066, .not 32 (.reg .rdx), 0x1068),  -- f7 d2                    not edx
  (0x1068, .test 32 (.reg .rdx) (.imm 0xF00), 0x106E),  -- f7 c2 00 0f 00 00        test edx, 0xf00
  (0x106E, .setcc .e (.reg .rdx), 0x1071),  -- 0f 94 c2                 sete dl
  (0x1071, .and 32 (.reg .rcx) (.imm 0xFF00000), 0x1077),  -- 81 e1 00 00 f0 0f        and ecx, 0xff00000
  (0x1077, .cmp 32 (.reg .rcx) (.imm 0xA00001), 0x107D),  -- 81 f9 01 00 a0 00        cmp ecx, 0xa00001
  (0x107D, .setcc .ae (.reg .rcx), 0x1080),  -- 0f 93 c1                 setae cl
  (0x1080, .and 8 (.reg .rdx) (.mem .rsp 0x1C), 0x1084),  -- 22 54 24 1c              and dl, byte ptr [rsp + 0x1c]
  (0x1084, .and 8 (.reg .rdx) (.reg .rcx), 0x1086),  -- 20 ca                    and dl, cl
  (0x1086, .shl 8 (.reg .rdx) 4, 0x1089),  -- c0 e2 04                 shl dl, 0x4
  (0x1089, .or 8 (.reg .rdx) (.reg .rax), 0x108B),  -- 08 c2                    or dl, al
  (0x108B, .or 8 (.reg .rdx) (.imm 0x8), 0x108E),  -- 80 ca 08                 or dl, 0x8
  (0x108E, .mov 32 (.reg .rax) (.reg .rdx), 0x1090),  -- 89 d0                    mov eax, edx
  (0x1090, .add 64 (.reg .rsp) (.imm 0x20), 0x1094),  -- 48 83 c4 20              add rsp, 0x20
  (0x1094, .pop .rbx, 0x1095),  -- 5b                       pop rbx
  (0x1095, .ret, 0x1096),  -- c3                       ret 
  -- _RNvNtCsbZEd7oTQFCq_13blake3_servil8platform14read_cpu_words.llvm.18339046496416464044
  (0x2000, .push .rbx, 0x2001),  -- 53                       push rbx
  (0x2001, .mov 64 (.reg .rbx) (.reg .rdi), 0x2004),  -- 48 89 fb                 mov rbx, rdi
  (0x2004, .xor 32 (.reg .rcx) (.reg .rcx), 0x2006),  -- 31 c9                    xor ecx, ecx
  (0x2006, .mov 32 (.reg .rax) (.imm 0x1), 0x200B),  -- b8 01 00 00 00           mov eax, 0x1
  (0x200B, .mov 64 (.reg .rsi) (.reg .rbx), 0x200E),  -- 48 89 de                 mov rsi, rbx
  (0x200E, .cpuid, 0x2010),  -- 0f a2                    cpuid 
  (0x2010, .xchg .rsi .rbx, 0x2013),  -- 48 87 f3                 xchg rsi, rbx
  (0x2013, .mov 32 (.mem .rdi 0x0) (.reg .rax), 0x2015),  -- 89 07                    mov dword ptr [rdi], eax
  (0x2015, .mov 32 (.mem .rdi 0x4) (.reg .rcx), 0x2018),  -- 89 4f 04                 mov dword ptr [rdi + 0x4], ecx
  (0x2018, .not 32 (.reg .rcx), 0x201A),  -- f7 d1                    not ecx
  (0x201A, .mov 64 (.mem .rdi 0x8) (.imm 0x0), 0x2022),  -- 48 c7 47 08 00 00 00 00  mov qword ptr [rdi + 0x8], 0x0
  (0x2022, .mov 8 (.mem .rdi 0x10) (.imm 0x0), 0x2026),  -- c6 47 10 00              mov byte ptr [rdi + 0x10], 0x0
  (0x2026, .test 32 (.reg .rcx) (.imm 0x1C000000), 0x202C),  -- f7 c1 00 00 00 1c        test ecx, 0x1c000000
  (0x202C, .jcc .ne 0x206E, 0x202E),  -- 75 40                    jne 0x6e <_RNvNtCsbZEd7oTQFCq_13blake3_servil8platform14read_cpu_words.llvm.18339046496416464044+0x6e>
  (0x202E, .call 0x3000, 0x2033),  -- e8 00 00 00 00           call 0x33 <_RNvNtCsbZEd7oTQFCq_13blake3_servil8platform14read_cpu_words.llvm.18339046496416464044+0x33>
  (0x2033, .mov 32 (.mem .rbx 0x8) (.reg .rax), 0x2036),  -- 89 43 08                 mov dword ptr [rbx + 0x8], eax
  (0x2036, .mov 32 (.reg .rax) (.imm 0x7), 0x203B),  -- b8 07 00 00 00           mov eax, 0x7
  (0x203B, .xor 32 (.reg .rcx) (.reg .rcx), 0x203D),  -- 31 c9                    xor ecx, ecx
  (0x203D, .mov 64 (.reg .rsi) (.reg .rbx), 0x2040),  -- 48 89 de                 mov rsi, rbx
  (0x2040, .cpuid, 0x2042),  -- 0f a2                    cpuid 
  (0x2042, .xchg .rsi .rbx, 0x2045),  -- 48 87 f3                 xchg rsi, rbx
  (0x2045, .xor 32 (.reg .rcx) (.reg .rcx), 0x2047),  -- 31 c9                    xor ecx, ecx
  (0x2047, .xor 32 (.reg .rax) (.reg .rax), 0x2049),  -- 31 c0                    xor eax, eax
  (0x2049, .mov 64 (.reg .rdi) (.reg .rbx), 0x204C),  -- 48 89 df                 mov rdi, rbx
  (0x204C, .cpuid, 0x204E),  -- 0f a2                    cpuid 
  (0x204E, .xchg .rdi .rbx, 0x2051),  -- 48 87 fb                 xchg rdi, rbx
  (0x2051, .mov 32 (.mem .rbx 0xC) (.reg .rsi), 0x2054),  -- 89 73 0c                 mov dword ptr [rbx + 0xc], esi
  (0x2054, .xor 32 (.reg .rdi) (.imm 0x68747541), 0x205A),  -- 81 f7 41 75 74 68        xor edi, 0x68747541
  (0x205A, .xor 32 (.reg .rdx) (.imm 0x69746E65), 0x2060),  -- 81 f2 65 6e 74 69        xor edx, 0x69746e65
  (0x2060, .or 32 (.reg .rdx) (.reg .rdi), 0x2062),  -- 09 fa                    or edx, edi
  (0x2062, .xor 32 (.reg .rcx) (.imm 0x444D4163), 0x2068),  -- 81 f1 63 41 4d 44        xor ecx, 0x444d4163
  (0x2068, .or 32 (.reg .rcx) (.reg .rdx), 0x206A),  -- 09 d1                    or ecx, edx
  (0x206A, .setcc .e (.mem .rbx 0x10), 0x206E),  -- 0f 94 43 10              sete byte ptr [rbx + 0x10]
  (0x206E, .mov 64 (.reg .rax) (.reg .rbx), 0x2071),  -- 48 89 d8                 mov rax, rbx
  (0x2071, .pop .rbx, 0x2072),  -- 5b                       pop rbx
  (0x2072, .ret, 0x2073),  -- c3                       ret 
  -- _RNvNtNtNtCskADBYZwJmSU_4core9core_arch3x865xsave7__xgetbv.llvm.18339046496416464044
  (0x3000, .xor 32 (.reg .rcx) (.reg .rcx), 0x3002),  -- 31 c9                    xor ecx, ecx
  (0x3002, .xgetbv, 0x3005),  -- 0f 01 d0                 xgetbv 
  (0x3005, .shl 64 (.reg .rdx) 32, 0x3009),  -- 48 c1 e2 20              shl rdx, 0x20
  (0x3009, .or 64 (.reg .rax) (.reg .rdx), 0x300C),  -- 48 09 d0                 or rax, rdx
  (0x300C, .ret, 0x300D)   -- c3                       ret 
]

/-- The instruction at an address, and the address after it. -/
def prog (pc : Nat) : Option (Instr × Nat) := table.lookup pc

@[code_at] theorem at_1000 : prog 0x1000 = some (.push .rbx, 0x1001) := rfl
@[code_at] theorem at_1001 : prog 0x1001 = some (.sub 64 (.reg .rsp) (.imm 0x20), 0x1005) := rfl
@[code_at] theorem at_1005 : prog 0x1005 = some (.lea .rbx .rsp 0xC, 0x100A) := rfl
@[code_at] theorem at_100A : prog 0x100A = some (.mov 64 (.reg .rdi) (.reg .rbx), 0x100D) := rfl
@[code_at] theorem at_100D : prog 0x100D = some (.call 0x2000, 0x1012) := rfl
@[code_at] theorem at_1012 : prog 0x1012 = some (.mov 32 (.reg .rax) (.mem .rbx 0x4), 0x1015) := rfl
@[code_at] theorem at_1015 : prog 0x1015 = some (.mov 32 (.reg .rcx) (.reg .rax), 0x1017) := rfl
@[code_at] theorem at_1017 : prog 0x1017 = some (.not 32 (.reg .rcx), 0x1019) := rfl
@[code_at] theorem at_1019 : prog 0x1019 = some (.shr 32 (.reg .rax) 19, 0x101C) := rfl
@[code_at] theorem at_101C : prog 0x101C = some (.and 32 (.reg .rax) (.imm 0x1), 0x101F) := rfl
@[code_at] theorem at_101F : prog 0x101F = some (.add 8 (.reg .rax) (.reg .rax), 0x1021) := rfl
@[code_at] theorem at_1021 : prog 0x1021 = some (.or 8 (.reg .rax) (.imm 0xFFFFFFFFFFFFFF80), 0x1023) := rfl
@[code_at] theorem at_1023 : prog 0x1023 = some (.test 32 (.reg .rcx) (.imm 0x1C000000), 0x1029) := rfl
@[code_at] theorem at_1029 : prog 0x1029 = some (.jcc .ne 0x1090, 0x102B) := rfl
@[code_at] theorem at_102B : prog 0x102B = some (.mov 32 (.reg .rcx) (.mem .rsp 0x14), 0x102F) := rfl
@[code_at] theorem at_102F : prog 0x102F = some (.mov 32 (.reg .rdx) (.mem .rsp 0x18), 0x1033) := rfl
@[code_at] theorem at_1033 : prog 0x1033 = some (.not 32 (.reg .rcx), 0x1035) := rfl
@[code_at] theorem at_1035 : prog 0x1035 = some (.mov 32 (.reg .rsi) (.reg .rdx), 0x1037) := rfl
@[code_at] theorem at_1037 : prog 0x1037 = some (.shr 8 (.reg .rsi) 3, 0x103B) := rfl
@[code_at] theorem at_103B : prog 0x103B = some (.and 8 (.reg .rsi) (.imm 0x4), 0x103F) := rfl
@[code_at] theorem at_103F : prog 0x103F = some (.xor 32 (.reg .rdi) (.reg .rdi), 0x1041) := rfl
@[code_at] theorem at_1041 : prog 0x1041 = some (.test 8 (.reg .rcx) (.imm 0x6), 0x1044) := rfl
@[code_at] theorem at_1044 : prog 0x1044 = some (.not 32 (.reg .rdx), 0x1046) := rfl
@[code_at] theorem at_1046 : prog 0x1046 = some (.movzx 8 .rsi (.reg .rsi), 0x104A) := rfl
@[code_at] theorem at_104A : prog 0x104A = some (.cmovcc .ne .rsi (.reg .rdi), 0x104D) := rfl
@[code_at] theorem at_104D : prog 0x104D = some (.or 8 (.reg .rax) (.reg .rsi), 0x1050) := rfl
@[code_at] theorem at_1050 : prog 0x1050 = some (.and 32 (.reg .rcx) (.imm 0xE6), 0x1056) := rfl
@[code_at] theorem at_1056 : prog 0x1056 = some (.and 32 (.reg .rdx) (.imm 0x80010000), 0x105C) := rfl
@[code_at] theorem at_105C : prog 0x105C = some (.or 32 (.reg .rdx) (.reg .rcx), 0x105E) := rfl
@[code_at] theorem at_105E : prog 0x105E = some (.jcc .ne 0x1090, 0x1060) := rfl
@[code_at] theorem at_1060 : prog 0x1060 = some (.mov 32 (.reg .rcx) (.mem .rsp 0xC), 0x1064) := rfl
@[code_at] theorem at_1064 : prog 0x1064 = some (.mov 32 (.reg .rdx) (.reg .rcx), 0x1066) := rfl
@[code_at] theorem at_1066 : prog 0x1066 = some (.not 32 (.reg .rdx), 0x1068) := rfl
@[code_at] theorem at_1068 : prog 0x1068 = some (.test 32 (.reg .rdx) (.imm 0xF00), 0x106E) := rfl
@[code_at] theorem at_106E : prog 0x106E = some (.setcc .e (.reg .rdx), 0x1071) := rfl
@[code_at] theorem at_1071 : prog 0x1071 = some (.and 32 (.reg .rcx) (.imm 0xFF00000), 0x1077) := rfl
@[code_at] theorem at_1077 : prog 0x1077 = some (.cmp 32 (.reg .rcx) (.imm 0xA00001), 0x107D) := rfl
@[code_at] theorem at_107D : prog 0x107D = some (.setcc .ae (.reg .rcx), 0x1080) := rfl
@[code_at] theorem at_1080 : prog 0x1080 = some (.and 8 (.reg .rdx) (.mem .rsp 0x1C), 0x1084) := rfl
@[code_at] theorem at_1084 : prog 0x1084 = some (.and 8 (.reg .rdx) (.reg .rcx), 0x1086) := rfl
@[code_at] theorem at_1086 : prog 0x1086 = some (.shl 8 (.reg .rdx) 4, 0x1089) := rfl
@[code_at] theorem at_1089 : prog 0x1089 = some (.or 8 (.reg .rdx) (.reg .rax), 0x108B) := rfl
@[code_at] theorem at_108B : prog 0x108B = some (.or 8 (.reg .rdx) (.imm 0x8), 0x108E) := rfl
@[code_at] theorem at_108E : prog 0x108E = some (.mov 32 (.reg .rax) (.reg .rdx), 0x1090) := rfl
@[code_at] theorem at_1090 : prog 0x1090 = some (.add 64 (.reg .rsp) (.imm 0x20), 0x1094) := rfl
@[code_at] theorem at_1094 : prog 0x1094 = some (.pop .rbx, 0x1095) := rfl
@[code_at] theorem at_1095 : prog 0x1095 = some (.ret, 0x1096) := rfl
@[code_at] theorem at_2000 : prog 0x2000 = some (.push .rbx, 0x2001) := rfl
@[code_at] theorem at_2001 : prog 0x2001 = some (.mov 64 (.reg .rbx) (.reg .rdi), 0x2004) := rfl
@[code_at] theorem at_2004 : prog 0x2004 = some (.xor 32 (.reg .rcx) (.reg .rcx), 0x2006) := rfl
@[code_at] theorem at_2006 : prog 0x2006 = some (.mov 32 (.reg .rax) (.imm 0x1), 0x200B) := rfl
@[code_at] theorem at_200B : prog 0x200B = some (.mov 64 (.reg .rsi) (.reg .rbx), 0x200E) := rfl
@[code_at] theorem at_200E : prog 0x200E = some (.cpuid, 0x2010) := rfl
@[code_at] theorem at_2010 : prog 0x2010 = some (.xchg .rsi .rbx, 0x2013) := rfl
@[code_at] theorem at_2013 : prog 0x2013 = some (.mov 32 (.mem .rdi 0x0) (.reg .rax), 0x2015) := rfl
@[code_at] theorem at_2015 : prog 0x2015 = some (.mov 32 (.mem .rdi 0x4) (.reg .rcx), 0x2018) := rfl
@[code_at] theorem at_2018 : prog 0x2018 = some (.not 32 (.reg .rcx), 0x201A) := rfl
@[code_at] theorem at_201A : prog 0x201A = some (.mov 64 (.mem .rdi 0x8) (.imm 0x0), 0x2022) := rfl
@[code_at] theorem at_2022 : prog 0x2022 = some (.mov 8 (.mem .rdi 0x10) (.imm 0x0), 0x2026) := rfl
@[code_at] theorem at_2026 : prog 0x2026 = some (.test 32 (.reg .rcx) (.imm 0x1C000000), 0x202C) := rfl
@[code_at] theorem at_202C : prog 0x202C = some (.jcc .ne 0x206E, 0x202E) := rfl
@[code_at] theorem at_202E : prog 0x202E = some (.call 0x3000, 0x2033) := rfl
@[code_at] theorem at_2033 : prog 0x2033 = some (.mov 32 (.mem .rbx 0x8) (.reg .rax), 0x2036) := rfl
@[code_at] theorem at_2036 : prog 0x2036 = some (.mov 32 (.reg .rax) (.imm 0x7), 0x203B) := rfl
@[code_at] theorem at_203B : prog 0x203B = some (.xor 32 (.reg .rcx) (.reg .rcx), 0x203D) := rfl
@[code_at] theorem at_203D : prog 0x203D = some (.mov 64 (.reg .rsi) (.reg .rbx), 0x2040) := rfl
@[code_at] theorem at_2040 : prog 0x2040 = some (.cpuid, 0x2042) := rfl
@[code_at] theorem at_2042 : prog 0x2042 = some (.xchg .rsi .rbx, 0x2045) := rfl
@[code_at] theorem at_2045 : prog 0x2045 = some (.xor 32 (.reg .rcx) (.reg .rcx), 0x2047) := rfl
@[code_at] theorem at_2047 : prog 0x2047 = some (.xor 32 (.reg .rax) (.reg .rax), 0x2049) := rfl
@[code_at] theorem at_2049 : prog 0x2049 = some (.mov 64 (.reg .rdi) (.reg .rbx), 0x204C) := rfl
@[code_at] theorem at_204C : prog 0x204C = some (.cpuid, 0x204E) := rfl
@[code_at] theorem at_204E : prog 0x204E = some (.xchg .rdi .rbx, 0x2051) := rfl
@[code_at] theorem at_2051 : prog 0x2051 = some (.mov 32 (.mem .rbx 0xC) (.reg .rsi), 0x2054) := rfl
@[code_at] theorem at_2054 : prog 0x2054 = some (.xor 32 (.reg .rdi) (.imm 0x68747541), 0x205A) := rfl
@[code_at] theorem at_205A : prog 0x205A = some (.xor 32 (.reg .rdx) (.imm 0x69746E65), 0x2060) := rfl
@[code_at] theorem at_2060 : prog 0x2060 = some (.or 32 (.reg .rdx) (.reg .rdi), 0x2062) := rfl
@[code_at] theorem at_2062 : prog 0x2062 = some (.xor 32 (.reg .rcx) (.imm 0x444D4163), 0x2068) := rfl
@[code_at] theorem at_2068 : prog 0x2068 = some (.or 32 (.reg .rcx) (.reg .rdx), 0x206A) := rfl
@[code_at] theorem at_206A : prog 0x206A = some (.setcc .e (.mem .rbx 0x10), 0x206E) := rfl
@[code_at] theorem at_206E : prog 0x206E = some (.mov 64 (.reg .rax) (.reg .rbx), 0x2071) := rfl
@[code_at] theorem at_2071 : prog 0x2071 = some (.pop .rbx, 0x2072) := rfl
@[code_at] theorem at_2072 : prog 0x2072 = some (.ret, 0x2073) := rfl
@[code_at] theorem at_3000 : prog 0x3000 = some (.xor 32 (.reg .rcx) (.reg .rcx), 0x3002) := rfl
@[code_at] theorem at_3002 : prog 0x3002 = some (.xgetbv, 0x3005) := rfl
@[code_at] theorem at_3005 : prog 0x3005 = some (.shl 64 (.reg .rdx) 32, 0x3009) := rfl
@[code_at] theorem at_3009 : prog 0x3009 = some (.or 64 (.reg .rax) (.reg .rdx), 0x300C) := rfl
@[code_at] theorem at_300C : prog 0x300C = some (.ret, 0x300D) := rfl

end Code
