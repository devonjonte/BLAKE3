import X86

/-! The compiled functions, as llvm-objdump reads them. Written by lift.py; not edited by hand. -/

namespace Code
open X86

def table : List (Nat × Instr × Nat) := [
  -- _RNvNtCsiEO6tG4yVoJ_13blake3_servil8platform17read_x86_features
  (0x1000, .sub 64 (.reg .rsp) (.imm 0x18), 0x1004),  -- 48 83 ec 18              sub rsp, 0x18
  (0x1004, .lea .rdi .rsp 0x4, 0x1009),  -- 48 8d 7c 24 04           lea rdi, [rsp + 0x4]
  (0x1009, .call 0x2000, 0x100E),  -- e8 00 00 00 00           call 0xe <_RNvNtCsiEO6tG4yVoJ_13blake3_servil8platform17read_x86_features+0xe>
  (0x100E, .mov 32 (.reg .rax) (.mem .rsp 0x8), 0x1012),  -- 8b 44 24 08              mov eax, dword ptr [rsp + 0x8]
  (0x1012, .mov 32 (.reg .rcx) (.reg .rax), 0x1014),  -- 89 c1                    mov ecx, eax
  (0x1014, .not 32 (.reg .rcx), 0x1016),  -- f7 d1                    not ecx
  (0x1016, .shr 32 (.reg .rax) 19, 0x1019),  -- c1 e8 13                 shr eax, 0x13
  (0x1019, .and 32 (.reg .rax) (.imm 0x1), 0x101C),  -- 83 e0 01                 and eax, 0x1
  (0x101C, .add 8 (.reg .rax) (.reg .rax), 0x101E),  -- 00 c0                    add al, al
  (0x101E, .or 8 (.reg .rax) (.imm 0xFFFFFFFFFFFFFF80), 0x1020),  -- 0c 80                    or al, -0x80
  (0x1020, .test 32 (.reg .rcx) (.imm 0x1C000000), 0x1026),  -- f7 c1 00 00 00 1c        test ecx, 0x1c000000
  (0x1026, .jcc .ne 0x108D, 0x1028),  -- 75 65                    jne 0x8d <_RNvNtCsiEO6tG4yVoJ_13blake3_servil8platform17read_x86_features+0x8d>
  (0x1028, .mov 32 (.reg .rcx) (.mem .rsp 0xC), 0x102C),  -- 8b 4c 24 0c              mov ecx, dword ptr [rsp + 0xc]
  (0x102C, .mov 32 (.reg .rdx) (.mem .rsp 0x10), 0x1030),  -- 8b 54 24 10              mov edx, dword ptr [rsp + 0x10]
  (0x1030, .not 32 (.reg .rcx), 0x1032),  -- f7 d1                    not ecx
  (0x1032, .mov 32 (.reg .rsi) (.reg .rdx), 0x1034),  -- 89 d6                    mov esi, edx
  (0x1034, .shr 8 (.reg .rsi) 3, 0x1038),  -- 40 c0 ee 03              shr sil, 0x3
  (0x1038, .and 8 (.reg .rsi) (.imm 0x4), 0x103C),  -- 40 80 e6 04              and sil, 0x4
  (0x103C, .xor 32 (.reg .rdi) (.reg .rdi), 0x103E),  -- 31 ff                    xor edi, edi
  (0x103E, .test 8 (.reg .rcx) (.imm 0x6), 0x1041),  -- f6 c1 06                 test cl, 0x6
  (0x1041, .not 32 (.reg .rdx), 0x1043),  -- f7 d2                    not edx
  (0x1043, .movzx 8 .rsi (.reg .rsi), 0x1047),  -- 40 0f b6 f6              movzx esi, sil
  (0x1047, .cmovcc .ne .rsi (.reg .rdi), 0x104A),  -- 0f 45 f7                 cmovne esi, edi
  (0x104A, .or 8 (.reg .rax) (.reg .rsi), 0x104D),  -- 40 08 f0                 or al, sil
  (0x104D, .and 32 (.reg .rcx) (.imm 0xE6), 0x1053),  -- 81 e1 e6 00 00 00        and ecx, 0xe6
  (0x1053, .and 32 (.reg .rdx) (.imm 0x80010000), 0x1059),  -- 81 e2 00 00 01 80        and edx, 0x80010000
  (0x1059, .or 32 (.reg .rdx) (.reg .rcx), 0x105B),  -- 09 ca                    or edx, ecx
  (0x105B, .jcc .ne 0x108D, 0x105D),  -- 75 30                    jne 0x8d <_RNvNtCsiEO6tG4yVoJ_13blake3_servil8platform17read_x86_features+0x8d>
  (0x105D, .mov 32 (.reg .rcx) (.mem .rsp 0x4), 0x1061),  -- 8b 4c 24 04              mov ecx, dword ptr [rsp + 0x4]
  (0x1061, .mov 32 (.reg .rdx) (.reg .rcx), 0x1063),  -- 89 ca                    mov edx, ecx
  (0x1063, .not 32 (.reg .rdx), 0x1065),  -- f7 d2                    not edx
  (0x1065, .test 32 (.reg .rdx) (.imm 0xF00), 0x106B),  -- f7 c2 00 0f 00 00        test edx, 0xf00
  (0x106B, .setcc .e (.reg .rdx), 0x106E),  -- 0f 94 c2                 sete dl
  (0x106E, .and 32 (.reg .rcx) (.imm 0xFF00000), 0x1074),  -- 81 e1 00 00 f0 0f        and ecx, 0xff00000
  (0x1074, .cmp 32 (.reg .rcx) (.imm 0xA00001), 0x107A),  -- 81 f9 01 00 a0 00        cmp ecx, 0xa00001
  (0x107A, .setcc .ae (.reg .rcx), 0x107D),  -- 0f 93 c1                 setae cl
  (0x107D, .and 8 (.reg .rdx) (.mem .rsp 0x14), 0x1081),  -- 22 54 24 14              and dl, byte ptr [rsp + 0x14]
  (0x1081, .and 8 (.reg .rdx) (.reg .rcx), 0x1083),  -- 20 ca                    and dl, cl
  (0x1083, .shl 8 (.reg .rdx) 4, 0x1086),  -- c0 e2 04                 shl dl, 0x4
  (0x1086, .or 8 (.reg .rdx) (.reg .rax), 0x1088),  -- 08 c2                    or dl, al
  (0x1088, .or 8 (.reg .rdx) (.imm 0x8), 0x108B),  -- 80 ca 08                 or dl, 0x8
  (0x108B, .mov 32 (.reg .rax) (.reg .rdx), 0x108D),  -- 89 d0                    mov eax, edx
  (0x108D, .add 64 (.reg .rsp) (.imm 0x18), 0x1091),  -- 48 83 c4 18              add rsp, 0x18
  (0x1091, .ret, 0x1092),  -- c3                       ret 
  -- _RNvNtCsiEO6tG4yVoJ_13blake3_servil8platform14read_cpu_words.llvm.17597660332881744898
  (0x2000, .mov 32 (.reg .rax) (.imm 0x1), 0x2005),  -- b8 01 00 00 00           mov eax, 0x1
  (0x2005, .xor 32 (.reg .rcx) (.reg .rcx), 0x2007),  -- 31 c9                    xor ecx, ecx
  (0x2007, .mov 64 (.reg .rsi) (.reg .rbx), 0x200A),  -- 48 89 de                 mov rsi, rbx
  (0x200A, .cpuid, 0x200C),  -- 0f a2                    cpuid 
  (0x200C, .xchg .rsi .rbx, 0x200F),  -- 48 87 f3                 xchg rsi, rbx
  (0x200F, .mov 32 (.mem .rdi 0x0) (.reg .rax), 0x2011),  -- 89 07                    mov dword ptr [rdi], eax
  (0x2011, .mov 32 (.mem .rdi 0x4) (.reg .rcx), 0x2014),  -- 89 4f 04                 mov dword ptr [rdi + 0x4], ecx
  (0x2014, .not 32 (.reg .rcx), 0x2016),  -- f7 d1                    not ecx
  (0x2016, .mov 64 (.mem .rdi 0x8) (.imm 0x0), 0x201E),  -- 48 c7 47 08 00 00 00 00  mov qword ptr [rdi + 0x8], 0x0
  (0x201E, .mov 8 (.mem .rdi 0x10) (.imm 0x0), 0x2022),  -- c6 47 10 00              mov byte ptr [rdi + 0x10], 0x0
  (0x2022, .test 32 (.reg .rcx) (.imm 0x1C000000), 0x2028),  -- f7 c1 00 00 00 1c        test ecx, 0x1c000000
  (0x2028, .jcc .ne 0x206F, 0x202A),  -- 75 45                    jne 0x6f <_RNvNtCsiEO6tG4yVoJ_13blake3_servil8platform14read_cpu_words.llvm.17597660332881744898+0x6f>
  (0x202A, .push .rbx, 0x202B),  -- 53                       push rbx
  (0x202B, .mov 64 (.reg .rbx) (.reg .rdi), 0x202E),  -- 48 89 fb                 mov rbx, rdi
  (0x202E, .call 0x3000, 0x2033),  -- e8 00 00 00 00           call 0x33 <_RNvNtCsiEO6tG4yVoJ_13blake3_servil8platform14read_cpu_words.llvm.17597660332881744898+0x33>
  (0x2033, .mov 32 (.mem .rbx 0x8) (.reg .rax), 0x2036),  -- 89 43 08                 mov dword ptr [rbx + 0x8], eax
  (0x2036, .mov 32 (.reg .rax) (.imm 0x7), 0x203B),  -- b8 07 00 00 00           mov eax, 0x7
  (0x203B, .xor 32 (.reg .rcx) (.reg .rcx), 0x203D),  -- 31 c9                    xor ecx, ecx
  (0x203D, .mov 64 (.reg .rsi) (.reg .rbx), 0x2040),  -- 48 89 de                 mov rsi, rbx
  (0x2040, .cpuid, 0x2042),  -- 0f a2                    cpuid 
  (0x2042, .xchg .rsi .rbx, 0x2045),  -- 48 87 f3                 xchg rsi, rbx
  (0x2045, .xor 32 (.reg .rax) (.reg .rax), 0x2047),  -- 31 c0                    xor eax, eax
  (0x2047, .xor 32 (.reg .rcx) (.reg .rcx), 0x2049),  -- 31 c9                    xor ecx, ecx
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
  (0x206E, .pop .rbx, 0x206F),  -- 5b                       pop rbx
  (0x206F, .ret, 0x2070),  -- c3                       ret 
  -- _RNvNtNtNtCskADBYZwJmSU_4core9core_arch3x865xsave7__xgetbv.llvm.17597660332881744898
  (0x3000, .xor 32 (.reg .rcx) (.reg .rcx), 0x3002),  -- 31 c9                    xor ecx, ecx
  (0x3002, .xgetbv, 0x3005),  -- 0f 01 d0                 xgetbv 
  (0x3005, .shl 64 (.reg .rdx) 32, 0x3009),  -- 48 c1 e2 20              shl rdx, 0x20
  (0x3009, .or 64 (.reg .rax) (.reg .rdx), 0x300C),  -- 48 09 d0                 or rax, rdx
  (0x300C, .ret, 0x300D)   -- c3                       ret 
]

/-- The instruction at an address, and the address after it. -/
def prog (pc : Nat) : Option (Instr × Nat) := table.lookup pc

@[simp] theorem at_1000 : prog 0x1000 = some (.sub 64 (.reg .rsp) (.imm 0x18), 0x1004) := rfl
@[simp] theorem at_1004 : prog 0x1004 = some (.lea .rdi .rsp 0x4, 0x1009) := rfl
@[simp] theorem at_1009 : prog 0x1009 = some (.call 0x2000, 0x100E) := rfl
@[simp] theorem at_100E : prog 0x100E = some (.mov 32 (.reg .rax) (.mem .rsp 0x8), 0x1012) := rfl
@[simp] theorem at_1012 : prog 0x1012 = some (.mov 32 (.reg .rcx) (.reg .rax), 0x1014) := rfl
@[simp] theorem at_1014 : prog 0x1014 = some (.not 32 (.reg .rcx), 0x1016) := rfl
@[simp] theorem at_1016 : prog 0x1016 = some (.shr 32 (.reg .rax) 19, 0x1019) := rfl
@[simp] theorem at_1019 : prog 0x1019 = some (.and 32 (.reg .rax) (.imm 0x1), 0x101C) := rfl
@[simp] theorem at_101C : prog 0x101C = some (.add 8 (.reg .rax) (.reg .rax), 0x101E) := rfl
@[simp] theorem at_101E : prog 0x101E = some (.or 8 (.reg .rax) (.imm 0xFFFFFFFFFFFFFF80), 0x1020) := rfl
@[simp] theorem at_1020 : prog 0x1020 = some (.test 32 (.reg .rcx) (.imm 0x1C000000), 0x1026) := rfl
@[simp] theorem at_1026 : prog 0x1026 = some (.jcc .ne 0x108D, 0x1028) := rfl
@[simp] theorem at_1028 : prog 0x1028 = some (.mov 32 (.reg .rcx) (.mem .rsp 0xC), 0x102C) := rfl
@[simp] theorem at_102C : prog 0x102C = some (.mov 32 (.reg .rdx) (.mem .rsp 0x10), 0x1030) := rfl
@[simp] theorem at_1030 : prog 0x1030 = some (.not 32 (.reg .rcx), 0x1032) := rfl
@[simp] theorem at_1032 : prog 0x1032 = some (.mov 32 (.reg .rsi) (.reg .rdx), 0x1034) := rfl
@[simp] theorem at_1034 : prog 0x1034 = some (.shr 8 (.reg .rsi) 3, 0x1038) := rfl
@[simp] theorem at_1038 : prog 0x1038 = some (.and 8 (.reg .rsi) (.imm 0x4), 0x103C) := rfl
@[simp] theorem at_103C : prog 0x103C = some (.xor 32 (.reg .rdi) (.reg .rdi), 0x103E) := rfl
@[simp] theorem at_103E : prog 0x103E = some (.test 8 (.reg .rcx) (.imm 0x6), 0x1041) := rfl
@[simp] theorem at_1041 : prog 0x1041 = some (.not 32 (.reg .rdx), 0x1043) := rfl
@[simp] theorem at_1043 : prog 0x1043 = some (.movzx 8 .rsi (.reg .rsi), 0x1047) := rfl
@[simp] theorem at_1047 : prog 0x1047 = some (.cmovcc .ne .rsi (.reg .rdi), 0x104A) := rfl
@[simp] theorem at_104A : prog 0x104A = some (.or 8 (.reg .rax) (.reg .rsi), 0x104D) := rfl
@[simp] theorem at_104D : prog 0x104D = some (.and 32 (.reg .rcx) (.imm 0xE6), 0x1053) := rfl
@[simp] theorem at_1053 : prog 0x1053 = some (.and 32 (.reg .rdx) (.imm 0x80010000), 0x1059) := rfl
@[simp] theorem at_1059 : prog 0x1059 = some (.or 32 (.reg .rdx) (.reg .rcx), 0x105B) := rfl
@[simp] theorem at_105B : prog 0x105B = some (.jcc .ne 0x108D, 0x105D) := rfl
@[simp] theorem at_105D : prog 0x105D = some (.mov 32 (.reg .rcx) (.mem .rsp 0x4), 0x1061) := rfl
@[simp] theorem at_1061 : prog 0x1061 = some (.mov 32 (.reg .rdx) (.reg .rcx), 0x1063) := rfl
@[simp] theorem at_1063 : prog 0x1063 = some (.not 32 (.reg .rdx), 0x1065) := rfl
@[simp] theorem at_1065 : prog 0x1065 = some (.test 32 (.reg .rdx) (.imm 0xF00), 0x106B) := rfl
@[simp] theorem at_106B : prog 0x106B = some (.setcc .e (.reg .rdx), 0x106E) := rfl
@[simp] theorem at_106E : prog 0x106E = some (.and 32 (.reg .rcx) (.imm 0xFF00000), 0x1074) := rfl
@[simp] theorem at_1074 : prog 0x1074 = some (.cmp 32 (.reg .rcx) (.imm 0xA00001), 0x107A) := rfl
@[simp] theorem at_107A : prog 0x107A = some (.setcc .ae (.reg .rcx), 0x107D) := rfl
@[simp] theorem at_107D : prog 0x107D = some (.and 8 (.reg .rdx) (.mem .rsp 0x14), 0x1081) := rfl
@[simp] theorem at_1081 : prog 0x1081 = some (.and 8 (.reg .rdx) (.reg .rcx), 0x1083) := rfl
@[simp] theorem at_1083 : prog 0x1083 = some (.shl 8 (.reg .rdx) 4, 0x1086) := rfl
@[simp] theorem at_1086 : prog 0x1086 = some (.or 8 (.reg .rdx) (.reg .rax), 0x1088) := rfl
@[simp] theorem at_1088 : prog 0x1088 = some (.or 8 (.reg .rdx) (.imm 0x8), 0x108B) := rfl
@[simp] theorem at_108B : prog 0x108B = some (.mov 32 (.reg .rax) (.reg .rdx), 0x108D) := rfl
@[simp] theorem at_108D : prog 0x108D = some (.add 64 (.reg .rsp) (.imm 0x18), 0x1091) := rfl
@[simp] theorem at_1091 : prog 0x1091 = some (.ret, 0x1092) := rfl
@[simp] theorem at_2000 : prog 0x2000 = some (.mov 32 (.reg .rax) (.imm 0x1), 0x2005) := rfl
@[simp] theorem at_2005 : prog 0x2005 = some (.xor 32 (.reg .rcx) (.reg .rcx), 0x2007) := rfl
@[simp] theorem at_2007 : prog 0x2007 = some (.mov 64 (.reg .rsi) (.reg .rbx), 0x200A) := rfl
@[simp] theorem at_200A : prog 0x200A = some (.cpuid, 0x200C) := rfl
@[simp] theorem at_200C : prog 0x200C = some (.xchg .rsi .rbx, 0x200F) := rfl
@[simp] theorem at_200F : prog 0x200F = some (.mov 32 (.mem .rdi 0x0) (.reg .rax), 0x2011) := rfl
@[simp] theorem at_2011 : prog 0x2011 = some (.mov 32 (.mem .rdi 0x4) (.reg .rcx), 0x2014) := rfl
@[simp] theorem at_2014 : prog 0x2014 = some (.not 32 (.reg .rcx), 0x2016) := rfl
@[simp] theorem at_2016 : prog 0x2016 = some (.mov 64 (.mem .rdi 0x8) (.imm 0x0), 0x201E) := rfl
@[simp] theorem at_201E : prog 0x201E = some (.mov 8 (.mem .rdi 0x10) (.imm 0x0), 0x2022) := rfl
@[simp] theorem at_2022 : prog 0x2022 = some (.test 32 (.reg .rcx) (.imm 0x1C000000), 0x2028) := rfl
@[simp] theorem at_2028 : prog 0x2028 = some (.jcc .ne 0x206F, 0x202A) := rfl
@[simp] theorem at_202A : prog 0x202A = some (.push .rbx, 0x202B) := rfl
@[simp] theorem at_202B : prog 0x202B = some (.mov 64 (.reg .rbx) (.reg .rdi), 0x202E) := rfl
@[simp] theorem at_202E : prog 0x202E = some (.call 0x3000, 0x2033) := rfl
@[simp] theorem at_2033 : prog 0x2033 = some (.mov 32 (.mem .rbx 0x8) (.reg .rax), 0x2036) := rfl
@[simp] theorem at_2036 : prog 0x2036 = some (.mov 32 (.reg .rax) (.imm 0x7), 0x203B) := rfl
@[simp] theorem at_203B : prog 0x203B = some (.xor 32 (.reg .rcx) (.reg .rcx), 0x203D) := rfl
@[simp] theorem at_203D : prog 0x203D = some (.mov 64 (.reg .rsi) (.reg .rbx), 0x2040) := rfl
@[simp] theorem at_2040 : prog 0x2040 = some (.cpuid, 0x2042) := rfl
@[simp] theorem at_2042 : prog 0x2042 = some (.xchg .rsi .rbx, 0x2045) := rfl
@[simp] theorem at_2045 : prog 0x2045 = some (.xor 32 (.reg .rax) (.reg .rax), 0x2047) := rfl
@[simp] theorem at_2047 : prog 0x2047 = some (.xor 32 (.reg .rcx) (.reg .rcx), 0x2049) := rfl
@[simp] theorem at_2049 : prog 0x2049 = some (.mov 64 (.reg .rdi) (.reg .rbx), 0x204C) := rfl
@[simp] theorem at_204C : prog 0x204C = some (.cpuid, 0x204E) := rfl
@[simp] theorem at_204E : prog 0x204E = some (.xchg .rdi .rbx, 0x2051) := rfl
@[simp] theorem at_2051 : prog 0x2051 = some (.mov 32 (.mem .rbx 0xC) (.reg .rsi), 0x2054) := rfl
@[simp] theorem at_2054 : prog 0x2054 = some (.xor 32 (.reg .rdi) (.imm 0x68747541), 0x205A) := rfl
@[simp] theorem at_205A : prog 0x205A = some (.xor 32 (.reg .rdx) (.imm 0x69746E65), 0x2060) := rfl
@[simp] theorem at_2060 : prog 0x2060 = some (.or 32 (.reg .rdx) (.reg .rdi), 0x2062) := rfl
@[simp] theorem at_2062 : prog 0x2062 = some (.xor 32 (.reg .rcx) (.imm 0x444D4163), 0x2068) := rfl
@[simp] theorem at_2068 : prog 0x2068 = some (.or 32 (.reg .rcx) (.reg .rdx), 0x206A) := rfl
@[simp] theorem at_206A : prog 0x206A = some (.setcc .e (.mem .rbx 0x10), 0x206E) := rfl
@[simp] theorem at_206E : prog 0x206E = some (.pop .rbx, 0x206F) := rfl
@[simp] theorem at_206F : prog 0x206F = some (.ret, 0x2070) := rfl
@[simp] theorem at_3000 : prog 0x3000 = some (.xor 32 (.reg .rcx) (.reg .rcx), 0x3002) := rfl
@[simp] theorem at_3002 : prog 0x3002 = some (.xgetbv, 0x3005) := rfl
@[simp] theorem at_3005 : prog 0x3005 = some (.shl 64 (.reg .rdx) 32, 0x3009) := rfl
@[simp] theorem at_3009 : prog 0x3009 = some (.or 64 (.reg .rax) (.reg .rdx), 0x300C) := rfl
@[simp] theorem at_300C : prog 0x300C = some (.ret, 0x300D) := rfl

end Code
