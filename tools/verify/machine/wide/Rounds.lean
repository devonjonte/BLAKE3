import Wide

/-! The seven rounds of `blake3_servil_hash_many_avx512`'s sixteen-lane loop: 784 instructions, as llvm-objdump reads them. -/

set_option maxRecDepth 1000000
namespace Rounds
open Wide

def table : List (Nat × Instr × Nat) := [
  (0x4F1, .vpaddd 0 0 16, 0x4F7),  -- 62 b1 7d 48 fe c0    vpaddd zmm0, zmm0, zmm16
  (0x4F7, .vpaddd 1 1 18, 0x4FD),  -- 62 b1 75 48 fe ca    vpaddd zmm1, zmm1, zmm18
  (0x4FD, .vpaddd 2 2 20, 0x503),  -- 62 b1 6d 48 fe d4    vpaddd zmm2, zmm2, zmm20
  (0x503, .vpaddd 3 3 22, 0x509),  -- 62 b1 65 48 fe de    vpaddd zmm3, zmm3, zmm22
  (0x509, .vpaddd 0 0 4, 0x50F),  -- 62 f1 7d 48 fe c4    vpaddd zmm0, zmm0, zmm4
  (0x50F, .vpaddd 1 1 5, 0x515),  -- 62 f1 75 48 fe cd    vpaddd zmm1, zmm1, zmm5
  (0x515, .vpaddd 2 2 6, 0x51B),  -- 62 f1 6d 48 fe d6    vpaddd zmm2, zmm2, zmm6
  (0x51B, .vpaddd 3 3 7, 0x521),  -- 62 f1 65 48 fe df    vpaddd zmm3, zmm3, zmm7
  (0x521, .vpxord 12 12 0, 0x527),  -- 62 71 1d 48 ef e0    vpxord zmm12, zmm12, zmm0
  (0x527, .vpxord 13 13 1, 0x52D),  -- 62 71 15 48 ef e9    vpxord zmm13, zmm13, zmm1
  (0x52D, .vpxord 14 14 2, 0x533),  -- 62 71 0d 48 ef f2    vpxord zmm14, zmm14, zmm2
  (0x533, .vpxord 15 15 3, 0x539),  -- 62 71 05 48 ef fb    vpxord zmm15, zmm15, zmm3
  (0x539, .vprord 12 12 16, 0x540),  -- 62 d1 1d 48 72 c4 10 vprord zmm12, zmm12, 0x10
  (0x540, .vprord 13 13 16, 0x547),  -- 62 d1 15 48 72 c5 10 vprord zmm13, zmm13, 0x10
  (0x547, .vprord 14 14 16, 0x54E),  -- 62 d1 0d 48 72 c6 10 vprord zmm14, zmm14, 0x10
  (0x54E, .vprord 15 15 16, 0x555),  -- 62 d1 05 48 72 c7 10 vprord zmm15, zmm15, 0x10
  (0x555, .vpaddd 8 8 12, 0x55B),  -- 62 51 3d 48 fe c4    vpaddd zmm8, zmm8, zmm12
  (0x55B, .vpaddd 9 9 13, 0x561),  -- 62 51 35 48 fe cd    vpaddd zmm9, zmm9, zmm13
  (0x561, .vpaddd 10 10 14, 0x567),  -- 62 51 2d 48 fe d6    vpaddd zmm10, zmm10, zmm14
  (0x567, .vpaddd 11 11 15, 0x56D),  -- 62 51 25 48 fe df    vpaddd zmm11, zmm11, zmm15
  (0x56D, .vpxord 4 4 8, 0x573),  -- 62 d1 5d 48 ef e0    vpxord zmm4, zmm4, zmm8
  (0x573, .vpxord 5 5 9, 0x579),  -- 62 d1 55 48 ef e9    vpxord zmm5, zmm5, zmm9
  (0x579, .vpxord 6 6 10, 0x57F),  -- 62 d1 4d 48 ef f2    vpxord zmm6, zmm6, zmm10
  (0x57F, .vpxord 7 7 11, 0x585),  -- 62 d1 45 48 ef fb    vpxord zmm7, zmm7, zmm11
  (0x585, .vprord 4 4 12, 0x58C),  -- 62 f1 5d 48 72 c4 0c vprord zmm4, zmm4, 0xc
  (0x58C, .vprord 5 5 12, 0x593),  -- 62 f1 55 48 72 c5 0c vprord zmm5, zmm5, 0xc
  (0x593, .vprord 6 6 12, 0x59A),  -- 62 f1 4d 48 72 c6 0c vprord zmm6, zmm6, 0xc
  (0x59A, .vprord 7 7 12, 0x5A1),  -- 62 f1 45 48 72 c7 0c vprord zmm7, zmm7, 0xc
  (0x5A1, .vpaddd 0 0 17, 0x5A7),  -- 62 b1 7d 48 fe c1    vpaddd zmm0, zmm0, zmm17
  (0x5A7, .vpaddd 1 1 19, 0x5AD),  -- 62 b1 75 48 fe cb    vpaddd zmm1, zmm1, zmm19
  (0x5AD, .vpaddd 2 2 21, 0x5B3),  -- 62 b1 6d 48 fe d5    vpaddd zmm2, zmm2, zmm21
  (0x5B3, .vpaddd 3 3 23, 0x5B9),  -- 62 b1 65 48 fe df    vpaddd zmm3, zmm3, zmm23
  (0x5B9, .vpaddd 0 0 4, 0x5BF),  -- 62 f1 7d 48 fe c4    vpaddd zmm0, zmm0, zmm4
  (0x5BF, .vpaddd 1 1 5, 0x5C5),  -- 62 f1 75 48 fe cd    vpaddd zmm1, zmm1, zmm5
  (0x5C5, .vpaddd 2 2 6, 0x5CB),  -- 62 f1 6d 48 fe d6    vpaddd zmm2, zmm2, zmm6
  (0x5CB, .vpaddd 3 3 7, 0x5D1),  -- 62 f1 65 48 fe df    vpaddd zmm3, zmm3, zmm7
  (0x5D1, .vpxord 12 12 0, 0x5D7),  -- 62 71 1d 48 ef e0    vpxord zmm12, zmm12, zmm0
  (0x5D7, .vpxord 13 13 1, 0x5DD),  -- 62 71 15 48 ef e9    vpxord zmm13, zmm13, zmm1
  (0x5DD, .vpxord 14 14 2, 0x5E3),  -- 62 71 0d 48 ef f2    vpxord zmm14, zmm14, zmm2
  (0x5E3, .vpxord 15 15 3, 0x5E9),  -- 62 71 05 48 ef fb    vpxord zmm15, zmm15, zmm3
  (0x5E9, .vprord 12 12 8, 0x5F0),  -- 62 d1 1d 48 72 c4 08 vprord zmm12, zmm12, 0x8
  (0x5F0, .vprord 13 13 8, 0x5F7),  -- 62 d1 15 48 72 c5 08 vprord zmm13, zmm13, 0x8
  (0x5F7, .vprord 14 14 8, 0x5FE),  -- 62 d1 0d 48 72 c6 08 vprord zmm14, zmm14, 0x8
  (0x5FE, .vprord 15 15 8, 0x605),  -- 62 d1 05 48 72 c7 08 vprord zmm15, zmm15, 0x8
  (0x605, .vpaddd 8 8 12, 0x60B),  -- 62 51 3d 48 fe c4    vpaddd zmm8, zmm8, zmm12
  (0x60B, .vpaddd 9 9 13, 0x611),  -- 62 51 35 48 fe cd    vpaddd zmm9, zmm9, zmm13
  (0x611, .vpaddd 10 10 14, 0x617),  -- 62 51 2d 48 fe d6    vpaddd zmm10, zmm10, zmm14
  (0x617, .vpaddd 11 11 15, 0x61D),  -- 62 51 25 48 fe df    vpaddd zmm11, zmm11, zmm15
  (0x61D, .vpxord 4 4 8, 0x623),  -- 62 d1 5d 48 ef e0    vpxord zmm4, zmm4, zmm8
  (0x623, .vpxord 5 5 9, 0x629),  -- 62 d1 55 48 ef e9    vpxord zmm5, zmm5, zmm9
  (0x629, .vpxord 6 6 10, 0x62F),  -- 62 d1 4d 48 ef f2    vpxord zmm6, zmm6, zmm10
  (0x62F, .vpxord 7 7 11, 0x635),  -- 62 d1 45 48 ef fb    vpxord zmm7, zmm7, zmm11
  (0x635, .vprord 4 4 7, 0x63C),  -- 62 f1 5d 48 72 c4 07 vprord zmm4, zmm4, 0x7
  (0x63C, .vprord 5 5 7, 0x643),  -- 62 f1 55 48 72 c5 07 vprord zmm5, zmm5, 0x7
  (0x643, .vprord 6 6 7, 0x64A),  -- 62 f1 4d 48 72 c6 07 vprord zmm6, zmm6, 0x7
  (0x64A, .vprord 7 7 7, 0x651),  -- 62 f1 45 48 72 c7 07 vprord zmm7, zmm7, 0x7
  (0x651, .vpaddd 0 0 24, 0x657),  -- 62 91 7d 48 fe c0    vpaddd zmm0, zmm0, zmm24
  (0x657, .vpaddd 1 1 26, 0x65D),  -- 62 91 75 48 fe ca    vpaddd zmm1, zmm1, zmm26
  (0x65D, .vpaddd 2 2 28, 0x663),  -- 62 91 6d 48 fe d4    vpaddd zmm2, zmm2, zmm28
  (0x663, .vpaddd 3 3 30, 0x669),  -- 62 91 65 48 fe de    vpaddd zmm3, zmm3, zmm30
  (0x669, .vpaddd 0 0 5, 0x66F),  -- 62 f1 7d 48 fe c5    vpaddd zmm0, zmm0, zmm5
  (0x66F, .vpaddd 1 1 6, 0x675),  -- 62 f1 75 48 fe ce    vpaddd zmm1, zmm1, zmm6
  (0x675, .vpaddd 2 2 7, 0x67B),  -- 62 f1 6d 48 fe d7    vpaddd zmm2, zmm2, zmm7
  (0x67B, .vpaddd 3 3 4, 0x681),  -- 62 f1 65 48 fe dc    vpaddd zmm3, zmm3, zmm4
  (0x681, .vpxord 15 15 0, 0x687),  -- 62 71 05 48 ef f8    vpxord zmm15, zmm15, zmm0
  (0x687, .vpxord 12 12 1, 0x68D),  -- 62 71 1d 48 ef e1    vpxord zmm12, zmm12, zmm1
  (0x68D, .vpxord 13 13 2, 0x693),  -- 62 71 15 48 ef ea    vpxord zmm13, zmm13, zmm2
  (0x693, .vpxord 14 14 3, 0x699),  -- 62 71 0d 48 ef f3    vpxord zmm14, zmm14, zmm3
  (0x699, .vprord 15 15 16, 0x6A0),  -- 62 d1 05 48 72 c7 10 vprord zmm15, zmm15, 0x10
  (0x6A0, .vprord 12 12 16, 0x6A7),  -- 62 d1 1d 48 72 c4 10 vprord zmm12, zmm12, 0x10
  (0x6A7, .vprord 13 13 16, 0x6AE),  -- 62 d1 15 48 72 c5 10 vprord zmm13, zmm13, 0x10
  (0x6AE, .vprord 14 14 16, 0x6B5),  -- 62 d1 0d 48 72 c6 10 vprord zmm14, zmm14, 0x10
  (0x6B5, .vpaddd 10 10 15, 0x6BB),  -- 62 51 2d 48 fe d7    vpaddd zmm10, zmm10, zmm15
  (0x6BB, .vpaddd 11 11 12, 0x6C1),  -- 62 51 25 48 fe dc    vpaddd zmm11, zmm11, zmm12
  (0x6C1, .vpaddd 8 8 13, 0x6C7),  -- 62 51 3d 48 fe c5    vpaddd zmm8, zmm8, zmm13
  (0x6C7, .vpaddd 9 9 14, 0x6CD),  -- 62 51 35 48 fe ce    vpaddd zmm9, zmm9, zmm14
  (0x6CD, .vpxord 5 5 10, 0x6D3),  -- 62 d1 55 48 ef ea    vpxord zmm5, zmm5, zmm10
  (0x6D3, .vpxord 6 6 11, 0x6D9),  -- 62 d1 4d 48 ef f3    vpxord zmm6, zmm6, zmm11
  (0x6D9, .vpxord 7 7 8, 0x6DF),  -- 62 d1 45 48 ef f8    vpxord zmm7, zmm7, zmm8
  (0x6DF, .vpxord 4 4 9, 0x6E5),  -- 62 d1 5d 48 ef e1    vpxord zmm4, zmm4, zmm9
  (0x6E5, .vprord 5 5 12, 0x6EC),  -- 62 f1 55 48 72 c5 0c vprord zmm5, zmm5, 0xc
  (0x6EC, .vprord 6 6 12, 0x6F3),  -- 62 f1 4d 48 72 c6 0c vprord zmm6, zmm6, 0xc
  (0x6F3, .vprord 7 7 12, 0x6FA),  -- 62 f1 45 48 72 c7 0c vprord zmm7, zmm7, 0xc
  (0x6FA, .vprord 4 4 12, 0x701),  -- 62 f1 5d 48 72 c4 0c vprord zmm4, zmm4, 0xc
  (0x701, .vpaddd 0 0 25, 0x707),  -- 62 91 7d 48 fe c1    vpaddd zmm0, zmm0, zmm25
  (0x707, .vpaddd 1 1 27, 0x70D),  -- 62 91 75 48 fe cb    vpaddd zmm1, zmm1, zmm27
  (0x70D, .vpaddd 2 2 29, 0x713),  -- 62 91 6d 48 fe d5    vpaddd zmm2, zmm2, zmm29
  (0x713, .vpaddd 3 3 31, 0x719),  -- 62 91 65 48 fe df    vpaddd zmm3, zmm3, zmm31
  (0x719, .vpaddd 0 0 5, 0x71F),  -- 62 f1 7d 48 fe c5    vpaddd zmm0, zmm0, zmm5
  (0x71F, .vpaddd 1 1 6, 0x725),  -- 62 f1 75 48 fe ce    vpaddd zmm1, zmm1, zmm6
  (0x725, .vpaddd 2 2 7, 0x72B),  -- 62 f1 6d 48 fe d7    vpaddd zmm2, zmm2, zmm7
  (0x72B, .vpaddd 3 3 4, 0x731),  -- 62 f1 65 48 fe dc    vpaddd zmm3, zmm3, zmm4
  (0x731, .vpxord 15 15 0, 0x737),  -- 62 71 05 48 ef f8    vpxord zmm15, zmm15, zmm0
  (0x737, .vpxord 12 12 1, 0x73D),  -- 62 71 1d 48 ef e1    vpxord zmm12, zmm12, zmm1
  (0x73D, .vpxord 13 13 2, 0x743),  -- 62 71 15 48 ef ea    vpxord zmm13, zmm13, zmm2
  (0x743, .vpxord 14 14 3, 0x749),  -- 62 71 0d 48 ef f3    vpxord zmm14, zmm14, zmm3
  (0x749, .vprord 15 15 8, 0x750),  -- 62 d1 05 48 72 c7 08 vprord zmm15, zmm15, 0x8
  (0x750, .vprord 12 12 8, 0x757),  -- 62 d1 1d 48 72 c4 08 vprord zmm12, zmm12, 0x8
  (0x757, .vprord 13 13 8, 0x75E),  -- 62 d1 15 48 72 c5 08 vprord zmm13, zmm13, 0x8
  (0x75E, .vprord 14 14 8, 0x765),  -- 62 d1 0d 48 72 c6 08 vprord zmm14, zmm14, 0x8
  (0x765, .vpaddd 10 10 15, 0x76B),  -- 62 51 2d 48 fe d7    vpaddd zmm10, zmm10, zmm15
  (0x76B, .vpaddd 11 11 12, 0x771),  -- 62 51 25 48 fe dc    vpaddd zmm11, zmm11, zmm12
  (0x771, .vpaddd 8 8 13, 0x777),  -- 62 51 3d 48 fe c5    vpaddd zmm8, zmm8, zmm13
  (0x777, .vpaddd 9 9 14, 0x77D),  -- 62 51 35 48 fe ce    vpaddd zmm9, zmm9, zmm14
  (0x77D, .vpxord 5 5 10, 0x783),  -- 62 d1 55 48 ef ea    vpxord zmm5, zmm5, zmm10
  (0x783, .vpxord 6 6 11, 0x789),  -- 62 d1 4d 48 ef f3    vpxord zmm6, zmm6, zmm11
  (0x789, .vpxord 7 7 8, 0x78F),  -- 62 d1 45 48 ef f8    vpxord zmm7, zmm7, zmm8
  (0x78F, .vpxord 4 4 9, 0x795),  -- 62 d1 5d 48 ef e1    vpxord zmm4, zmm4, zmm9
  (0x795, .vprord 5 5 7, 0x79C),  -- 62 f1 55 48 72 c5 07 vprord zmm5, zmm5, 0x7
  (0x79C, .vprord 6 6 7, 0x7A3),  -- 62 f1 4d 48 72 c6 07 vprord zmm6, zmm6, 0x7
  (0x7A3, .vprord 7 7 7, 0x7AA),  -- 62 f1 45 48 72 c7 07 vprord zmm7, zmm7, 0x7
  (0x7AA, .vprord 4 4 7, 0x7B1),  -- 62 f1 5d 48 72 c4 07 vprord zmm4, zmm4, 0x7
  (0x7B1, .vpaddd 0 0 18, 0x7B7),  -- 62 b1 7d 48 fe c2    vpaddd zmm0, zmm0, zmm18
  (0x7B7, .vpaddd 1 1 19, 0x7BD),  -- 62 b1 75 48 fe cb    vpaddd zmm1, zmm1, zmm19
  (0x7BD, .vpaddd 2 2 23, 0x7C3),  -- 62 b1 6d 48 fe d7    vpaddd zmm2, zmm2, zmm23
  (0x7C3, .vpaddd 3 3 20, 0x7C9),  -- 62 b1 65 48 fe dc    vpaddd zmm3, zmm3, zmm20
  (0x7C9, .vpaddd 0 0 4, 0x7CF),  -- 62 f1 7d 48 fe c4    vpaddd zmm0, zmm0, zmm4
  (0x7CF, .vpaddd 1 1 5, 0x7D5),  -- 62 f1 75 48 fe cd    vpaddd zmm1, zmm1, zmm5
  (0x7D5, .vpaddd 2 2 6, 0x7DB),  -- 62 f1 6d 48 fe d6    vpaddd zmm2, zmm2, zmm6
  (0x7DB, .vpaddd 3 3 7, 0x7E1),  -- 62 f1 65 48 fe df    vpaddd zmm3, zmm3, zmm7
  (0x7E1, .vpxord 12 12 0, 0x7E7),  -- 62 71 1d 48 ef e0    vpxord zmm12, zmm12, zmm0
  (0x7E7, .vpxord 13 13 1, 0x7ED),  -- 62 71 15 48 ef e9    vpxord zmm13, zmm13, zmm1
  (0x7ED, .vpxord 14 14 2, 0x7F3),  -- 62 71 0d 48 ef f2    vpxord zmm14, zmm14, zmm2
  (0x7F3, .vpxord 15 15 3, 0x7F9),  -- 62 71 05 48 ef fb    vpxord zmm15, zmm15, zmm3
  (0x7F9, .vprord 12 12 16, 0x800),  -- 62 d1 1d 48 72 c4 10 vprord zmm12, zmm12, 0x10
  (0x800, .vprord 13 13 16, 0x807),  -- 62 d1 15 48 72 c5 10 vprord zmm13, zmm13, 0x10
  (0x807, .vprord 14 14 16, 0x80E),  -- 62 d1 0d 48 72 c6 10 vprord zmm14, zmm14, 0x10
  (0x80E, .vprord 15 15 16, 0x815),  -- 62 d1 05 48 72 c7 10 vprord zmm15, zmm15, 0x10
  (0x815, .vpaddd 8 8 12, 0x81B),  -- 62 51 3d 48 fe c4    vpaddd zmm8, zmm8, zmm12
  (0x81B, .vpaddd 9 9 13, 0x821),  -- 62 51 35 48 fe cd    vpaddd zmm9, zmm9, zmm13
  (0x821, .vpaddd 10 10 14, 0x827),  -- 62 51 2d 48 fe d6    vpaddd zmm10, zmm10, zmm14
  (0x827, .vpaddd 11 11 15, 0x82D),  -- 62 51 25 48 fe df    vpaddd zmm11, zmm11, zmm15
  (0x82D, .vpxord 4 4 8, 0x833),  -- 62 d1 5d 48 ef e0    vpxord zmm4, zmm4, zmm8
  (0x833, .vpxord 5 5 9, 0x839),  -- 62 d1 55 48 ef e9    vpxord zmm5, zmm5, zmm9
  (0x839, .vpxord 6 6 10, 0x83F),  -- 62 d1 4d 48 ef f2    vpxord zmm6, zmm6, zmm10
  (0x83F, .vpxord 7 7 11, 0x845),  -- 62 d1 45 48 ef fb    vpxord zmm7, zmm7, zmm11
  (0x845, .vprord 4 4 12, 0x84C),  -- 62 f1 5d 48 72 c4 0c vprord zmm4, zmm4, 0xc
  (0x84C, .vprord 5 5 12, 0x853),  -- 62 f1 55 48 72 c5 0c vprord zmm5, zmm5, 0xc
  (0x853, .vprord 6 6 12, 0x85A),  -- 62 f1 4d 48 72 c6 0c vprord zmm6, zmm6, 0xc
  (0x85A, .vprord 7 7 12, 0x861),  -- 62 f1 45 48 72 c7 0c vprord zmm7, zmm7, 0xc
  (0x861, .vpaddd 0 0 22, 0x867),  -- 62 b1 7d 48 fe c6    vpaddd zmm0, zmm0, zmm22
  (0x867, .vpaddd 1 1 26, 0x86D),  -- 62 91 75 48 fe ca    vpaddd zmm1, zmm1, zmm26
  (0x86D, .vpaddd 2 2 16, 0x873),  -- 62 b1 6d 48 fe d0    vpaddd zmm2, zmm2, zmm16
  (0x873, .vpaddd 3 3 29, 0x879),  -- 62 91 65 48 fe dd    vpaddd zmm3, zmm3, zmm29
  (0x879, .vpaddd 0 0 4, 0x87F),  -- 62 f1 7d 48 fe c4    vpaddd zmm0, zmm0, zmm4
  (0x87F, .vpaddd 1 1 5, 0x885),  -- 62 f1 75 48 fe cd    vpaddd zmm1, zmm1, zmm5
  (0x885, .vpaddd 2 2 6, 0x88B),  -- 62 f1 6d 48 fe d6    vpaddd zmm2, zmm2, zmm6
  (0x88B, .vpaddd 3 3 7, 0x891),  -- 62 f1 65 48 fe df    vpaddd zmm3, zmm3, zmm7
  (0x891, .vpxord 12 12 0, 0x897),  -- 62 71 1d 48 ef e0    vpxord zmm12, zmm12, zmm0
  (0x897, .vpxord 13 13 1, 0x89D),  -- 62 71 15 48 ef e9    vpxord zmm13, zmm13, zmm1
  (0x89D, .vpxord 14 14 2, 0x8A3),  -- 62 71 0d 48 ef f2    vpxord zmm14, zmm14, zmm2
  (0x8A3, .vpxord 15 15 3, 0x8A9),  -- 62 71 05 48 ef fb    vpxord zmm15, zmm15, zmm3
  (0x8A9, .vprord 12 12 8, 0x8B0),  -- 62 d1 1d 48 72 c4 08 vprord zmm12, zmm12, 0x8
  (0x8B0, .vprord 13 13 8, 0x8B7),  -- 62 d1 15 48 72 c5 08 vprord zmm13, zmm13, 0x8
  (0x8B7, .vprord 14 14 8, 0x8BE),  -- 62 d1 0d 48 72 c6 08 vprord zmm14, zmm14, 0x8
  (0x8BE, .vprord 15 15 8, 0x8C5),  -- 62 d1 05 48 72 c7 08 vprord zmm15, zmm15, 0x8
  (0x8C5, .vpaddd 8 8 12, 0x8CB),  -- 62 51 3d 48 fe c4    vpaddd zmm8, zmm8, zmm12
  (0x8CB, .vpaddd 9 9 13, 0x8D1),  -- 62 51 35 48 fe cd    vpaddd zmm9, zmm9, zmm13
  (0x8D1, .vpaddd 10 10 14, 0x8D7),  -- 62 51 2d 48 fe d6    vpaddd zmm10, zmm10, zmm14
  (0x8D7, .vpaddd 11 11 15, 0x8DD),  -- 62 51 25 48 fe df    vpaddd zmm11, zmm11, zmm15
  (0x8DD, .vpxord 4 4 8, 0x8E3),  -- 62 d1 5d 48 ef e0    vpxord zmm4, zmm4, zmm8
  (0x8E3, .vpxord 5 5 9, 0x8E9),  -- 62 d1 55 48 ef e9    vpxord zmm5, zmm5, zmm9
  (0x8E9, .vpxord 6 6 10, 0x8EF),  -- 62 d1 4d 48 ef f2    vpxord zmm6, zmm6, zmm10
  (0x8EF, .vpxord 7 7 11, 0x8F5),  -- 62 d1 45 48 ef fb    vpxord zmm7, zmm7, zmm11
  (0x8F5, .vprord 4 4 7, 0x8FC),  -- 62 f1 5d 48 72 c4 07 vprord zmm4, zmm4, 0x7
  (0x8FC, .vprord 5 5 7, 0x903),  -- 62 f1 55 48 72 c5 07 vprord zmm5, zmm5, 0x7
  (0x903, .vprord 6 6 7, 0x90A),  -- 62 f1 4d 48 72 c6 07 vprord zmm6, zmm6, 0x7
  (0x90A, .vprord 7 7 7, 0x911),  -- 62 f1 45 48 72 c7 07 vprord zmm7, zmm7, 0x7
  (0x911, .vpaddd 0 0 17, 0x917),  -- 62 b1 7d 48 fe c1    vpaddd zmm0, zmm0, zmm17
  (0x917, .vpaddd 1 1 28, 0x91D),  -- 62 91 75 48 fe cc    vpaddd zmm1, zmm1, zmm28
  (0x91D, .vpaddd 2 2 25, 0x923),  -- 62 91 6d 48 fe d1    vpaddd zmm2, zmm2, zmm25
  (0x923, .vpaddd 3 3 31, 0x929),  -- 62 91 65 48 fe df    vpaddd zmm3, zmm3, zmm31
  (0x929, .vpaddd 0 0 5, 0x92F),  -- 62 f1 7d 48 fe c5    vpaddd zmm0, zmm0, zmm5
  (0x92F, .vpaddd 1 1 6, 0x935),  -- 62 f1 75 48 fe ce    vpaddd zmm1, zmm1, zmm6
  (0x935, .vpaddd 2 2 7, 0x93B),  -- 62 f1 6d 48 fe d7    vpaddd zmm2, zmm2, zmm7
  (0x93B, .vpaddd 3 3 4, 0x941),  -- 62 f1 65 48 fe dc    vpaddd zmm3, zmm3, zmm4
  (0x941, .vpxord 15 15 0, 0x947),  -- 62 71 05 48 ef f8    vpxord zmm15, zmm15, zmm0
  (0x947, .vpxord 12 12 1, 0x94D),  -- 62 71 1d 48 ef e1    vpxord zmm12, zmm12, zmm1
  (0x94D, .vpxord 13 13 2, 0x953),  -- 62 71 15 48 ef ea    vpxord zmm13, zmm13, zmm2
  (0x953, .vpxord 14 14 3, 0x959),  -- 62 71 0d 48 ef f3    vpxord zmm14, zmm14, zmm3
  (0x959, .vprord 15 15 16, 0x960),  -- 62 d1 05 48 72 c7 10 vprord zmm15, zmm15, 0x10
  (0x960, .vprord 12 12 16, 0x967),  -- 62 d1 1d 48 72 c4 10 vprord zmm12, zmm12, 0x10
  (0x967, .vprord 13 13 16, 0x96E),  -- 62 d1 15 48 72 c5 10 vprord zmm13, zmm13, 0x10
  (0x96E, .vprord 14 14 16, 0x975),  -- 62 d1 0d 48 72 c6 10 vprord zmm14, zmm14, 0x10
  (0x975, .vpaddd 10 10 15, 0x97B),  -- 62 51 2d 48 fe d7    vpaddd zmm10, zmm10, zmm15
  (0x97B, .vpaddd 11 11 12, 0x981),  -- 62 51 25 48 fe dc    vpaddd zmm11, zmm11, zmm12
  (0x981, .vpaddd 8 8 13, 0x987),  -- 62 51 3d 48 fe c5    vpaddd zmm8, zmm8, zmm13
  (0x987, .vpaddd 9 9 14, 0x98D),  -- 62 51 35 48 fe ce    vpaddd zmm9, zmm9, zmm14
  (0x98D, .vpxord 5 5 10, 0x993),  -- 62 d1 55 48 ef ea    vpxord zmm5, zmm5, zmm10
  (0x993, .vpxord 6 6 11, 0x999),  -- 62 d1 4d 48 ef f3    vpxord zmm6, zmm6, zmm11
  (0x999, .vpxord 7 7 8, 0x99F),  -- 62 d1 45 48 ef f8    vpxord zmm7, zmm7, zmm8
  (0x99F, .vpxord 4 4 9, 0x9A5),  -- 62 d1 5d 48 ef e1    vpxord zmm4, zmm4, zmm9
  (0x9A5, .vprord 5 5 12, 0x9AC),  -- 62 f1 55 48 72 c5 0c vprord zmm5, zmm5, 0xc
  (0x9AC, .vprord 6 6 12, 0x9B3),  -- 62 f1 4d 48 72 c6 0c vprord zmm6, zmm6, 0xc
  (0x9B3, .vprord 7 7 12, 0x9BA),  -- 62 f1 45 48 72 c7 0c vprord zmm7, zmm7, 0xc
  (0x9BA, .vprord 4 4 12, 0x9C1),  -- 62 f1 5d 48 72 c4 0c vprord zmm4, zmm4, 0xc
  (0x9C1, .vpaddd 0 0 27, 0x9C7),  -- 62 91 7d 48 fe c3    vpaddd zmm0, zmm0, zmm27
  (0x9C7, .vpaddd 1 1 21, 0x9CD),  -- 62 b1 75 48 fe cd    vpaddd zmm1, zmm1, zmm21
  (0x9CD, .vpaddd 2 2 30, 0x9D3),  -- 62 91 6d 48 fe d6    vpaddd zmm2, zmm2, zmm30
  (0x9D3, .vpaddd 3 3 24, 0x9D9),  -- 62 91 65 48 fe d8    vpaddd zmm3, zmm3, zmm24
  (0x9D9, .vpaddd 0 0 5, 0x9DF),  -- 62 f1 7d 48 fe c5    vpaddd zmm0, zmm0, zmm5
  (0x9DF, .vpaddd 1 1 6, 0x9E5),  -- 62 f1 75 48 fe ce    vpaddd zmm1, zmm1, zmm6
  (0x9E5, .vpaddd 2 2 7, 0x9EB),  -- 62 f1 6d 48 fe d7    vpaddd zmm2, zmm2, zmm7
  (0x9EB, .vpaddd 3 3 4, 0x9F1),  -- 62 f1 65 48 fe dc    vpaddd zmm3, zmm3, zmm4
  (0x9F1, .vpxord 15 15 0, 0x9F7),  -- 62 71 05 48 ef f8    vpxord zmm15, zmm15, zmm0
  (0x9F7, .vpxord 12 12 1, 0x9FD),  -- 62 71 1d 48 ef e1    vpxord zmm12, zmm12, zmm1
  (0x9FD, .vpxord 13 13 2, 0xA03),  -- 62 71 15 48 ef ea    vpxord zmm13, zmm13, zmm2
  (0xA03, .vpxord 14 14 3, 0xA09),  -- 62 71 0d 48 ef f3    vpxord zmm14, zmm14, zmm3
  (0xA09, .vprord 15 15 8, 0xA10),  -- 62 d1 05 48 72 c7 08 vprord zmm15, zmm15, 0x8
  (0xA10, .vprord 12 12 8, 0xA17),  -- 62 d1 1d 48 72 c4 08 vprord zmm12, zmm12, 0x8
  (0xA17, .vprord 13 13 8, 0xA1E),  -- 62 d1 15 48 72 c5 08 vprord zmm13, zmm13, 0x8
  (0xA1E, .vprord 14 14 8, 0xA25),  -- 62 d1 0d 48 72 c6 08 vprord zmm14, zmm14, 0x8
  (0xA25, .vpaddd 10 10 15, 0xA2B),  -- 62 51 2d 48 fe d7    vpaddd zmm10, zmm10, zmm15
  (0xA2B, .vpaddd 11 11 12, 0xA31),  -- 62 51 25 48 fe dc    vpaddd zmm11, zmm11, zmm12
  (0xA31, .vpaddd 8 8 13, 0xA37),  -- 62 51 3d 48 fe c5    vpaddd zmm8, zmm8, zmm13
  (0xA37, .vpaddd 9 9 14, 0xA3D),  -- 62 51 35 48 fe ce    vpaddd zmm9, zmm9, zmm14
  (0xA3D, .vpxord 5 5 10, 0xA43),  -- 62 d1 55 48 ef ea    vpxord zmm5, zmm5, zmm10
  (0xA43, .vpxord 6 6 11, 0xA49),  -- 62 d1 4d 48 ef f3    vpxord zmm6, zmm6, zmm11
  (0xA49, .vpxord 7 7 8, 0xA4F),  -- 62 d1 45 48 ef f8    vpxord zmm7, zmm7, zmm8
  (0xA4F, .vpxord 4 4 9, 0xA55),  -- 62 d1 5d 48 ef e1    vpxord zmm4, zmm4, zmm9
  (0xA55, .vprord 5 5 7, 0xA5C),  -- 62 f1 55 48 72 c5 07 vprord zmm5, zmm5, 0x7
  (0xA5C, .vprord 6 6 7, 0xA63),  -- 62 f1 4d 48 72 c6 07 vprord zmm6, zmm6, 0x7
  (0xA63, .vprord 7 7 7, 0xA6A),  -- 62 f1 45 48 72 c7 07 vprord zmm7, zmm7, 0x7
  (0xA6A, .vprord 4 4 7, 0xA71),  -- 62 f1 5d 48 72 c4 07 vprord zmm4, zmm4, 0x7
  (0xA71, .vpaddd 0 0 19, 0xA77),  -- 62 b1 7d 48 fe c3    vpaddd zmm0, zmm0, zmm19
  (0xA77, .vpaddd 1 1 26, 0xA7D),  -- 62 91 75 48 fe ca    vpaddd zmm1, zmm1, zmm26
  (0xA7D, .vpaddd 2 2 29, 0xA83),  -- 62 91 6d 48 fe d5    vpaddd zmm2, zmm2, zmm29
  (0xA83, .vpaddd 3 3 23, 0xA89),  -- 62 b1 65 48 fe df    vpaddd zmm3, zmm3, zmm23
  (0xA89, .vpaddd 0 0 4, 0xA8F),  -- 62 f1 7d 48 fe c4    vpaddd zmm0, zmm0, zmm4
  (0xA8F, .vpaddd 1 1 5, 0xA95),  -- 62 f1 75 48 fe cd    vpaddd zmm1, zmm1, zmm5
  (0xA95, .vpaddd 2 2 6, 0xA9B),  -- 62 f1 6d 48 fe d6    vpaddd zmm2, zmm2, zmm6
  (0xA9B, .vpaddd 3 3 7, 0xAA1),  -- 62 f1 65 48 fe df    vpaddd zmm3, zmm3, zmm7
  (0xAA1, .vpxord 12 12 0, 0xAA7),  -- 62 71 1d 48 ef e0    vpxord zmm12, zmm12, zmm0
  (0xAA7, .vpxord 13 13 1, 0xAAD),  -- 62 71 15 48 ef e9    vpxord zmm13, zmm13, zmm1
  (0xAAD, .vpxord 14 14 2, 0xAB3),  -- 62 71 0d 48 ef f2    vpxord zmm14, zmm14, zmm2
  (0xAB3, .vpxord 15 15 3, 0xAB9),  -- 62 71 05 48 ef fb    vpxord zmm15, zmm15, zmm3
  (0xAB9, .vprord 12 12 16, 0xAC0),  -- 62 d1 1d 48 72 c4 10 vprord zmm12, zmm12, 0x10
  (0xAC0, .vprord 13 13 16, 0xAC7),  -- 62 d1 15 48 72 c5 10 vprord zmm13, zmm13, 0x10
  (0xAC7, .vprord 14 14 16, 0xACE),  -- 62 d1 0d 48 72 c6 10 vprord zmm14, zmm14, 0x10
  (0xACE, .vprord 15 15 16, 0xAD5),  -- 62 d1 05 48 72 c7 10 vprord zmm15, zmm15, 0x10
  (0xAD5, .vpaddd 8 8 12, 0xADB),  -- 62 51 3d 48 fe c4    vpaddd zmm8, zmm8, zmm12
  (0xADB, .vpaddd 9 9 13, 0xAE1),  -- 62 51 35 48 fe cd    vpaddd zmm9, zmm9, zmm13
  (0xAE1, .vpaddd 10 10 14, 0xAE7),  -- 62 51 2d 48 fe d6    vpaddd zmm10, zmm10, zmm14
  (0xAE7, .vpaddd 11 11 15, 0xAED),  -- 62 51 25 48 fe df    vpaddd zmm11, zmm11, zmm15
  (0xAED, .vpxord 4 4 8, 0xAF3),  -- 62 d1 5d 48 ef e0    vpxord zmm4, zmm4, zmm8
  (0xAF3, .vpxord 5 5 9, 0xAF9),  -- 62 d1 55 48 ef e9    vpxord zmm5, zmm5, zmm9
  (0xAF9, .vpxord 6 6 10, 0xAFF),  -- 62 d1 4d 48 ef f2    vpxord zmm6, zmm6, zmm10
  (0xAFF, .vpxord 7 7 11, 0xB05),  -- 62 d1 45 48 ef fb    vpxord zmm7, zmm7, zmm11
  (0xB05, .vprord 4 4 12, 0xB0C),  -- 62 f1 5d 48 72 c4 0c vprord zmm4, zmm4, 0xc
  (0xB0C, .vprord 5 5 12, 0xB13),  -- 62 f1 55 48 72 c5 0c vprord zmm5, zmm5, 0xc
  (0xB13, .vprord 6 6 12, 0xB1A),  -- 62 f1 4d 48 72 c6 0c vprord zmm6, zmm6, 0xc
  (0xB1A, .vprord 7 7 12, 0xB21),  -- 62 f1 45 48 72 c7 0c vprord zmm7, zmm7, 0xc
  (0xB21, .vpaddd 0 0 20, 0xB27),  -- 62 b1 7d 48 fe c4    vpaddd zmm0, zmm0, zmm20
  (0xB27, .vpaddd 1 1 28, 0xB2D),  -- 62 91 75 48 fe cc    vpaddd zmm1, zmm1, zmm28
  (0xB2D, .vpaddd 2 2 18, 0xB33),  -- 62 b1 6d 48 fe d2    vpaddd zmm2, zmm2, zmm18
  (0xB33, .vpaddd 3 3 30, 0xB39),  -- 62 91 65 48 fe de    vpaddd zmm3, zmm3, zmm30
  (0xB39, .vpaddd 0 0 4, 0xB3F),  -- 62 f1 7d 48 fe c4    vpaddd zmm0, zmm0, zmm4
  (0xB3F, .vpaddd 1 1 5, 0xB45),  -- 62 f1 75 48 fe cd    vpaddd zmm1, zmm1, zmm5
  (0xB45, .vpaddd 2 2 6, 0xB4B),  -- 62 f1 6d 48 fe d6    vpaddd zmm2, zmm2, zmm6
  (0xB4B, .vpaddd 3 3 7, 0xB51),  -- 62 f1 65 48 fe df    vpaddd zmm3, zmm3, zmm7
  (0xB51, .vpxord 12 12 0, 0xB57),  -- 62 71 1d 48 ef e0    vpxord zmm12, zmm12, zmm0
  (0xB57, .vpxord 13 13 1, 0xB5D),  -- 62 71 15 48 ef e9    vpxord zmm13, zmm13, zmm1
  (0xB5D, .vpxord 14 14 2, 0xB63),  -- 62 71 0d 48 ef f2    vpxord zmm14, zmm14, zmm2
  (0xB63, .vpxord 15 15 3, 0xB69),  -- 62 71 05 48 ef fb    vpxord zmm15, zmm15, zmm3
  (0xB69, .vprord 12 12 8, 0xB70),  -- 62 d1 1d 48 72 c4 08 vprord zmm12, zmm12, 0x8
  (0xB70, .vprord 13 13 8, 0xB77),  -- 62 d1 15 48 72 c5 08 vprord zmm13, zmm13, 0x8
  (0xB77, .vprord 14 14 8, 0xB7E),  -- 62 d1 0d 48 72 c6 08 vprord zmm14, zmm14, 0x8
  (0xB7E, .vprord 15 15 8, 0xB85),  -- 62 d1 05 48 72 c7 08 vprord zmm15, zmm15, 0x8
  (0xB85, .vpaddd 8 8 12, 0xB8B),  -- 62 51 3d 48 fe c4    vpaddd zmm8, zmm8, zmm12
  (0xB8B, .vpaddd 9 9 13, 0xB91),  -- 62 51 35 48 fe cd    vpaddd zmm9, zmm9, zmm13
  (0xB91, .vpaddd 10 10 14, 0xB97),  -- 62 51 2d 48 fe d6    vpaddd zmm10, zmm10, zmm14
  (0xB97, .vpaddd 11 11 15, 0xB9D),  -- 62 51 25 48 fe df    vpaddd zmm11, zmm11, zmm15
  (0xB9D, .vpxord 4 4 8, 0xBA3),  -- 62 d1 5d 48 ef e0    vpxord zmm4, zmm4, zmm8
  (0xBA3, .vpxord 5 5 9, 0xBA9),  -- 62 d1 55 48 ef e9    vpxord zmm5, zmm5, zmm9
  (0xBA9, .vpxord 6 6 10, 0xBAF),  -- 62 d1 4d 48 ef f2    vpxord zmm6, zmm6, zmm10
  (0xBAF, .vpxord 7 7 11, 0xBB5),  -- 62 d1 45 48 ef fb    vpxord zmm7, zmm7, zmm11
  (0xBB5, .vprord 4 4 7, 0xBBC),  -- 62 f1 5d 48 72 c4 07 vprord zmm4, zmm4, 0x7
  (0xBBC, .vprord 5 5 7, 0xBC3),  -- 62 f1 55 48 72 c5 07 vprord zmm5, zmm5, 0x7
  (0xBC3, .vprord 6 6 7, 0xBCA),  -- 62 f1 4d 48 72 c6 07 vprord zmm6, zmm6, 0x7
  (0xBCA, .vprord 7 7 7, 0xBD1),  -- 62 f1 45 48 72 c7 07 vprord zmm7, zmm7, 0x7
  (0xBD1, .vpaddd 0 0 22, 0xBD7),  -- 62 b1 7d 48 fe c6    vpaddd zmm0, zmm0, zmm22
  (0xBD7, .vpaddd 1 1 25, 0xBDD),  -- 62 91 75 48 fe c9    vpaddd zmm1, zmm1, zmm25
  (0xBDD, .vpaddd 2 2 27, 0xBE3),  -- 62 91 6d 48 fe d3    vpaddd zmm2, zmm2, zmm27
  (0xBE3, .vpaddd 3 3 24, 0xBE9),  -- 62 91 65 48 fe d8    vpaddd zmm3, zmm3, zmm24
  (0xBE9, .vpaddd 0 0 5, 0xBEF),  -- 62 f1 7d 48 fe c5    vpaddd zmm0, zmm0, zmm5
  (0xBEF, .vpaddd 1 1 6, 0xBF5),  -- 62 f1 75 48 fe ce    vpaddd zmm1, zmm1, zmm6
  (0xBF5, .vpaddd 2 2 7, 0xBFB),  -- 62 f1 6d 48 fe d7    vpaddd zmm2, zmm2, zmm7
  (0xBFB, .vpaddd 3 3 4, 0xC01),  -- 62 f1 65 48 fe dc    vpaddd zmm3, zmm3, zmm4
  (0xC01, .vpxord 15 15 0, 0xC07),  -- 62 71 05 48 ef f8    vpxord zmm15, zmm15, zmm0
  (0xC07, .vpxord 12 12 1, 0xC0D),  -- 62 71 1d 48 ef e1    vpxord zmm12, zmm12, zmm1
  (0xC0D, .vpxord 13 13 2, 0xC13),  -- 62 71 15 48 ef ea    vpxord zmm13, zmm13, zmm2
  (0xC13, .vpxord 14 14 3, 0xC19),  -- 62 71 0d 48 ef f3    vpxord zmm14, zmm14, zmm3
  (0xC19, .vprord 15 15 16, 0xC20),  -- 62 d1 05 48 72 c7 10 vprord zmm15, zmm15, 0x10
  (0xC20, .vprord 12 12 16, 0xC27),  -- 62 d1 1d 48 72 c4 10 vprord zmm12, zmm12, 0x10
  (0xC27, .vprord 13 13 16, 0xC2E),  -- 62 d1 15 48 72 c5 10 vprord zmm13, zmm13, 0x10
  (0xC2E, .vprord 14 14 16, 0xC35),  -- 62 d1 0d 48 72 c6 10 vprord zmm14, zmm14, 0x10
  (0xC35, .vpaddd 10 10 15, 0xC3B),  -- 62 51 2d 48 fe d7    vpaddd zmm10, zmm10, zmm15
  (0xC3B, .vpaddd 11 11 12, 0xC41),  -- 62 51 25 48 fe dc    vpaddd zmm11, zmm11, zmm12
  (0xC41, .vpaddd 8 8 13, 0xC47),  -- 62 51 3d 48 fe c5    vpaddd zmm8, zmm8, zmm13
  (0xC47, .vpaddd 9 9 14, 0xC4D),  -- 62 51 35 48 fe ce    vpaddd zmm9, zmm9, zmm14
  (0xC4D, .vpxord 5 5 10, 0xC53),  -- 62 d1 55 48 ef ea    vpxord zmm5, zmm5, zmm10
  (0xC53, .vpxord 6 6 11, 0xC59),  -- 62 d1 4d 48 ef f3    vpxord zmm6, zmm6, zmm11
  (0xC59, .vpxord 7 7 8, 0xC5F),  -- 62 d1 45 48 ef f8    vpxord zmm7, zmm7, zmm8
  (0xC5F, .vpxord 4 4 9, 0xC65),  -- 62 d1 5d 48 ef e1    vpxord zmm4, zmm4, zmm9
  (0xC65, .vprord 5 5 12, 0xC6C),  -- 62 f1 55 48 72 c5 0c vprord zmm5, zmm5, 0xc
  (0xC6C, .vprord 6 6 12, 0xC73),  -- 62 f1 4d 48 72 c6 0c vprord zmm6, zmm6, 0xc
  (0xC73, .vprord 7 7 12, 0xC7A),  -- 62 f1 45 48 72 c7 0c vprord zmm7, zmm7, 0xc
  (0xC7A, .vprord 4 4 12, 0xC81),  -- 62 f1 5d 48 72 c4 0c vprord zmm4, zmm4, 0xc
  (0xC81, .vpaddd 0 0 21, 0xC87),  -- 62 b1 7d 48 fe c5    vpaddd zmm0, zmm0, zmm21
  (0xC87, .vpaddd 1 1 16, 0xC8D),  -- 62 b1 75 48 fe c8    vpaddd zmm1, zmm1, zmm16
  (0xC8D, .vpaddd 2 2 31, 0xC93),  -- 62 91 6d 48 fe d7    vpaddd zmm2, zmm2, zmm31
  (0xC93, .vpaddd 3 3 17, 0xC99),  -- 62 b1 65 48 fe d9    vpaddd zmm3, zmm3, zmm17
  (0xC99, .vpaddd 0 0 5, 0xC9F),  -- 62 f1 7d 48 fe c5    vpaddd zmm0, zmm0, zmm5
  (0xC9F, .vpaddd 1 1 6, 0xCA5),  -- 62 f1 75 48 fe ce    vpaddd zmm1, zmm1, zmm6
  (0xCA5, .vpaddd 2 2 7, 0xCAB),  -- 62 f1 6d 48 fe d7    vpaddd zmm2, zmm2, zmm7
  (0xCAB, .vpaddd 3 3 4, 0xCB1),  -- 62 f1 65 48 fe dc    vpaddd zmm3, zmm3, zmm4
  (0xCB1, .vpxord 15 15 0, 0xCB7),  -- 62 71 05 48 ef f8    vpxord zmm15, zmm15, zmm0
  (0xCB7, .vpxord 12 12 1, 0xCBD),  -- 62 71 1d 48 ef e1    vpxord zmm12, zmm12, zmm1
  (0xCBD, .vpxord 13 13 2, 0xCC3),  -- 62 71 15 48 ef ea    vpxord zmm13, zmm13, zmm2
  (0xCC3, .vpxord 14 14 3, 0xCC9),  -- 62 71 0d 48 ef f3    vpxord zmm14, zmm14, zmm3
  (0xCC9, .vprord 15 15 8, 0xCD0),  -- 62 d1 05 48 72 c7 08 vprord zmm15, zmm15, 0x8
  (0xCD0, .vprord 12 12 8, 0xCD7),  -- 62 d1 1d 48 72 c4 08 vprord zmm12, zmm12, 0x8
  (0xCD7, .vprord 13 13 8, 0xCDE),  -- 62 d1 15 48 72 c5 08 vprord zmm13, zmm13, 0x8
  (0xCDE, .vprord 14 14 8, 0xCE5),  -- 62 d1 0d 48 72 c6 08 vprord zmm14, zmm14, 0x8
  (0xCE5, .vpaddd 10 10 15, 0xCEB),  -- 62 51 2d 48 fe d7    vpaddd zmm10, zmm10, zmm15
  (0xCEB, .vpaddd 11 11 12, 0xCF1),  -- 62 51 25 48 fe dc    vpaddd zmm11, zmm11, zmm12
  (0xCF1, .vpaddd 8 8 13, 0xCF7),  -- 62 51 3d 48 fe c5    vpaddd zmm8, zmm8, zmm13
  (0xCF7, .vpaddd 9 9 14, 0xCFD),  -- 62 51 35 48 fe ce    vpaddd zmm9, zmm9, zmm14
  (0xCFD, .vpxord 5 5 10, 0xD03),  -- 62 d1 55 48 ef ea    vpxord zmm5, zmm5, zmm10
  (0xD03, .vpxord 6 6 11, 0xD09),  -- 62 d1 4d 48 ef f3    vpxord zmm6, zmm6, zmm11
  (0xD09, .vpxord 7 7 8, 0xD0F),  -- 62 d1 45 48 ef f8    vpxord zmm7, zmm7, zmm8
  (0xD0F, .vpxord 4 4 9, 0xD15),  -- 62 d1 5d 48 ef e1    vpxord zmm4, zmm4, zmm9
  (0xD15, .vprord 5 5 7, 0xD1C),  -- 62 f1 55 48 72 c5 07 vprord zmm5, zmm5, 0x7
  (0xD1C, .vprord 6 6 7, 0xD23),  -- 62 f1 4d 48 72 c6 07 vprord zmm6, zmm6, 0x7
  (0xD23, .vprord 7 7 7, 0xD2A),  -- 62 f1 45 48 72 c7 07 vprord zmm7, zmm7, 0x7
  (0xD2A, .vprord 4 4 7, 0xD31),  -- 62 f1 5d 48 72 c4 07 vprord zmm4, zmm4, 0x7
  (0xD31, .vpaddd 0 0 26, 0xD37),  -- 62 91 7d 48 fe c2    vpaddd zmm0, zmm0, zmm26
  (0xD37, .vpaddd 1 1 28, 0xD3D),  -- 62 91 75 48 fe cc    vpaddd zmm1, zmm1, zmm28
  (0xD3D, .vpaddd 2 2 30, 0xD43),  -- 62 91 6d 48 fe d6    vpaddd zmm2, zmm2, zmm30
  (0xD43, .vpaddd 3 3 29, 0xD49),  -- 62 91 65 48 fe dd    vpaddd zmm3, zmm3, zmm29
  (0xD49, .vpaddd 0 0 4, 0xD4F),  -- 62 f1 7d 48 fe c4    vpaddd zmm0, zmm0, zmm4
  (0xD4F, .vpaddd 1 1 5, 0xD55),  -- 62 f1 75 48 fe cd    vpaddd zmm1, zmm1, zmm5
  (0xD55, .vpaddd 2 2 6, 0xD5B),  -- 62 f1 6d 48 fe d6    vpaddd zmm2, zmm2, zmm6
  (0xD5B, .vpaddd 3 3 7, 0xD61),  -- 62 f1 65 48 fe df    vpaddd zmm3, zmm3, zmm7
  (0xD61, .vpxord 12 12 0, 0xD67),  -- 62 71 1d 48 ef e0    vpxord zmm12, zmm12, zmm0
  (0xD67, .vpxord 13 13 1, 0xD6D),  -- 62 71 15 48 ef e9    vpxord zmm13, zmm13, zmm1
  (0xD6D, .vpxord 14 14 2, 0xD73),  -- 62 71 0d 48 ef f2    vpxord zmm14, zmm14, zmm2
  (0xD73, .vpxord 15 15 3, 0xD79),  -- 62 71 05 48 ef fb    vpxord zmm15, zmm15, zmm3
  (0xD79, .vprord 12 12 16, 0xD80),  -- 62 d1 1d 48 72 c4 10 vprord zmm12, zmm12, 0x10
  (0xD80, .vprord 13 13 16, 0xD87),  -- 62 d1 15 48 72 c5 10 vprord zmm13, zmm13, 0x10
  (0xD87, .vprord 14 14 16, 0xD8E),  -- 62 d1 0d 48 72 c6 10 vprord zmm14, zmm14, 0x10
  (0xD8E, .vprord 15 15 16, 0xD95),  -- 62 d1 05 48 72 c7 10 vprord zmm15, zmm15, 0x10
  (0xD95, .vpaddd 8 8 12, 0xD9B),  -- 62 51 3d 48 fe c4    vpaddd zmm8, zmm8, zmm12
  (0xD9B, .vpaddd 9 9 13, 0xDA1),  -- 62 51 35 48 fe cd    vpaddd zmm9, zmm9, zmm13
  (0xDA1, .vpaddd 10 10 14, 0xDA7),  -- 62 51 2d 48 fe d6    vpaddd zmm10, zmm10, zmm14
  (0xDA7, .vpaddd 11 11 15, 0xDAD),  -- 62 51 25 48 fe df    vpaddd zmm11, zmm11, zmm15
  (0xDAD, .vpxord 4 4 8, 0xDB3),  -- 62 d1 5d 48 ef e0    vpxord zmm4, zmm4, zmm8
  (0xDB3, .vpxord 5 5 9, 0xDB9),  -- 62 d1 55 48 ef e9    vpxord zmm5, zmm5, zmm9
  (0xDB9, .vpxord 6 6 10, 0xDBF),  -- 62 d1 4d 48 ef f2    vpxord zmm6, zmm6, zmm10
  (0xDBF, .vpxord 7 7 11, 0xDC5),  -- 62 d1 45 48 ef fb    vpxord zmm7, zmm7, zmm11
  (0xDC5, .vprord 4 4 12, 0xDCC),  -- 62 f1 5d 48 72 c4 0c vprord zmm4, zmm4, 0xc
  (0xDCC, .vprord 5 5 12, 0xDD3),  -- 62 f1 55 48 72 c5 0c vprord zmm5, zmm5, 0xc
  (0xDD3, .vprord 6 6 12, 0xDDA),  -- 62 f1 4d 48 72 c6 0c vprord zmm6, zmm6, 0xc
  (0xDDA, .vprord 7 7 12, 0xDE1),  -- 62 f1 45 48 72 c7 0c vprord zmm7, zmm7, 0xc
  (0xDE1, .vpaddd 0 0 23, 0xDE7),  -- 62 b1 7d 48 fe c7    vpaddd zmm0, zmm0, zmm23
  (0xDE7, .vpaddd 1 1 25, 0xDED),  -- 62 91 75 48 fe c9    vpaddd zmm1, zmm1, zmm25
  (0xDED, .vpaddd 2 2 19, 0xDF3),  -- 62 b1 6d 48 fe d3    vpaddd zmm2, zmm2, zmm19
  (0xDF3, .vpaddd 3 3 31, 0xDF9),  -- 62 91 65 48 fe df    vpaddd zmm3, zmm3, zmm31
  (0xDF9, .vpaddd 0 0 4, 0xDFF),  -- 62 f1 7d 48 fe c4    vpaddd zmm0, zmm0, zmm4
  (0xDFF, .vpaddd 1 1 5, 0xE05),  -- 62 f1 75 48 fe cd    vpaddd zmm1, zmm1, zmm5
  (0xE05, .vpaddd 2 2 6, 0xE0B),  -- 62 f1 6d 48 fe d6    vpaddd zmm2, zmm2, zmm6
  (0xE0B, .vpaddd 3 3 7, 0xE11),  -- 62 f1 65 48 fe df    vpaddd zmm3, zmm3, zmm7
  (0xE11, .vpxord 12 12 0, 0xE17),  -- 62 71 1d 48 ef e0    vpxord zmm12, zmm12, zmm0
  (0xE17, .vpxord 13 13 1, 0xE1D),  -- 62 71 15 48 ef e9    vpxord zmm13, zmm13, zmm1
  (0xE1D, .vpxord 14 14 2, 0xE23),  -- 62 71 0d 48 ef f2    vpxord zmm14, zmm14, zmm2
  (0xE23, .vpxord 15 15 3, 0xE29),  -- 62 71 05 48 ef fb    vpxord zmm15, zmm15, zmm3
  (0xE29, .vprord 12 12 8, 0xE30),  -- 62 d1 1d 48 72 c4 08 vprord zmm12, zmm12, 0x8
  (0xE30, .vprord 13 13 8, 0xE37),  -- 62 d1 15 48 72 c5 08 vprord zmm13, zmm13, 0x8
  (0xE37, .vprord 14 14 8, 0xE3E),  -- 62 d1 0d 48 72 c6 08 vprord zmm14, zmm14, 0x8
  (0xE3E, .vprord 15 15 8, 0xE45),  -- 62 d1 05 48 72 c7 08 vprord zmm15, zmm15, 0x8
  (0xE45, .vpaddd 8 8 12, 0xE4B),  -- 62 51 3d 48 fe c4    vpaddd zmm8, zmm8, zmm12
  (0xE4B, .vpaddd 9 9 13, 0xE51),  -- 62 51 35 48 fe cd    vpaddd zmm9, zmm9, zmm13
  (0xE51, .vpaddd 10 10 14, 0xE57),  -- 62 51 2d 48 fe d6    vpaddd zmm10, zmm10, zmm14
  (0xE57, .vpaddd 11 11 15, 0xE5D),  -- 62 51 25 48 fe df    vpaddd zmm11, zmm11, zmm15
  (0xE5D, .vpxord 4 4 8, 0xE63),  -- 62 d1 5d 48 ef e0    vpxord zmm4, zmm4, zmm8
  (0xE63, .vpxord 5 5 9, 0xE69),  -- 62 d1 55 48 ef e9    vpxord zmm5, zmm5, zmm9
  (0xE69, .vpxord 6 6 10, 0xE6F),  -- 62 d1 4d 48 ef f2    vpxord zmm6, zmm6, zmm10
  (0xE6F, .vpxord 7 7 11, 0xE75),  -- 62 d1 45 48 ef fb    vpxord zmm7, zmm7, zmm11
  (0xE75, .vprord 4 4 7, 0xE7C),  -- 62 f1 5d 48 72 c4 07 vprord zmm4, zmm4, 0x7
  (0xE7C, .vprord 5 5 7, 0xE83),  -- 62 f1 55 48 72 c5 07 vprord zmm5, zmm5, 0x7
  (0xE83, .vprord 6 6 7, 0xE8A),  -- 62 f1 4d 48 72 c6 07 vprord zmm6, zmm6, 0x7
  (0xE8A, .vprord 7 7 7, 0xE91),  -- 62 f1 45 48 72 c7 07 vprord zmm7, zmm7, 0x7
  (0xE91, .vpaddd 0 0 20, 0xE97),  -- 62 b1 7d 48 fe c4    vpaddd zmm0, zmm0, zmm20
  (0xE97, .vpaddd 1 1 27, 0xE9D),  -- 62 91 75 48 fe cb    vpaddd zmm1, zmm1, zmm27
  (0xE9D, .vpaddd 2 2 21, 0xEA3),  -- 62 b1 6d 48 fe d5    vpaddd zmm2, zmm2, zmm21
  (0xEA3, .vpaddd 3 3 17, 0xEA9),  -- 62 b1 65 48 fe d9    vpaddd zmm3, zmm3, zmm17
  (0xEA9, .vpaddd 0 0 5, 0xEAF),  -- 62 f1 7d 48 fe c5    vpaddd zmm0, zmm0, zmm5
  (0xEAF, .vpaddd 1 1 6, 0xEB5),  -- 62 f1 75 48 fe ce    vpaddd zmm1, zmm1, zmm6
  (0xEB5, .vpaddd 2 2 7, 0xEBB),  -- 62 f1 6d 48 fe d7    vpaddd zmm2, zmm2, zmm7
  (0xEBB, .vpaddd 3 3 4, 0xEC1),  -- 62 f1 65 48 fe dc    vpaddd zmm3, zmm3, zmm4
  (0xEC1, .vpxord 15 15 0, 0xEC7),  -- 62 71 05 48 ef f8    vpxord zmm15, zmm15, zmm0
  (0xEC7, .vpxord 12 12 1, 0xECD),  -- 62 71 1d 48 ef e1    vpxord zmm12, zmm12, zmm1
  (0xECD, .vpxord 13 13 2, 0xED3),  -- 62 71 15 48 ef ea    vpxord zmm13, zmm13, zmm2
  (0xED3, .vpxord 14 14 3, 0xED9),  -- 62 71 0d 48 ef f3    vpxord zmm14, zmm14, zmm3
  (0xED9, .vprord 15 15 16, 0xEE0),  -- 62 d1 05 48 72 c7 10 vprord zmm15, zmm15, 0x10
  (0xEE0, .vprord 12 12 16, 0xEE7),  -- 62 d1 1d 48 72 c4 10 vprord zmm12, zmm12, 0x10
  (0xEE7, .vprord 13 13 16, 0xEEE),  -- 62 d1 15 48 72 c5 10 vprord zmm13, zmm13, 0x10
  (0xEEE, .vprord 14 14 16, 0xEF5),  -- 62 d1 0d 48 72 c6 10 vprord zmm14, zmm14, 0x10
  (0xEF5, .vpaddd 10 10 15, 0xEFB),  -- 62 51 2d 48 fe d7    vpaddd zmm10, zmm10, zmm15
  (0xEFB, .vpaddd 11 11 12, 0xF01),  -- 62 51 25 48 fe dc    vpaddd zmm11, zmm11, zmm12
  (0xF01, .vpaddd 8 8 13, 0xF07),  -- 62 51 3d 48 fe c5    vpaddd zmm8, zmm8, zmm13
  (0xF07, .vpaddd 9 9 14, 0xF0D),  -- 62 51 35 48 fe ce    vpaddd zmm9, zmm9, zmm14
  (0xF0D, .vpxord 5 5 10, 0xF13),  -- 62 d1 55 48 ef ea    vpxord zmm5, zmm5, zmm10
  (0xF13, .vpxord 6 6 11, 0xF19),  -- 62 d1 4d 48 ef f3    vpxord zmm6, zmm6, zmm11
  (0xF19, .vpxord 7 7 8, 0xF1F),  -- 62 d1 45 48 ef f8    vpxord zmm7, zmm7, zmm8
  (0xF1F, .vpxord 4 4 9, 0xF25),  -- 62 d1 5d 48 ef e1    vpxord zmm4, zmm4, zmm9
  (0xF25, .vprord 5 5 12, 0xF2C),  -- 62 f1 55 48 72 c5 0c vprord zmm5, zmm5, 0xc
  (0xF2C, .vprord 6 6 12, 0xF33),  -- 62 f1 4d 48 72 c6 0c vprord zmm6, zmm6, 0xc
  (0xF33, .vprord 7 7 12, 0xF3A),  -- 62 f1 45 48 72 c7 0c vprord zmm7, zmm7, 0xc
  (0xF3A, .vprord 4 4 12, 0xF41),  -- 62 f1 5d 48 72 c4 0c vprord zmm4, zmm4, 0xc
  (0xF41, .vpaddd 0 0 16, 0xF47),  -- 62 b1 7d 48 fe c0    vpaddd zmm0, zmm0, zmm16
  (0xF47, .vpaddd 1 1 18, 0xF4D),  -- 62 b1 75 48 fe ca    vpaddd zmm1, zmm1, zmm18
  (0xF4D, .vpaddd 2 2 24, 0xF53),  -- 62 91 6d 48 fe d0    vpaddd zmm2, zmm2, zmm24
  (0xF53, .vpaddd 3 3 22, 0xF59),  -- 62 b1 65 48 fe de    vpaddd zmm3, zmm3, zmm22
  (0xF59, .vpaddd 0 0 5, 0xF5F),  -- 62 f1 7d 48 fe c5    vpaddd zmm0, zmm0, zmm5
  (0xF5F, .vpaddd 1 1 6, 0xF65),  -- 62 f1 75 48 fe ce    vpaddd zmm1, zmm1, zmm6
  (0xF65, .vpaddd 2 2 7, 0xF6B),  -- 62 f1 6d 48 fe d7    vpaddd zmm2, zmm2, zmm7
  (0xF6B, .vpaddd 3 3 4, 0xF71),  -- 62 f1 65 48 fe dc    vpaddd zmm3, zmm3, zmm4
  (0xF71, .vpxord 15 15 0, 0xF77),  -- 62 71 05 48 ef f8    vpxord zmm15, zmm15, zmm0
  (0xF77, .vpxord 12 12 1, 0xF7D),  -- 62 71 1d 48 ef e1    vpxord zmm12, zmm12, zmm1
  (0xF7D, .vpxord 13 13 2, 0xF83),  -- 62 71 15 48 ef ea    vpxord zmm13, zmm13, zmm2
  (0xF83, .vpxord 14 14 3, 0xF89),  -- 62 71 0d 48 ef f3    vpxord zmm14, zmm14, zmm3
  (0xF89, .vprord 15 15 8, 0xF90),  -- 62 d1 05 48 72 c7 08 vprord zmm15, zmm15, 0x8
  (0xF90, .vprord 12 12 8, 0xF97),  -- 62 d1 1d 48 72 c4 08 vprord zmm12, zmm12, 0x8
  (0xF97, .vprord 13 13 8, 0xF9E),  -- 62 d1 15 48 72 c5 08 vprord zmm13, zmm13, 0x8
  (0xF9E, .vprord 14 14 8, 0xFA5),  -- 62 d1 0d 48 72 c6 08 vprord zmm14, zmm14, 0x8
  (0xFA5, .vpaddd 10 10 15, 0xFAB),  -- 62 51 2d 48 fe d7    vpaddd zmm10, zmm10, zmm15
  (0xFAB, .vpaddd 11 11 12, 0xFB1),  -- 62 51 25 48 fe dc    vpaddd zmm11, zmm11, zmm12
  (0xFB1, .vpaddd 8 8 13, 0xFB7),  -- 62 51 3d 48 fe c5    vpaddd zmm8, zmm8, zmm13
  (0xFB7, .vpaddd 9 9 14, 0xFBD),  -- 62 51 35 48 fe ce    vpaddd zmm9, zmm9, zmm14
  (0xFBD, .vpxord 5 5 10, 0xFC3),  -- 62 d1 55 48 ef ea    vpxord zmm5, zmm5, zmm10
  (0xFC3, .vpxord 6 6 11, 0xFC9),  -- 62 d1 4d 48 ef f3    vpxord zmm6, zmm6, zmm11
  (0xFC9, .vpxord 7 7 8, 0xFCF),  -- 62 d1 45 48 ef f8    vpxord zmm7, zmm7, zmm8
  (0xFCF, .vpxord 4 4 9, 0xFD5),  -- 62 d1 5d 48 ef e1    vpxord zmm4, zmm4, zmm9
  (0xFD5, .vprord 5 5 7, 0xFDC),  -- 62 f1 55 48 72 c5 07 vprord zmm5, zmm5, 0x7
  (0xFDC, .vprord 6 6 7, 0xFE3),  -- 62 f1 4d 48 72 c6 07 vprord zmm6, zmm6, 0x7
  (0xFE3, .vprord 7 7 7, 0xFEA),  -- 62 f1 45 48 72 c7 07 vprord zmm7, zmm7, 0x7
  (0xFEA, .vprord 4 4 7, 0xFF1),  -- 62 f1 5d 48 72 c4 07 vprord zmm4, zmm4, 0x7
  (0xFF1, .vpaddd 0 0 28, 0xFF7),  -- 62 91 7d 48 fe c4    vpaddd zmm0, zmm0, zmm28
  (0xFF7, .vpaddd 1 1 25, 0xFFD),  -- 62 91 75 48 fe c9    vpaddd zmm1, zmm1, zmm25
  (0xFFD, .vpaddd 2 2 31, 0x1003),  -- 62 91 6d 48 fe d7    vpaddd zmm2, zmm2, zmm31
  (0x1003, .vpaddd 3 3 30, 0x1009),  -- 62 91 65 48 fe de    vpaddd zmm3, zmm3, zmm30
  (0x1009, .vpaddd 0 0 4, 0x100F),  -- 62 f1 7d 48 fe c4    vpaddd zmm0, zmm0, zmm4
  (0x100F, .vpaddd 1 1 5, 0x1015),  -- 62 f1 75 48 fe cd    vpaddd zmm1, zmm1, zmm5
  (0x1015, .vpaddd 2 2 6, 0x101B),  -- 62 f1 6d 48 fe d6    vpaddd zmm2, zmm2, zmm6
  (0x101B, .vpaddd 3 3 7, 0x1021),  -- 62 f1 65 48 fe df    vpaddd zmm3, zmm3, zmm7
  (0x1021, .vpxord 12 12 0, 0x1027),  -- 62 71 1d 48 ef e0    vpxord zmm12, zmm12, zmm0
  (0x1027, .vpxord 13 13 1, 0x102D),  -- 62 71 15 48 ef e9    vpxord zmm13, zmm13, zmm1
  (0x102D, .vpxord 14 14 2, 0x1033),  -- 62 71 0d 48 ef f2    vpxord zmm14, zmm14, zmm2
  (0x1033, .vpxord 15 15 3, 0x1039),  -- 62 71 05 48 ef fb    vpxord zmm15, zmm15, zmm3
  (0x1039, .vprord 12 12 16, 0x1040),  -- 62 d1 1d 48 72 c4 10 vprord zmm12, zmm12, 0x10
  (0x1040, .vprord 13 13 16, 0x1047),  -- 62 d1 15 48 72 c5 10 vprord zmm13, zmm13, 0x10
  (0x1047, .vprord 14 14 16, 0x104E),  -- 62 d1 0d 48 72 c6 10 vprord zmm14, zmm14, 0x10
  (0x104E, .vprord 15 15 16, 0x1055),  -- 62 d1 05 48 72 c7 10 vprord zmm15, zmm15, 0x10
  (0x1055, .vpaddd 8 8 12, 0x105B),  -- 62 51 3d 48 fe c4    vpaddd zmm8, zmm8, zmm12
  (0x105B, .vpaddd 9 9 13, 0x1061),  -- 62 51 35 48 fe cd    vpaddd zmm9, zmm9, zmm13
  (0x1061, .vpaddd 10 10 14, 0x1067),  -- 62 51 2d 48 fe d6    vpaddd zmm10, zmm10, zmm14
  (0x1067, .vpaddd 11 11 15, 0x106D),  -- 62 51 25 48 fe df    vpaddd zmm11, zmm11, zmm15
  (0x106D, .vpxord 4 4 8, 0x1073),  -- 62 d1 5d 48 ef e0    vpxord zmm4, zmm4, zmm8
  (0x1073, .vpxord 5 5 9, 0x1079),  -- 62 d1 55 48 ef e9    vpxord zmm5, zmm5, zmm9
  (0x1079, .vpxord 6 6 10, 0x107F),  -- 62 d1 4d 48 ef f2    vpxord zmm6, zmm6, zmm10
  (0x107F, .vpxord 7 7 11, 0x1085),  -- 62 d1 45 48 ef fb    vpxord zmm7, zmm7, zmm11
  (0x1085, .vprord 4 4 12, 0x108C),  -- 62 f1 5d 48 72 c4 0c vprord zmm4, zmm4, 0xc
  (0x108C, .vprord 5 5 12, 0x1093),  -- 62 f1 55 48 72 c5 0c vprord zmm5, zmm5, 0xc
  (0x1093, .vprord 6 6 12, 0x109A),  -- 62 f1 4d 48 72 c6 0c vprord zmm6, zmm6, 0xc
  (0x109A, .vprord 7 7 12, 0x10A1),  -- 62 f1 45 48 72 c7 0c vprord zmm7, zmm7, 0xc
  (0x10A1, .vpaddd 0 0 29, 0x10A7),  -- 62 91 7d 48 fe c5    vpaddd zmm0, zmm0, zmm29
  (0x10A7, .vpaddd 1 1 27, 0x10AD),  -- 62 91 75 48 fe cb    vpaddd zmm1, zmm1, zmm27
  (0x10AD, .vpaddd 2 2 26, 0x10B3),  -- 62 91 6d 48 fe d2    vpaddd zmm2, zmm2, zmm26
  (0x10B3, .vpaddd 3 3 24, 0x10B9),  -- 62 91 65 48 fe d8    vpaddd zmm3, zmm3, zmm24
  (0x10B9, .vpaddd 0 0 4, 0x10BF),  -- 62 f1 7d 48 fe c4    vpaddd zmm0, zmm0, zmm4
  (0x10BF, .vpaddd 1 1 5, 0x10C5),  -- 62 f1 75 48 fe cd    vpaddd zmm1, zmm1, zmm5
  (0x10C5, .vpaddd 2 2 6, 0x10CB),  -- 62 f1 6d 48 fe d6    vpaddd zmm2, zmm2, zmm6
  (0x10CB, .vpaddd 3 3 7, 0x10D1),  -- 62 f1 65 48 fe df    vpaddd zmm3, zmm3, zmm7
  (0x10D1, .vpxord 12 12 0, 0x10D7),  -- 62 71 1d 48 ef e0    vpxord zmm12, zmm12, zmm0
  (0x10D7, .vpxord 13 13 1, 0x10DD),  -- 62 71 15 48 ef e9    vpxord zmm13, zmm13, zmm1
  (0x10DD, .vpxord 14 14 2, 0x10E3),  -- 62 71 0d 48 ef f2    vpxord zmm14, zmm14, zmm2
  (0x10E3, .vpxord 15 15 3, 0x10E9),  -- 62 71 05 48 ef fb    vpxord zmm15, zmm15, zmm3
  (0x10E9, .vprord 12 12 8, 0x10F0),  -- 62 d1 1d 48 72 c4 08 vprord zmm12, zmm12, 0x8
  (0x10F0, .vprord 13 13 8, 0x10F7),  -- 62 d1 15 48 72 c5 08 vprord zmm13, zmm13, 0x8
  (0x10F7, .vprord 14 14 8, 0x10FE),  -- 62 d1 0d 48 72 c6 08 vprord zmm14, zmm14, 0x8
  (0x10FE, .vprord 15 15 8, 0x1105),  -- 62 d1 05 48 72 c7 08 vprord zmm15, zmm15, 0x8
  (0x1105, .vpaddd 8 8 12, 0x110B),  -- 62 51 3d 48 fe c4    vpaddd zmm8, zmm8, zmm12
  (0x110B, .vpaddd 9 9 13, 0x1111),  -- 62 51 35 48 fe cd    vpaddd zmm9, zmm9, zmm13
  (0x1111, .vpaddd 10 10 14, 0x1117),  -- 62 51 2d 48 fe d6    vpaddd zmm10, zmm10, zmm14
  (0x1117, .vpaddd 11 11 15, 0x111D),  -- 62 51 25 48 fe df    vpaddd zmm11, zmm11, zmm15
  (0x111D, .vpxord 4 4 8, 0x1123),  -- 62 d1 5d 48 ef e0    vpxord zmm4, zmm4, zmm8
  (0x1123, .vpxord 5 5 9, 0x1129),  -- 62 d1 55 48 ef e9    vpxord zmm5, zmm5, zmm9
  (0x1129, .vpxord 6 6 10, 0x112F),  -- 62 d1 4d 48 ef f2    vpxord zmm6, zmm6, zmm10
  (0x112F, .vpxord 7 7 11, 0x1135),  -- 62 d1 45 48 ef fb    vpxord zmm7, zmm7, zmm11
  (0x1135, .vprord 4 4 7, 0x113C),  -- 62 f1 5d 48 72 c4 07 vprord zmm4, zmm4, 0x7
  (0x113C, .vprord 5 5 7, 0x1143),  -- 62 f1 55 48 72 c5 07 vprord zmm5, zmm5, 0x7
  (0x1143, .vprord 6 6 7, 0x114A),  -- 62 f1 4d 48 72 c6 07 vprord zmm6, zmm6, 0x7
  (0x114A, .vprord 7 7 7, 0x1151),  -- 62 f1 45 48 72 c7 07 vprord zmm7, zmm7, 0x7
  (0x1151, .vpaddd 0 0 23, 0x1157),  -- 62 b1 7d 48 fe c7    vpaddd zmm0, zmm0, zmm23
  (0x1157, .vpaddd 1 1 21, 0x115D),  -- 62 b1 75 48 fe cd    vpaddd zmm1, zmm1, zmm21
  (0x115D, .vpaddd 2 2 16, 0x1163),  -- 62 b1 6d 48 fe d0    vpaddd zmm2, zmm2, zmm16
  (0x1163, .vpaddd 3 3 22, 0x1169),  -- 62 b1 65 48 fe de    vpaddd zmm3, zmm3, zmm22
  (0x1169, .vpaddd 0 0 5, 0x116F),  -- 62 f1 7d 48 fe c5    vpaddd zmm0, zmm0, zmm5
  (0x116F, .vpaddd 1 1 6, 0x1175),  -- 62 f1 75 48 fe ce    vpaddd zmm1, zmm1, zmm6
  (0x1175, .vpaddd 2 2 7, 0x117B),  -- 62 f1 6d 48 fe d7    vpaddd zmm2, zmm2, zmm7
  (0x117B, .vpaddd 3 3 4, 0x1181),  -- 62 f1 65 48 fe dc    vpaddd zmm3, zmm3, zmm4
  (0x1181, .vpxord 15 15 0, 0x1187),  -- 62 71 05 48 ef f8    vpxord zmm15, zmm15, zmm0
  (0x1187, .vpxord 12 12 1, 0x118D),  -- 62 71 1d 48 ef e1    vpxord zmm12, zmm12, zmm1
  (0x118D, .vpxord 13 13 2, 0x1193),  -- 62 71 15 48 ef ea    vpxord zmm13, zmm13, zmm2
  (0x1193, .vpxord 14 14 3, 0x1199),  -- 62 71 0d 48 ef f3    vpxord zmm14, zmm14, zmm3
  (0x1199, .vprord 15 15 16, 0x11A0),  -- 62 d1 05 48 72 c7 10 vprord zmm15, zmm15, 0x10
  (0x11A0, .vprord 12 12 16, 0x11A7),  -- 62 d1 1d 48 72 c4 10 vprord zmm12, zmm12, 0x10
  (0x11A7, .vprord 13 13 16, 0x11AE),  -- 62 d1 15 48 72 c5 10 vprord zmm13, zmm13, 0x10
  (0x11AE, .vprord 14 14 16, 0x11B5),  -- 62 d1 0d 48 72 c6 10 vprord zmm14, zmm14, 0x10
  (0x11B5, .vpaddd 10 10 15, 0x11BB),  -- 62 51 2d 48 fe d7    vpaddd zmm10, zmm10, zmm15
  (0x11BB, .vpaddd 11 11 12, 0x11C1),  -- 62 51 25 48 fe dc    vpaddd zmm11, zmm11, zmm12
  (0x11C1, .vpaddd 8 8 13, 0x11C7),  -- 62 51 3d 48 fe c5    vpaddd zmm8, zmm8, zmm13
  (0x11C7, .vpaddd 9 9 14, 0x11CD),  -- 62 51 35 48 fe ce    vpaddd zmm9, zmm9, zmm14
  (0x11CD, .vpxord 5 5 10, 0x11D3),  -- 62 d1 55 48 ef ea    vpxord zmm5, zmm5, zmm10
  (0x11D3, .vpxord 6 6 11, 0x11D9),  -- 62 d1 4d 48 ef f3    vpxord zmm6, zmm6, zmm11
  (0x11D9, .vpxord 7 7 8, 0x11DF),  -- 62 d1 45 48 ef f8    vpxord zmm7, zmm7, zmm8
  (0x11DF, .vpxord 4 4 9, 0x11E5),  -- 62 d1 5d 48 ef e1    vpxord zmm4, zmm4, zmm9
  (0x11E5, .vprord 5 5 12, 0x11EC),  -- 62 f1 55 48 72 c5 0c vprord zmm5, zmm5, 0xc
  (0x11EC, .vprord 6 6 12, 0x11F3),  -- 62 f1 4d 48 72 c6 0c vprord zmm6, zmm6, 0xc
  (0x11F3, .vprord 7 7 12, 0x11FA),  -- 62 f1 45 48 72 c7 0c vprord zmm7, zmm7, 0xc
  (0x11FA, .vprord 4 4 12, 0x1201),  -- 62 f1 5d 48 72 c4 0c vprord zmm4, zmm4, 0xc
  (0x1201, .vpaddd 0 0 18, 0x1207),  -- 62 b1 7d 48 fe c2    vpaddd zmm0, zmm0, zmm18
  (0x1207, .vpaddd 1 1 19, 0x120D),  -- 62 b1 75 48 fe cb    vpaddd zmm1, zmm1, zmm19
  (0x120D, .vpaddd 2 2 17, 0x1213),  -- 62 b1 6d 48 fe d1    vpaddd zmm2, zmm2, zmm17
  (0x1213, .vpaddd 3 3 20, 0x1219),  -- 62 b1 65 48 fe dc    vpaddd zmm3, zmm3, zmm20
  (0x1219, .vpaddd 0 0 5, 0x121F),  -- 62 f1 7d 48 fe c5    vpaddd zmm0, zmm0, zmm5
  (0x121F, .vpaddd 1 1 6, 0x1225),  -- 62 f1 75 48 fe ce    vpaddd zmm1, zmm1, zmm6
  (0x1225, .vpaddd 2 2 7, 0x122B),  -- 62 f1 6d 48 fe d7    vpaddd zmm2, zmm2, zmm7
  (0x122B, .vpaddd 3 3 4, 0x1231),  -- 62 f1 65 48 fe dc    vpaddd zmm3, zmm3, zmm4
  (0x1231, .vpxord 15 15 0, 0x1237),  -- 62 71 05 48 ef f8    vpxord zmm15, zmm15, zmm0
  (0x1237, .vpxord 12 12 1, 0x123D),  -- 62 71 1d 48 ef e1    vpxord zmm12, zmm12, zmm1
  (0x123D, .vpxord 13 13 2, 0x1243),  -- 62 71 15 48 ef ea    vpxord zmm13, zmm13, zmm2
  (0x1243, .vpxord 14 14 3, 0x1249),  -- 62 71 0d 48 ef f3    vpxord zmm14, zmm14, zmm3
  (0x1249, .vprord 15 15 8, 0x1250),  -- 62 d1 05 48 72 c7 08 vprord zmm15, zmm15, 0x8
  (0x1250, .vprord 12 12 8, 0x1257),  -- 62 d1 1d 48 72 c4 08 vprord zmm12, zmm12, 0x8
  (0x1257, .vprord 13 13 8, 0x125E),  -- 62 d1 15 48 72 c5 08 vprord zmm13, zmm13, 0x8
  (0x125E, .vprord 14 14 8, 0x1265),  -- 62 d1 0d 48 72 c6 08 vprord zmm14, zmm14, 0x8
  (0x1265, .vpaddd 10 10 15, 0x126B),  -- 62 51 2d 48 fe d7    vpaddd zmm10, zmm10, zmm15
  (0x126B, .vpaddd 11 11 12, 0x1271),  -- 62 51 25 48 fe dc    vpaddd zmm11, zmm11, zmm12
  (0x1271, .vpaddd 8 8 13, 0x1277),  -- 62 51 3d 48 fe c5    vpaddd zmm8, zmm8, zmm13
  (0x1277, .vpaddd 9 9 14, 0x127D),  -- 62 51 35 48 fe ce    vpaddd zmm9, zmm9, zmm14
  (0x127D, .vpxord 5 5 10, 0x1283),  -- 62 d1 55 48 ef ea    vpxord zmm5, zmm5, zmm10
  (0x1283, .vpxord 6 6 11, 0x1289),  -- 62 d1 4d 48 ef f3    vpxord zmm6, zmm6, zmm11
  (0x1289, .vpxord 7 7 8, 0x128F),  -- 62 d1 45 48 ef f8    vpxord zmm7, zmm7, zmm8
  (0x128F, .vpxord 4 4 9, 0x1295),  -- 62 d1 5d 48 ef e1    vpxord zmm4, zmm4, zmm9
  (0x1295, .vprord 5 5 7, 0x129C),  -- 62 f1 55 48 72 c5 07 vprord zmm5, zmm5, 0x7
  (0x129C, .vprord 6 6 7, 0x12A3),  -- 62 f1 4d 48 72 c6 07 vprord zmm6, zmm6, 0x7
  (0x12A3, .vprord 7 7 7, 0x12AA),  -- 62 f1 45 48 72 c7 07 vprord zmm7, zmm7, 0x7
  (0x12AA, .vprord 4 4 7, 0x12B1),  -- 62 f1 5d 48 72 c4 07 vprord zmm4, zmm4, 0x7
  (0x12B1, .vpaddd 0 0 25, 0x12B7),  -- 62 91 7d 48 fe c1    vpaddd zmm0, zmm0, zmm25
  (0x12B7, .vpaddd 1 1 27, 0x12BD),  -- 62 91 75 48 fe cb    vpaddd zmm1, zmm1, zmm27
  (0x12BD, .vpaddd 2 2 24, 0x12C3),  -- 62 91 6d 48 fe d0    vpaddd zmm2, zmm2, zmm24
  (0x12C3, .vpaddd 3 3 31, 0x12C9),  -- 62 91 65 48 fe df    vpaddd zmm3, zmm3, zmm31
  (0x12C9, .vpaddd 0 0 4, 0x12CF),  -- 62 f1 7d 48 fe c4    vpaddd zmm0, zmm0, zmm4
  (0x12CF, .vpaddd 1 1 5, 0x12D5),  -- 62 f1 75 48 fe cd    vpaddd zmm1, zmm1, zmm5
  (0x12D5, .vpaddd 2 2 6, 0x12DB),  -- 62 f1 6d 48 fe d6    vpaddd zmm2, zmm2, zmm6
  (0x12DB, .vpaddd 3 3 7, 0x12E1),  -- 62 f1 65 48 fe df    vpaddd zmm3, zmm3, zmm7
  (0x12E1, .vpxord 12 12 0, 0x12E7),  -- 62 71 1d 48 ef e0    vpxord zmm12, zmm12, zmm0
  (0x12E7, .vpxord 13 13 1, 0x12ED),  -- 62 71 15 48 ef e9    vpxord zmm13, zmm13, zmm1
  (0x12ED, .vpxord 14 14 2, 0x12F3),  -- 62 71 0d 48 ef f2    vpxord zmm14, zmm14, zmm2
  (0x12F3, .vpxord 15 15 3, 0x12F9),  -- 62 71 05 48 ef fb    vpxord zmm15, zmm15, zmm3
  (0x12F9, .vprord 12 12 16, 0x1300),  -- 62 d1 1d 48 72 c4 10 vprord zmm12, zmm12, 0x10
  (0x1300, .vprord 13 13 16, 0x1307),  -- 62 d1 15 48 72 c5 10 vprord zmm13, zmm13, 0x10
  (0x1307, .vprord 14 14 16, 0x130E),  -- 62 d1 0d 48 72 c6 10 vprord zmm14, zmm14, 0x10
  (0x130E, .vprord 15 15 16, 0x1315),  -- 62 d1 05 48 72 c7 10 vprord zmm15, zmm15, 0x10
  (0x1315, .vpaddd 8 8 12, 0x131B),  -- 62 51 3d 48 fe c4    vpaddd zmm8, zmm8, zmm12
  (0x131B, .vpaddd 9 9 13, 0x1321),  -- 62 51 35 48 fe cd    vpaddd zmm9, zmm9, zmm13
  (0x1321, .vpaddd 10 10 14, 0x1327),  -- 62 51 2d 48 fe d6    vpaddd zmm10, zmm10, zmm14
  (0x1327, .vpaddd 11 11 15, 0x132D),  -- 62 51 25 48 fe df    vpaddd zmm11, zmm11, zmm15
  (0x132D, .vpxord 4 4 8, 0x1333),  -- 62 d1 5d 48 ef e0    vpxord zmm4, zmm4, zmm8
  (0x1333, .vpxord 5 5 9, 0x1339),  -- 62 d1 55 48 ef e9    vpxord zmm5, zmm5, zmm9
  (0x1339, .vpxord 6 6 10, 0x133F),  -- 62 d1 4d 48 ef f2    vpxord zmm6, zmm6, zmm10
  (0x133F, .vpxord 7 7 11, 0x1345),  -- 62 d1 45 48 ef fb    vpxord zmm7, zmm7, zmm11
  (0x1345, .vprord 4 4 12, 0x134C),  -- 62 f1 5d 48 72 c4 0c vprord zmm4, zmm4, 0xc
  (0x134C, .vprord 5 5 12, 0x1353),  -- 62 f1 55 48 72 c5 0c vprord zmm5, zmm5, 0xc
  (0x1353, .vprord 6 6 12, 0x135A),  -- 62 f1 4d 48 72 c6 0c vprord zmm6, zmm6, 0xc
  (0x135A, .vprord 7 7 12, 0x1361),  -- 62 f1 45 48 72 c7 0c vprord zmm7, zmm7, 0xc
  (0x1361, .vpaddd 0 0 30, 0x1367),  -- 62 91 7d 48 fe c6    vpaddd zmm0, zmm0, zmm30
  (0x1367, .vpaddd 1 1 21, 0x136D),  -- 62 b1 75 48 fe cd    vpaddd zmm1, zmm1, zmm21
  (0x136D, .vpaddd 2 2 28, 0x1373),  -- 62 91 6d 48 fe d4    vpaddd zmm2, zmm2, zmm28
  (0x1373, .vpaddd 3 3 17, 0x1379),  -- 62 b1 65 48 fe d9    vpaddd zmm3, zmm3, zmm17
  (0x1379, .vpaddd 0 0 4, 0x137F),  -- 62 f1 7d 48 fe c4    vpaddd zmm0, zmm0, zmm4
  (0x137F, .vpaddd 1 1 5, 0x1385),  -- 62 f1 75 48 fe cd    vpaddd zmm1, zmm1, zmm5
  (0x1385, .vpaddd 2 2 6, 0x138B),  -- 62 f1 6d 48 fe d6    vpaddd zmm2, zmm2, zmm6
  (0x138B, .vpaddd 3 3 7, 0x1391),  -- 62 f1 65 48 fe df    vpaddd zmm3, zmm3, zmm7
  (0x1391, .vpxord 12 12 0, 0x1397),  -- 62 71 1d 48 ef e0    vpxord zmm12, zmm12, zmm0
  (0x1397, .vpxord 13 13 1, 0x139D),  -- 62 71 15 48 ef e9    vpxord zmm13, zmm13, zmm1
  (0x139D, .vpxord 14 14 2, 0x13A3),  -- 62 71 0d 48 ef f2    vpxord zmm14, zmm14, zmm2
  (0x13A3, .vpxord 15 15 3, 0x13A9),  -- 62 71 05 48 ef fb    vpxord zmm15, zmm15, zmm3
  (0x13A9, .vprord 12 12 8, 0x13B0),  -- 62 d1 1d 48 72 c4 08 vprord zmm12, zmm12, 0x8
  (0x13B0, .vprord 13 13 8, 0x13B7),  -- 62 d1 15 48 72 c5 08 vprord zmm13, zmm13, 0x8
  (0x13B7, .vprord 14 14 8, 0x13BE),  -- 62 d1 0d 48 72 c6 08 vprord zmm14, zmm14, 0x8
  (0x13BE, .vprord 15 15 8, 0x13C5),  -- 62 d1 05 48 72 c7 08 vprord zmm15, zmm15, 0x8
  (0x13C5, .vpaddd 8 8 12, 0x13CB),  -- 62 51 3d 48 fe c4    vpaddd zmm8, zmm8, zmm12
  (0x13CB, .vpaddd 9 9 13, 0x13D1),  -- 62 51 35 48 fe cd    vpaddd zmm9, zmm9, zmm13
  (0x13D1, .vpaddd 10 10 14, 0x13D7),  -- 62 51 2d 48 fe d6    vpaddd zmm10, zmm10, zmm14
  (0x13D7, .vpaddd 11 11 15, 0x13DD),  -- 62 51 25 48 fe df    vpaddd zmm11, zmm11, zmm15
  (0x13DD, .vpxord 4 4 8, 0x13E3),  -- 62 d1 5d 48 ef e0    vpxord zmm4, zmm4, zmm8
  (0x13E3, .vpxord 5 5 9, 0x13E9),  -- 62 d1 55 48 ef e9    vpxord zmm5, zmm5, zmm9
  (0x13E9, .vpxord 6 6 10, 0x13EF),  -- 62 d1 4d 48 ef f2    vpxord zmm6, zmm6, zmm10
  (0x13EF, .vpxord 7 7 11, 0x13F5),  -- 62 d1 45 48 ef fb    vpxord zmm7, zmm7, zmm11
  (0x13F5, .vprord 4 4 7, 0x13FC),  -- 62 f1 5d 48 72 c4 07 vprord zmm4, zmm4, 0x7
  (0x13FC, .vprord 5 5 7, 0x1403),  -- 62 f1 55 48 72 c5 07 vprord zmm5, zmm5, 0x7
  (0x1403, .vprord 6 6 7, 0x140A),  -- 62 f1 4d 48 72 c6 07 vprord zmm6, zmm6, 0x7
  (0x140A, .vprord 7 7 7, 0x1411),  -- 62 f1 45 48 72 c7 07 vprord zmm7, zmm7, 0x7
  (0x1411, .vpaddd 0 0 29, 0x1417),  -- 62 91 7d 48 fe c5    vpaddd zmm0, zmm0, zmm29
  (0x1417, .vpaddd 1 1 16, 0x141D),  -- 62 b1 75 48 fe c8    vpaddd zmm1, zmm1, zmm16
  (0x141D, .vpaddd 2 2 18, 0x1423),  -- 62 b1 6d 48 fe d2    vpaddd zmm2, zmm2, zmm18
  (0x1423, .vpaddd 3 3 20, 0x1429),  -- 62 b1 65 48 fe dc    vpaddd zmm3, zmm3, zmm20
  (0x1429, .vpaddd 0 0 5, 0x142F),  -- 62 f1 7d 48 fe c5    vpaddd zmm0, zmm0, zmm5
  (0x142F, .vpaddd 1 1 6, 0x1435),  -- 62 f1 75 48 fe ce    vpaddd zmm1, zmm1, zmm6
  (0x1435, .vpaddd 2 2 7, 0x143B),  -- 62 f1 6d 48 fe d7    vpaddd zmm2, zmm2, zmm7
  (0x143B, .vpaddd 3 3 4, 0x1441),  -- 62 f1 65 48 fe dc    vpaddd zmm3, zmm3, zmm4
  (0x1441, .vpxord 15 15 0, 0x1447),  -- 62 71 05 48 ef f8    vpxord zmm15, zmm15, zmm0
  (0x1447, .vpxord 12 12 1, 0x144D),  -- 62 71 1d 48 ef e1    vpxord zmm12, zmm12, zmm1
  (0x144D, .vpxord 13 13 2, 0x1453),  -- 62 71 15 48 ef ea    vpxord zmm13, zmm13, zmm2
  (0x1453, .vpxord 14 14 3, 0x1459),  -- 62 71 0d 48 ef f3    vpxord zmm14, zmm14, zmm3
  (0x1459, .vprord 15 15 16, 0x1460),  -- 62 d1 05 48 72 c7 10 vprord zmm15, zmm15, 0x10
  (0x1460, .vprord 12 12 16, 0x1467),  -- 62 d1 1d 48 72 c4 10 vprord zmm12, zmm12, 0x10
  (0x1467, .vprord 13 13 16, 0x146E),  -- 62 d1 15 48 72 c5 10 vprord zmm13, zmm13, 0x10
  (0x146E, .vprord 14 14 16, 0x1475),  -- 62 d1 0d 48 72 c6 10 vprord zmm14, zmm14, 0x10
  (0x1475, .vpaddd 10 10 15, 0x147B),  -- 62 51 2d 48 fe d7    vpaddd zmm10, zmm10, zmm15
  (0x147B, .vpaddd 11 11 12, 0x1481),  -- 62 51 25 48 fe dc    vpaddd zmm11, zmm11, zmm12
  (0x1481, .vpaddd 8 8 13, 0x1487),  -- 62 51 3d 48 fe c5    vpaddd zmm8, zmm8, zmm13
  (0x1487, .vpaddd 9 9 14, 0x148D),  -- 62 51 35 48 fe ce    vpaddd zmm9, zmm9, zmm14
  (0x148D, .vpxord 5 5 10, 0x1493),  -- 62 d1 55 48 ef ea    vpxord zmm5, zmm5, zmm10
  (0x1493, .vpxord 6 6 11, 0x1499),  -- 62 d1 4d 48 ef f3    vpxord zmm6, zmm6, zmm11
  (0x1499, .vpxord 7 7 8, 0x149F),  -- 62 d1 45 48 ef f8    vpxord zmm7, zmm7, zmm8
  (0x149F, .vpxord 4 4 9, 0x14A5),  -- 62 d1 5d 48 ef e1    vpxord zmm4, zmm4, zmm9
  (0x14A5, .vprord 5 5 12, 0x14AC),  -- 62 f1 55 48 72 c5 0c vprord zmm5, zmm5, 0xc
  (0x14AC, .vprord 6 6 12, 0x14B3),  -- 62 f1 4d 48 72 c6 0c vprord zmm6, zmm6, 0xc
  (0x14B3, .vprord 7 7 12, 0x14BA),  -- 62 f1 45 48 72 c7 0c vprord zmm7, zmm7, 0xc
  (0x14BA, .vprord 4 4 12, 0x14C1),  -- 62 f1 5d 48 72 c4 0c vprord zmm4, zmm4, 0xc
  (0x14C1, .vpaddd 0 0 19, 0x14C7),  -- 62 b1 7d 48 fe c3    vpaddd zmm0, zmm0, zmm19
  (0x14C7, .vpaddd 1 1 26, 0x14CD),  -- 62 91 75 48 fe ca    vpaddd zmm1, zmm1, zmm26
  (0x14CD, .vpaddd 2 2 22, 0x14D3),  -- 62 b1 6d 48 fe d6    vpaddd zmm2, zmm2, zmm22
  (0x14D3, .vpaddd 3 3 23, 0x14D9),  -- 62 b1 65 48 fe df    vpaddd zmm3, zmm3, zmm23
  (0x14D9, .vpaddd 0 0 5, 0x14DF),  -- 62 f1 7d 48 fe c5    vpaddd zmm0, zmm0, zmm5
  (0x14DF, .vpaddd 1 1 6, 0x14E5),  -- 62 f1 75 48 fe ce    vpaddd zmm1, zmm1, zmm6
  (0x14E5, .vpaddd 2 2 7, 0x14EB),  -- 62 f1 6d 48 fe d7    vpaddd zmm2, zmm2, zmm7
  (0x14EB, .vpaddd 3 3 4, 0x14F1),  -- 62 f1 65 48 fe dc    vpaddd zmm3, zmm3, zmm4
  (0x14F1, .vpxord 15 15 0, 0x14F7),  -- 62 71 05 48 ef f8    vpxord zmm15, zmm15, zmm0
  (0x14F7, .vpxord 12 12 1, 0x14FD),  -- 62 71 1d 48 ef e1    vpxord zmm12, zmm12, zmm1
  (0x14FD, .vpxord 13 13 2, 0x1503),  -- 62 71 15 48 ef ea    vpxord zmm13, zmm13, zmm2
  (0x1503, .vpxord 14 14 3, 0x1509),  -- 62 71 0d 48 ef f3    vpxord zmm14, zmm14, zmm3
  (0x1509, .vprord 15 15 8, 0x1510),  -- 62 d1 05 48 72 c7 08 vprord zmm15, zmm15, 0x8
  (0x1510, .vprord 12 12 8, 0x1517),  -- 62 d1 1d 48 72 c4 08 vprord zmm12, zmm12, 0x8
  (0x1517, .vprord 13 13 8, 0x151E),  -- 62 d1 15 48 72 c5 08 vprord zmm13, zmm13, 0x8
  (0x151E, .vprord 14 14 8, 0x1525),  -- 62 d1 0d 48 72 c6 08 vprord zmm14, zmm14, 0x8
  (0x1525, .vpaddd 10 10 15, 0x152B),  -- 62 51 2d 48 fe d7    vpaddd zmm10, zmm10, zmm15
  (0x152B, .vpaddd 11 11 12, 0x1531),  -- 62 51 25 48 fe dc    vpaddd zmm11, zmm11, zmm12
  (0x1531, .vpaddd 8 8 13, 0x1537),  -- 62 51 3d 48 fe c5    vpaddd zmm8, zmm8, zmm13
  (0x1537, .vpaddd 9 9 14, 0x153D),  -- 62 51 35 48 fe ce    vpaddd zmm9, zmm9, zmm14
  (0x153D, .vpxord 5 5 10, 0x1543),  -- 62 d1 55 48 ef ea    vpxord zmm5, zmm5, zmm10
  (0x1543, .vpxord 6 6 11, 0x1549),  -- 62 d1 4d 48 ef f3    vpxord zmm6, zmm6, zmm11
  (0x1549, .vpxord 7 7 8, 0x154F),  -- 62 d1 45 48 ef f8    vpxord zmm7, zmm7, zmm8
  (0x154F, .vpxord 4 4 9, 0x1555),  -- 62 d1 5d 48 ef e1    vpxord zmm4, zmm4, zmm9
  (0x1555, .vprord 5 5 7, 0x155C),  -- 62 f1 55 48 72 c5 07 vprord zmm5, zmm5, 0x7
  (0x155C, .vprord 6 6 7, 0x1563),  -- 62 f1 4d 48 72 c6 07 vprord zmm6, zmm6, 0x7
  (0x1563, .vprord 7 7 7, 0x156A),  -- 62 f1 45 48 72 c7 07 vprord zmm7, zmm7, 0x7
  (0x156A, .vprord 4 4 7, 0x1571),  -- 62 f1 5d 48 72 c4 07 vprord zmm4, zmm4, 0x7
  (0x1571, .vpaddd 0 0 27, 0x1577),  -- 62 91 7d 48 fe c3    vpaddd zmm0, zmm0, zmm27
  (0x1577, .vpaddd 1 1 21, 0x157D),  -- 62 b1 75 48 fe cd    vpaddd zmm1, zmm1, zmm21
  (0x157D, .vpaddd 2 2 17, 0x1583),  -- 62 b1 6d 48 fe d1    vpaddd zmm2, zmm2, zmm17
  (0x1583, .vpaddd 3 3 24, 0x1589),  -- 62 91 65 48 fe d8    vpaddd zmm3, zmm3, zmm24
  (0x1589, .vpaddd 0 0 4, 0x158F),  -- 62 f1 7d 48 fe c4    vpaddd zmm0, zmm0, zmm4
  (0x158F, .vpaddd 1 1 5, 0x1595),  -- 62 f1 75 48 fe cd    vpaddd zmm1, zmm1, zmm5
  (0x1595, .vpaddd 2 2 6, 0x159B),  -- 62 f1 6d 48 fe d6    vpaddd zmm2, zmm2, zmm6
  (0x159B, .vpaddd 3 3 7, 0x15A1),  -- 62 f1 65 48 fe df    vpaddd zmm3, zmm3, zmm7
  (0x15A1, .vpxord 12 12 0, 0x15A7),  -- 62 71 1d 48 ef e0    vpxord zmm12, zmm12, zmm0
  (0x15A7, .vpxord 13 13 1, 0x15AD),  -- 62 71 15 48 ef e9    vpxord zmm13, zmm13, zmm1
  (0x15AD, .vpxord 14 14 2, 0x15B3),  -- 62 71 0d 48 ef f2    vpxord zmm14, zmm14, zmm2
  (0x15B3, .vpxord 15 15 3, 0x15B9),  -- 62 71 05 48 ef fb    vpxord zmm15, zmm15, zmm3
  (0x15B9, .vprord 12 12 16, 0x15C0),  -- 62 d1 1d 48 72 c4 10 vprord zmm12, zmm12, 0x10
  (0x15C0, .vprord 13 13 16, 0x15C7),  -- 62 d1 15 48 72 c5 10 vprord zmm13, zmm13, 0x10
  (0x15C7, .vprord 14 14 16, 0x15CE),  -- 62 d1 0d 48 72 c6 10 vprord zmm14, zmm14, 0x10
  (0x15CE, .vprord 15 15 16, 0x15D5),  -- 62 d1 05 48 72 c7 10 vprord zmm15, zmm15, 0x10
  (0x15D5, .vpaddd 8 8 12, 0x15DB),  -- 62 51 3d 48 fe c4    vpaddd zmm8, zmm8, zmm12
  (0x15DB, .vpaddd 9 9 13, 0x15E1),  -- 62 51 35 48 fe cd    vpaddd zmm9, zmm9, zmm13
  (0x15E1, .vpaddd 10 10 14, 0x15E7),  -- 62 51 2d 48 fe d6    vpaddd zmm10, zmm10, zmm14
  (0x15E7, .vpaddd 11 11 15, 0x15ED),  -- 62 51 25 48 fe df    vpaddd zmm11, zmm11, zmm15
  (0x15ED, .vpxord 4 4 8, 0x15F3),  -- 62 d1 5d 48 ef e0    vpxord zmm4, zmm4, zmm8
  (0x15F3, .vpxord 5 5 9, 0x15F9),  -- 62 d1 55 48 ef e9    vpxord zmm5, zmm5, zmm9
  (0x15F9, .vpxord 6 6 10, 0x15FF),  -- 62 d1 4d 48 ef f2    vpxord zmm6, zmm6, zmm10
  (0x15FF, .vpxord 7 7 11, 0x1605),  -- 62 d1 45 48 ef fb    vpxord zmm7, zmm7, zmm11
  (0x1605, .vprord 4 4 12, 0x160C),  -- 62 f1 5d 48 72 c4 0c vprord zmm4, zmm4, 0xc
  (0x160C, .vprord 5 5 12, 0x1613),  -- 62 f1 55 48 72 c5 0c vprord zmm5, zmm5, 0xc
  (0x1613, .vprord 6 6 12, 0x161A),  -- 62 f1 4d 48 72 c6 0c vprord zmm6, zmm6, 0xc
  (0x161A, .vprord 7 7 12, 0x1621),  -- 62 f1 45 48 72 c7 0c vprord zmm7, zmm7, 0xc
  (0x1621, .vpaddd 0 0 31, 0x1627),  -- 62 91 7d 48 fe c7    vpaddd zmm0, zmm0, zmm31
  (0x1627, .vpaddd 1 1 16, 0x162D),  -- 62 b1 75 48 fe c8    vpaddd zmm1, zmm1, zmm16
  (0x162D, .vpaddd 2 2 25, 0x1633),  -- 62 91 6d 48 fe d1    vpaddd zmm2, zmm2, zmm25
  (0x1633, .vpaddd 3 3 22, 0x1639),  -- 62 b1 65 48 fe de    vpaddd zmm3, zmm3, zmm22
  (0x1639, .vpaddd 0 0 4, 0x163F),  -- 62 f1 7d 48 fe c4    vpaddd zmm0, zmm0, zmm4
  (0x163F, .vpaddd 1 1 5, 0x1645),  -- 62 f1 75 48 fe cd    vpaddd zmm1, zmm1, zmm5
  (0x1645, .vpaddd 2 2 6, 0x164B),  -- 62 f1 6d 48 fe d6    vpaddd zmm2, zmm2, zmm6
  (0x164B, .vpaddd 3 3 7, 0x1651),  -- 62 f1 65 48 fe df    vpaddd zmm3, zmm3, zmm7
  (0x1651, .vpxord 12 12 0, 0x1657),  -- 62 71 1d 48 ef e0    vpxord zmm12, zmm12, zmm0
  (0x1657, .vpxord 13 13 1, 0x165D),  -- 62 71 15 48 ef e9    vpxord zmm13, zmm13, zmm1
  (0x165D, .vpxord 14 14 2, 0x1663),  -- 62 71 0d 48 ef f2    vpxord zmm14, zmm14, zmm2
  (0x1663, .vpxord 15 15 3, 0x1669),  -- 62 71 05 48 ef fb    vpxord zmm15, zmm15, zmm3
  (0x1669, .vprord 12 12 8, 0x1670),  -- 62 d1 1d 48 72 c4 08 vprord zmm12, zmm12, 0x8
  (0x1670, .vprord 13 13 8, 0x1677),  -- 62 d1 15 48 72 c5 08 vprord zmm13, zmm13, 0x8
  (0x1677, .vprord 14 14 8, 0x167E),  -- 62 d1 0d 48 72 c6 08 vprord zmm14, zmm14, 0x8
  (0x167E, .vprord 15 15 8, 0x1685),  -- 62 d1 05 48 72 c7 08 vprord zmm15, zmm15, 0x8
  (0x1685, .vpaddd 8 8 12, 0x168B),  -- 62 51 3d 48 fe c4    vpaddd zmm8, zmm8, zmm12
  (0x168B, .vpaddd 9 9 13, 0x1691),  -- 62 51 35 48 fe cd    vpaddd zmm9, zmm9, zmm13
  (0x1691, .vpaddd 10 10 14, 0x1697),  -- 62 51 2d 48 fe d6    vpaddd zmm10, zmm10, zmm14
  (0x1697, .vpaddd 11 11 15, 0x169D),  -- 62 51 25 48 fe df    vpaddd zmm11, zmm11, zmm15
  (0x169D, .vpxord 4 4 8, 0x16A3),  -- 62 d1 5d 48 ef e0    vpxord zmm4, zmm4, zmm8
  (0x16A3, .vpxord 5 5 9, 0x16A9),  -- 62 d1 55 48 ef e9    vpxord zmm5, zmm5, zmm9
  (0x16A9, .vpxord 6 6 10, 0x16AF),  -- 62 d1 4d 48 ef f2    vpxord zmm6, zmm6, zmm10
  (0x16AF, .vpxord 7 7 11, 0x16B5),  -- 62 d1 45 48 ef fb    vpxord zmm7, zmm7, zmm11
  (0x16B5, .vprord 4 4 7, 0x16BC),  -- 62 f1 5d 48 72 c4 07 vprord zmm4, zmm4, 0x7
  (0x16BC, .vprord 5 5 7, 0x16C3),  -- 62 f1 55 48 72 c5 07 vprord zmm5, zmm5, 0x7
  (0x16C3, .vprord 6 6 7, 0x16CA),  -- 62 f1 4d 48 72 c6 07 vprord zmm6, zmm6, 0x7
  (0x16CA, .vprord 7 7 7, 0x16D1),  -- 62 f1 45 48 72 c7 07 vprord zmm7, zmm7, 0x7
  (0x16D1, .vpaddd 0 0 30, 0x16D7),  -- 62 91 7d 48 fe c6    vpaddd zmm0, zmm0, zmm30
  (0x16D7, .vpaddd 1 1 18, 0x16DD),  -- 62 b1 75 48 fe ca    vpaddd zmm1, zmm1, zmm18
  (0x16DD, .vpaddd 2 2 19, 0x16E3),  -- 62 b1 6d 48 fe d3    vpaddd zmm2, zmm2, zmm19
  (0x16E3, .vpaddd 3 3 23, 0x16E9),  -- 62 b1 65 48 fe df    vpaddd zmm3, zmm3, zmm23
  (0x16E9, .vpaddd 0 0 5, 0x16EF),  -- 62 f1 7d 48 fe c5    vpaddd zmm0, zmm0, zmm5
  (0x16EF, .vpaddd 1 1 6, 0x16F5),  -- 62 f1 75 48 fe ce    vpaddd zmm1, zmm1, zmm6
  (0x16F5, .vpaddd 2 2 7, 0x16FB),  -- 62 f1 6d 48 fe d7    vpaddd zmm2, zmm2, zmm7
  (0x16FB, .vpaddd 3 3 4, 0x1701),  -- 62 f1 65 48 fe dc    vpaddd zmm3, zmm3, zmm4
  (0x1701, .vpxord 15 15 0, 0x1707),  -- 62 71 05 48 ef f8    vpxord zmm15, zmm15, zmm0
  (0x1707, .vpxord 12 12 1, 0x170D),  -- 62 71 1d 48 ef e1    vpxord zmm12, zmm12, zmm1
  (0x170D, .vpxord 13 13 2, 0x1713),  -- 62 71 15 48 ef ea    vpxord zmm13, zmm13, zmm2
  (0x1713, .vpxord 14 14 3, 0x1719),  -- 62 71 0d 48 ef f3    vpxord zmm14, zmm14, zmm3
  (0x1719, .vprord 15 15 16, 0x1720),  -- 62 d1 05 48 72 c7 10 vprord zmm15, zmm15, 0x10
  (0x1720, .vprord 12 12 16, 0x1727),  -- 62 d1 1d 48 72 c4 10 vprord zmm12, zmm12, 0x10
  (0x1727, .vprord 13 13 16, 0x172E),  -- 62 d1 15 48 72 c5 10 vprord zmm13, zmm13, 0x10
  (0x172E, .vprord 14 14 16, 0x1735),  -- 62 d1 0d 48 72 c6 10 vprord zmm14, zmm14, 0x10
  (0x1735, .vpaddd 10 10 15, 0x173B),  -- 62 51 2d 48 fe d7    vpaddd zmm10, zmm10, zmm15
  (0x173B, .vpaddd 11 11 12, 0x1741),  -- 62 51 25 48 fe dc    vpaddd zmm11, zmm11, zmm12
  (0x1741, .vpaddd 8 8 13, 0x1747),  -- 62 51 3d 48 fe c5    vpaddd zmm8, zmm8, zmm13
  (0x1747, .vpaddd 9 9 14, 0x174D),  -- 62 51 35 48 fe ce    vpaddd zmm9, zmm9, zmm14
  (0x174D, .vpxord 5 5 10, 0x1753),  -- 62 d1 55 48 ef ea    vpxord zmm5, zmm5, zmm10
  (0x1753, .vpxord 6 6 11, 0x1759),  -- 62 d1 4d 48 ef f3    vpxord zmm6, zmm6, zmm11
  (0x1759, .vpxord 7 7 8, 0x175F),  -- 62 d1 45 48 ef f8    vpxord zmm7, zmm7, zmm8
  (0x175F, .vpxord 4 4 9, 0x1765),  -- 62 d1 5d 48 ef e1    vpxord zmm4, zmm4, zmm9
  (0x1765, .vprord 5 5 12, 0x176C),  -- 62 f1 55 48 72 c5 0c vprord zmm5, zmm5, 0xc
  (0x176C, .vprord 6 6 12, 0x1773),  -- 62 f1 4d 48 72 c6 0c vprord zmm6, zmm6, 0xc
  (0x1773, .vprord 7 7 12, 0x177A),  -- 62 f1 45 48 72 c7 0c vprord zmm7, zmm7, 0xc
  (0x177A, .vprord 4 4 12, 0x1781),  -- 62 f1 5d 48 72 c4 0c vprord zmm4, zmm4, 0xc
  (0x1781, .vpaddd 0 0 26, 0x1787),  -- 62 91 7d 48 fe c2    vpaddd zmm0, zmm0, zmm26
  (0x1787, .vpaddd 1 1 28, 0x178D),  -- 62 91 75 48 fe cc    vpaddd zmm1, zmm1, zmm28
  (0x178D, .vpaddd 2 2 20, 0x1793),  -- 62 b1 6d 48 fe d4    vpaddd zmm2, zmm2, zmm20
  (0x1793, .vpaddd 3 3 29, 0x1799),  -- 62 91 65 48 fe dd    vpaddd zmm3, zmm3, zmm29
  (0x1799, .vpaddd 0 0 5, 0x179F),  -- 62 f1 7d 48 fe c5    vpaddd zmm0, zmm0, zmm5
  (0x179F, .vpaddd 1 1 6, 0x17A5),  -- 62 f1 75 48 fe ce    vpaddd zmm1, zmm1, zmm6
  (0x17A5, .vpaddd 2 2 7, 0x17AB),  -- 62 f1 6d 48 fe d7    vpaddd zmm2, zmm2, zmm7
  (0x17AB, .vpaddd 3 3 4, 0x17B1),  -- 62 f1 65 48 fe dc    vpaddd zmm3, zmm3, zmm4
  (0x17B1, .vpxord 15 15 0, 0x17B7),  -- 62 71 05 48 ef f8    vpxord zmm15, zmm15, zmm0
  (0x17B7, .vpxord 12 12 1, 0x17BD),  -- 62 71 1d 48 ef e1    vpxord zmm12, zmm12, zmm1
  (0x17BD, .vpxord 13 13 2, 0x17C3),  -- 62 71 15 48 ef ea    vpxord zmm13, zmm13, zmm2
  (0x17C3, .vpxord 14 14 3, 0x17C9),  -- 62 71 0d 48 ef f3    vpxord zmm14, zmm14, zmm3
  (0x17C9, .vprord 15 15 8, 0x17D0),  -- 62 d1 05 48 72 c7 08 vprord zmm15, zmm15, 0x8
  (0x17D0, .vprord 12 12 8, 0x17D7),  -- 62 d1 1d 48 72 c4 08 vprord zmm12, zmm12, 0x8
  (0x17D7, .vprord 13 13 8, 0x17DE),  -- 62 d1 15 48 72 c5 08 vprord zmm13, zmm13, 0x8
  (0x17DE, .vprord 14 14 8, 0x17E5),  -- 62 d1 0d 48 72 c6 08 vprord zmm14, zmm14, 0x8
  (0x17E5, .vpaddd 10 10 15, 0x17EB),  -- 62 51 2d 48 fe d7    vpaddd zmm10, zmm10, zmm15
  (0x17EB, .vpaddd 11 11 12, 0x17F1),  -- 62 51 25 48 fe dc    vpaddd zmm11, zmm11, zmm12
  (0x17F1, .vpaddd 8 8 13, 0x17F7),  -- 62 51 3d 48 fe c5    vpaddd zmm8, zmm8, zmm13
  (0x17F7, .vpaddd 9 9 14, 0x17FD),  -- 62 51 35 48 fe ce    vpaddd zmm9, zmm9, zmm14
  (0x17FD, .vpxord 5 5 10, 0x1803),  -- 62 d1 55 48 ef ea    vpxord zmm5, zmm5, zmm10
  (0x1803, .vpxord 6 6 11, 0x1809),  -- 62 d1 4d 48 ef f3    vpxord zmm6, zmm6, zmm11
  (0x1809, .vpxord 7 7 8, 0x180F),  -- 62 d1 45 48 ef f8    vpxord zmm7, zmm7, zmm8
  (0x180F, .vpxord 4 4 9, 0x1815),  -- 62 d1 5d 48 ef e1    vpxord zmm4, zmm4, zmm9
  (0x1815, .vprord 5 5 7, 0x181C),  -- 62 f1 55 48 72 c5 07 vprord zmm5, zmm5, 0x7
  (0x181C, .vprord 6 6 7, 0x1823),  -- 62 f1 4d 48 72 c6 07 vprord zmm6, zmm6, 0x7
  (0x1823, .vprord 7 7 7, 0x182A),  -- 62 f1 45 48 72 c7 07 vprord zmm7, zmm7, 0x7
  (0x182A, .vprord 4 4 7, 0x1831)  -- 62 f1 5d 48 72 c4 07 vprord zmm4, zmm4, 0x7
]

def prog (pc : Nat) : Option (Instr × Nat) := table.lookup pc

theorem at_4F1 : prog 0x4F1 = some (.vpaddd 0 0 16, 0x4F7) := rfl
theorem at_4F7 : prog 0x4F7 = some (.vpaddd 1 1 18, 0x4FD) := rfl
theorem at_4FD : prog 0x4FD = some (.vpaddd 2 2 20, 0x503) := rfl
theorem at_503 : prog 0x503 = some (.vpaddd 3 3 22, 0x509) := rfl
theorem at_509 : prog 0x509 = some (.vpaddd 0 0 4, 0x50F) := rfl
theorem at_50F : prog 0x50F = some (.vpaddd 1 1 5, 0x515) := rfl
theorem at_515 : prog 0x515 = some (.vpaddd 2 2 6, 0x51B) := rfl
theorem at_51B : prog 0x51B = some (.vpaddd 3 3 7, 0x521) := rfl
theorem at_521 : prog 0x521 = some (.vpxord 12 12 0, 0x527) := rfl
theorem at_527 : prog 0x527 = some (.vpxord 13 13 1, 0x52D) := rfl
theorem at_52D : prog 0x52D = some (.vpxord 14 14 2, 0x533) := rfl
theorem at_533 : prog 0x533 = some (.vpxord 15 15 3, 0x539) := rfl
theorem at_539 : prog 0x539 = some (.vprord 12 12 16, 0x540) := rfl
theorem at_540 : prog 0x540 = some (.vprord 13 13 16, 0x547) := rfl
theorem at_547 : prog 0x547 = some (.vprord 14 14 16, 0x54E) := rfl
theorem at_54E : prog 0x54E = some (.vprord 15 15 16, 0x555) := rfl
theorem at_555 : prog 0x555 = some (.vpaddd 8 8 12, 0x55B) := rfl
theorem at_55B : prog 0x55B = some (.vpaddd 9 9 13, 0x561) := rfl
theorem at_561 : prog 0x561 = some (.vpaddd 10 10 14, 0x567) := rfl
theorem at_567 : prog 0x567 = some (.vpaddd 11 11 15, 0x56D) := rfl
theorem at_56D : prog 0x56D = some (.vpxord 4 4 8, 0x573) := rfl
theorem at_573 : prog 0x573 = some (.vpxord 5 5 9, 0x579) := rfl
theorem at_579 : prog 0x579 = some (.vpxord 6 6 10, 0x57F) := rfl
theorem at_57F : prog 0x57F = some (.vpxord 7 7 11, 0x585) := rfl
theorem at_585 : prog 0x585 = some (.vprord 4 4 12, 0x58C) := rfl
theorem at_58C : prog 0x58C = some (.vprord 5 5 12, 0x593) := rfl
theorem at_593 : prog 0x593 = some (.vprord 6 6 12, 0x59A) := rfl
theorem at_59A : prog 0x59A = some (.vprord 7 7 12, 0x5A1) := rfl
theorem at_5A1 : prog 0x5A1 = some (.vpaddd 0 0 17, 0x5A7) := rfl
theorem at_5A7 : prog 0x5A7 = some (.vpaddd 1 1 19, 0x5AD) := rfl
theorem at_5AD : prog 0x5AD = some (.vpaddd 2 2 21, 0x5B3) := rfl
theorem at_5B3 : prog 0x5B3 = some (.vpaddd 3 3 23, 0x5B9) := rfl
theorem at_5B9 : prog 0x5B9 = some (.vpaddd 0 0 4, 0x5BF) := rfl
theorem at_5BF : prog 0x5BF = some (.vpaddd 1 1 5, 0x5C5) := rfl
theorem at_5C5 : prog 0x5C5 = some (.vpaddd 2 2 6, 0x5CB) := rfl
theorem at_5CB : prog 0x5CB = some (.vpaddd 3 3 7, 0x5D1) := rfl
theorem at_5D1 : prog 0x5D1 = some (.vpxord 12 12 0, 0x5D7) := rfl
theorem at_5D7 : prog 0x5D7 = some (.vpxord 13 13 1, 0x5DD) := rfl
theorem at_5DD : prog 0x5DD = some (.vpxord 14 14 2, 0x5E3) := rfl
theorem at_5E3 : prog 0x5E3 = some (.vpxord 15 15 3, 0x5E9) := rfl
theorem at_5E9 : prog 0x5E9 = some (.vprord 12 12 8, 0x5F0) := rfl
theorem at_5F0 : prog 0x5F0 = some (.vprord 13 13 8, 0x5F7) := rfl
theorem at_5F7 : prog 0x5F7 = some (.vprord 14 14 8, 0x5FE) := rfl
theorem at_5FE : prog 0x5FE = some (.vprord 15 15 8, 0x605) := rfl
theorem at_605 : prog 0x605 = some (.vpaddd 8 8 12, 0x60B) := rfl
theorem at_60B : prog 0x60B = some (.vpaddd 9 9 13, 0x611) := rfl
theorem at_611 : prog 0x611 = some (.vpaddd 10 10 14, 0x617) := rfl
theorem at_617 : prog 0x617 = some (.vpaddd 11 11 15, 0x61D) := rfl
theorem at_61D : prog 0x61D = some (.vpxord 4 4 8, 0x623) := rfl
theorem at_623 : prog 0x623 = some (.vpxord 5 5 9, 0x629) := rfl
theorem at_629 : prog 0x629 = some (.vpxord 6 6 10, 0x62F) := rfl
theorem at_62F : prog 0x62F = some (.vpxord 7 7 11, 0x635) := rfl
theorem at_635 : prog 0x635 = some (.vprord 4 4 7, 0x63C) := rfl
theorem at_63C : prog 0x63C = some (.vprord 5 5 7, 0x643) := rfl
theorem at_643 : prog 0x643 = some (.vprord 6 6 7, 0x64A) := rfl
theorem at_64A : prog 0x64A = some (.vprord 7 7 7, 0x651) := rfl
theorem at_651 : prog 0x651 = some (.vpaddd 0 0 24, 0x657) := rfl
theorem at_657 : prog 0x657 = some (.vpaddd 1 1 26, 0x65D) := rfl
theorem at_65D : prog 0x65D = some (.vpaddd 2 2 28, 0x663) := rfl
theorem at_663 : prog 0x663 = some (.vpaddd 3 3 30, 0x669) := rfl
theorem at_669 : prog 0x669 = some (.vpaddd 0 0 5, 0x66F) := rfl
theorem at_66F : prog 0x66F = some (.vpaddd 1 1 6, 0x675) := rfl
theorem at_675 : prog 0x675 = some (.vpaddd 2 2 7, 0x67B) := rfl
theorem at_67B : prog 0x67B = some (.vpaddd 3 3 4, 0x681) := rfl
theorem at_681 : prog 0x681 = some (.vpxord 15 15 0, 0x687) := rfl
theorem at_687 : prog 0x687 = some (.vpxord 12 12 1, 0x68D) := rfl
theorem at_68D : prog 0x68D = some (.vpxord 13 13 2, 0x693) := rfl
theorem at_693 : prog 0x693 = some (.vpxord 14 14 3, 0x699) := rfl
theorem at_699 : prog 0x699 = some (.vprord 15 15 16, 0x6A0) := rfl
theorem at_6A0 : prog 0x6A0 = some (.vprord 12 12 16, 0x6A7) := rfl
theorem at_6A7 : prog 0x6A7 = some (.vprord 13 13 16, 0x6AE) := rfl
theorem at_6AE : prog 0x6AE = some (.vprord 14 14 16, 0x6B5) := rfl
theorem at_6B5 : prog 0x6B5 = some (.vpaddd 10 10 15, 0x6BB) := rfl
theorem at_6BB : prog 0x6BB = some (.vpaddd 11 11 12, 0x6C1) := rfl
theorem at_6C1 : prog 0x6C1 = some (.vpaddd 8 8 13, 0x6C7) := rfl
theorem at_6C7 : prog 0x6C7 = some (.vpaddd 9 9 14, 0x6CD) := rfl
theorem at_6CD : prog 0x6CD = some (.vpxord 5 5 10, 0x6D3) := rfl
theorem at_6D3 : prog 0x6D3 = some (.vpxord 6 6 11, 0x6D9) := rfl
theorem at_6D9 : prog 0x6D9 = some (.vpxord 7 7 8, 0x6DF) := rfl
theorem at_6DF : prog 0x6DF = some (.vpxord 4 4 9, 0x6E5) := rfl
theorem at_6E5 : prog 0x6E5 = some (.vprord 5 5 12, 0x6EC) := rfl
theorem at_6EC : prog 0x6EC = some (.vprord 6 6 12, 0x6F3) := rfl
theorem at_6F3 : prog 0x6F3 = some (.vprord 7 7 12, 0x6FA) := rfl
theorem at_6FA : prog 0x6FA = some (.vprord 4 4 12, 0x701) := rfl
theorem at_701 : prog 0x701 = some (.vpaddd 0 0 25, 0x707) := rfl
theorem at_707 : prog 0x707 = some (.vpaddd 1 1 27, 0x70D) := rfl
theorem at_70D : prog 0x70D = some (.vpaddd 2 2 29, 0x713) := rfl
theorem at_713 : prog 0x713 = some (.vpaddd 3 3 31, 0x719) := rfl
theorem at_719 : prog 0x719 = some (.vpaddd 0 0 5, 0x71F) := rfl
theorem at_71F : prog 0x71F = some (.vpaddd 1 1 6, 0x725) := rfl
theorem at_725 : prog 0x725 = some (.vpaddd 2 2 7, 0x72B) := rfl
theorem at_72B : prog 0x72B = some (.vpaddd 3 3 4, 0x731) := rfl
theorem at_731 : prog 0x731 = some (.vpxord 15 15 0, 0x737) := rfl
theorem at_737 : prog 0x737 = some (.vpxord 12 12 1, 0x73D) := rfl
theorem at_73D : prog 0x73D = some (.vpxord 13 13 2, 0x743) := rfl
theorem at_743 : prog 0x743 = some (.vpxord 14 14 3, 0x749) := rfl
theorem at_749 : prog 0x749 = some (.vprord 15 15 8, 0x750) := rfl
theorem at_750 : prog 0x750 = some (.vprord 12 12 8, 0x757) := rfl
theorem at_757 : prog 0x757 = some (.vprord 13 13 8, 0x75E) := rfl
theorem at_75E : prog 0x75E = some (.vprord 14 14 8, 0x765) := rfl
theorem at_765 : prog 0x765 = some (.vpaddd 10 10 15, 0x76B) := rfl
theorem at_76B : prog 0x76B = some (.vpaddd 11 11 12, 0x771) := rfl
theorem at_771 : prog 0x771 = some (.vpaddd 8 8 13, 0x777) := rfl
theorem at_777 : prog 0x777 = some (.vpaddd 9 9 14, 0x77D) := rfl
theorem at_77D : prog 0x77D = some (.vpxord 5 5 10, 0x783) := rfl
theorem at_783 : prog 0x783 = some (.vpxord 6 6 11, 0x789) := rfl
theorem at_789 : prog 0x789 = some (.vpxord 7 7 8, 0x78F) := rfl
theorem at_78F : prog 0x78F = some (.vpxord 4 4 9, 0x795) := rfl
theorem at_795 : prog 0x795 = some (.vprord 5 5 7, 0x79C) := rfl
theorem at_79C : prog 0x79C = some (.vprord 6 6 7, 0x7A3) := rfl
theorem at_7A3 : prog 0x7A3 = some (.vprord 7 7 7, 0x7AA) := rfl
theorem at_7AA : prog 0x7AA = some (.vprord 4 4 7, 0x7B1) := rfl
theorem at_7B1 : prog 0x7B1 = some (.vpaddd 0 0 18, 0x7B7) := rfl
theorem at_7B7 : prog 0x7B7 = some (.vpaddd 1 1 19, 0x7BD) := rfl
theorem at_7BD : prog 0x7BD = some (.vpaddd 2 2 23, 0x7C3) := rfl
theorem at_7C3 : prog 0x7C3 = some (.vpaddd 3 3 20, 0x7C9) := rfl
theorem at_7C9 : prog 0x7C9 = some (.vpaddd 0 0 4, 0x7CF) := rfl
theorem at_7CF : prog 0x7CF = some (.vpaddd 1 1 5, 0x7D5) := rfl
theorem at_7D5 : prog 0x7D5 = some (.vpaddd 2 2 6, 0x7DB) := rfl
theorem at_7DB : prog 0x7DB = some (.vpaddd 3 3 7, 0x7E1) := rfl
theorem at_7E1 : prog 0x7E1 = some (.vpxord 12 12 0, 0x7E7) := rfl
theorem at_7E7 : prog 0x7E7 = some (.vpxord 13 13 1, 0x7ED) := rfl
theorem at_7ED : prog 0x7ED = some (.vpxord 14 14 2, 0x7F3) := rfl
theorem at_7F3 : prog 0x7F3 = some (.vpxord 15 15 3, 0x7F9) := rfl
theorem at_7F9 : prog 0x7F9 = some (.vprord 12 12 16, 0x800) := rfl
theorem at_800 : prog 0x800 = some (.vprord 13 13 16, 0x807) := rfl
theorem at_807 : prog 0x807 = some (.vprord 14 14 16, 0x80E) := rfl
theorem at_80E : prog 0x80E = some (.vprord 15 15 16, 0x815) := rfl
theorem at_815 : prog 0x815 = some (.vpaddd 8 8 12, 0x81B) := rfl
theorem at_81B : prog 0x81B = some (.vpaddd 9 9 13, 0x821) := rfl
theorem at_821 : prog 0x821 = some (.vpaddd 10 10 14, 0x827) := rfl
theorem at_827 : prog 0x827 = some (.vpaddd 11 11 15, 0x82D) := rfl
theorem at_82D : prog 0x82D = some (.vpxord 4 4 8, 0x833) := rfl
theorem at_833 : prog 0x833 = some (.vpxord 5 5 9, 0x839) := rfl
theorem at_839 : prog 0x839 = some (.vpxord 6 6 10, 0x83F) := rfl
theorem at_83F : prog 0x83F = some (.vpxord 7 7 11, 0x845) := rfl
theorem at_845 : prog 0x845 = some (.vprord 4 4 12, 0x84C) := rfl
theorem at_84C : prog 0x84C = some (.vprord 5 5 12, 0x853) := rfl
theorem at_853 : prog 0x853 = some (.vprord 6 6 12, 0x85A) := rfl
theorem at_85A : prog 0x85A = some (.vprord 7 7 12, 0x861) := rfl
theorem at_861 : prog 0x861 = some (.vpaddd 0 0 22, 0x867) := rfl
theorem at_867 : prog 0x867 = some (.vpaddd 1 1 26, 0x86D) := rfl
theorem at_86D : prog 0x86D = some (.vpaddd 2 2 16, 0x873) := rfl
theorem at_873 : prog 0x873 = some (.vpaddd 3 3 29, 0x879) := rfl
theorem at_879 : prog 0x879 = some (.vpaddd 0 0 4, 0x87F) := rfl
theorem at_87F : prog 0x87F = some (.vpaddd 1 1 5, 0x885) := rfl
theorem at_885 : prog 0x885 = some (.vpaddd 2 2 6, 0x88B) := rfl
theorem at_88B : prog 0x88B = some (.vpaddd 3 3 7, 0x891) := rfl
theorem at_891 : prog 0x891 = some (.vpxord 12 12 0, 0x897) := rfl
theorem at_897 : prog 0x897 = some (.vpxord 13 13 1, 0x89D) := rfl
theorem at_89D : prog 0x89D = some (.vpxord 14 14 2, 0x8A3) := rfl
theorem at_8A3 : prog 0x8A3 = some (.vpxord 15 15 3, 0x8A9) := rfl
theorem at_8A9 : prog 0x8A9 = some (.vprord 12 12 8, 0x8B0) := rfl
theorem at_8B0 : prog 0x8B0 = some (.vprord 13 13 8, 0x8B7) := rfl
theorem at_8B7 : prog 0x8B7 = some (.vprord 14 14 8, 0x8BE) := rfl
theorem at_8BE : prog 0x8BE = some (.vprord 15 15 8, 0x8C5) := rfl
theorem at_8C5 : prog 0x8C5 = some (.vpaddd 8 8 12, 0x8CB) := rfl
theorem at_8CB : prog 0x8CB = some (.vpaddd 9 9 13, 0x8D1) := rfl
theorem at_8D1 : prog 0x8D1 = some (.vpaddd 10 10 14, 0x8D7) := rfl
theorem at_8D7 : prog 0x8D7 = some (.vpaddd 11 11 15, 0x8DD) := rfl
theorem at_8DD : prog 0x8DD = some (.vpxord 4 4 8, 0x8E3) := rfl
theorem at_8E3 : prog 0x8E3 = some (.vpxord 5 5 9, 0x8E9) := rfl
theorem at_8E9 : prog 0x8E9 = some (.vpxord 6 6 10, 0x8EF) := rfl
theorem at_8EF : prog 0x8EF = some (.vpxord 7 7 11, 0x8F5) := rfl
theorem at_8F5 : prog 0x8F5 = some (.vprord 4 4 7, 0x8FC) := rfl
theorem at_8FC : prog 0x8FC = some (.vprord 5 5 7, 0x903) := rfl
theorem at_903 : prog 0x903 = some (.vprord 6 6 7, 0x90A) := rfl
theorem at_90A : prog 0x90A = some (.vprord 7 7 7, 0x911) := rfl
theorem at_911 : prog 0x911 = some (.vpaddd 0 0 17, 0x917) := rfl
theorem at_917 : prog 0x917 = some (.vpaddd 1 1 28, 0x91D) := rfl
theorem at_91D : prog 0x91D = some (.vpaddd 2 2 25, 0x923) := rfl
theorem at_923 : prog 0x923 = some (.vpaddd 3 3 31, 0x929) := rfl
theorem at_929 : prog 0x929 = some (.vpaddd 0 0 5, 0x92F) := rfl
theorem at_92F : prog 0x92F = some (.vpaddd 1 1 6, 0x935) := rfl
theorem at_935 : prog 0x935 = some (.vpaddd 2 2 7, 0x93B) := rfl
theorem at_93B : prog 0x93B = some (.vpaddd 3 3 4, 0x941) := rfl
theorem at_941 : prog 0x941 = some (.vpxord 15 15 0, 0x947) := rfl
theorem at_947 : prog 0x947 = some (.vpxord 12 12 1, 0x94D) := rfl
theorem at_94D : prog 0x94D = some (.vpxord 13 13 2, 0x953) := rfl
theorem at_953 : prog 0x953 = some (.vpxord 14 14 3, 0x959) := rfl
theorem at_959 : prog 0x959 = some (.vprord 15 15 16, 0x960) := rfl
theorem at_960 : prog 0x960 = some (.vprord 12 12 16, 0x967) := rfl
theorem at_967 : prog 0x967 = some (.vprord 13 13 16, 0x96E) := rfl
theorem at_96E : prog 0x96E = some (.vprord 14 14 16, 0x975) := rfl
theorem at_975 : prog 0x975 = some (.vpaddd 10 10 15, 0x97B) := rfl
theorem at_97B : prog 0x97B = some (.vpaddd 11 11 12, 0x981) := rfl
theorem at_981 : prog 0x981 = some (.vpaddd 8 8 13, 0x987) := rfl
theorem at_987 : prog 0x987 = some (.vpaddd 9 9 14, 0x98D) := rfl
theorem at_98D : prog 0x98D = some (.vpxord 5 5 10, 0x993) := rfl
theorem at_993 : prog 0x993 = some (.vpxord 6 6 11, 0x999) := rfl
theorem at_999 : prog 0x999 = some (.vpxord 7 7 8, 0x99F) := rfl
theorem at_99F : prog 0x99F = some (.vpxord 4 4 9, 0x9A5) := rfl
theorem at_9A5 : prog 0x9A5 = some (.vprord 5 5 12, 0x9AC) := rfl
theorem at_9AC : prog 0x9AC = some (.vprord 6 6 12, 0x9B3) := rfl
theorem at_9B3 : prog 0x9B3 = some (.vprord 7 7 12, 0x9BA) := rfl
theorem at_9BA : prog 0x9BA = some (.vprord 4 4 12, 0x9C1) := rfl
theorem at_9C1 : prog 0x9C1 = some (.vpaddd 0 0 27, 0x9C7) := rfl
theorem at_9C7 : prog 0x9C7 = some (.vpaddd 1 1 21, 0x9CD) := rfl
theorem at_9CD : prog 0x9CD = some (.vpaddd 2 2 30, 0x9D3) := rfl
theorem at_9D3 : prog 0x9D3 = some (.vpaddd 3 3 24, 0x9D9) := rfl
theorem at_9D9 : prog 0x9D9 = some (.vpaddd 0 0 5, 0x9DF) := rfl
theorem at_9DF : prog 0x9DF = some (.vpaddd 1 1 6, 0x9E5) := rfl
theorem at_9E5 : prog 0x9E5 = some (.vpaddd 2 2 7, 0x9EB) := rfl
theorem at_9EB : prog 0x9EB = some (.vpaddd 3 3 4, 0x9F1) := rfl
theorem at_9F1 : prog 0x9F1 = some (.vpxord 15 15 0, 0x9F7) := rfl
theorem at_9F7 : prog 0x9F7 = some (.vpxord 12 12 1, 0x9FD) := rfl
theorem at_9FD : prog 0x9FD = some (.vpxord 13 13 2, 0xA03) := rfl
theorem at_A03 : prog 0xA03 = some (.vpxord 14 14 3, 0xA09) := rfl
theorem at_A09 : prog 0xA09 = some (.vprord 15 15 8, 0xA10) := rfl
theorem at_A10 : prog 0xA10 = some (.vprord 12 12 8, 0xA17) := rfl
theorem at_A17 : prog 0xA17 = some (.vprord 13 13 8, 0xA1E) := rfl
theorem at_A1E : prog 0xA1E = some (.vprord 14 14 8, 0xA25) := rfl
theorem at_A25 : prog 0xA25 = some (.vpaddd 10 10 15, 0xA2B) := rfl
theorem at_A2B : prog 0xA2B = some (.vpaddd 11 11 12, 0xA31) := rfl
theorem at_A31 : prog 0xA31 = some (.vpaddd 8 8 13, 0xA37) := rfl
theorem at_A37 : prog 0xA37 = some (.vpaddd 9 9 14, 0xA3D) := rfl
theorem at_A3D : prog 0xA3D = some (.vpxord 5 5 10, 0xA43) := rfl
theorem at_A43 : prog 0xA43 = some (.vpxord 6 6 11, 0xA49) := rfl
theorem at_A49 : prog 0xA49 = some (.vpxord 7 7 8, 0xA4F) := rfl
theorem at_A4F : prog 0xA4F = some (.vpxord 4 4 9, 0xA55) := rfl
theorem at_A55 : prog 0xA55 = some (.vprord 5 5 7, 0xA5C) := rfl
theorem at_A5C : prog 0xA5C = some (.vprord 6 6 7, 0xA63) := rfl
theorem at_A63 : prog 0xA63 = some (.vprord 7 7 7, 0xA6A) := rfl
theorem at_A6A : prog 0xA6A = some (.vprord 4 4 7, 0xA71) := rfl
theorem at_A71 : prog 0xA71 = some (.vpaddd 0 0 19, 0xA77) := rfl
theorem at_A77 : prog 0xA77 = some (.vpaddd 1 1 26, 0xA7D) := rfl
theorem at_A7D : prog 0xA7D = some (.vpaddd 2 2 29, 0xA83) := rfl
theorem at_A83 : prog 0xA83 = some (.vpaddd 3 3 23, 0xA89) := rfl
theorem at_A89 : prog 0xA89 = some (.vpaddd 0 0 4, 0xA8F) := rfl
theorem at_A8F : prog 0xA8F = some (.vpaddd 1 1 5, 0xA95) := rfl
theorem at_A95 : prog 0xA95 = some (.vpaddd 2 2 6, 0xA9B) := rfl
theorem at_A9B : prog 0xA9B = some (.vpaddd 3 3 7, 0xAA1) := rfl
theorem at_AA1 : prog 0xAA1 = some (.vpxord 12 12 0, 0xAA7) := rfl
theorem at_AA7 : prog 0xAA7 = some (.vpxord 13 13 1, 0xAAD) := rfl
theorem at_AAD : prog 0xAAD = some (.vpxord 14 14 2, 0xAB3) := rfl
theorem at_AB3 : prog 0xAB3 = some (.vpxord 15 15 3, 0xAB9) := rfl
theorem at_AB9 : prog 0xAB9 = some (.vprord 12 12 16, 0xAC0) := rfl
theorem at_AC0 : prog 0xAC0 = some (.vprord 13 13 16, 0xAC7) := rfl
theorem at_AC7 : prog 0xAC7 = some (.vprord 14 14 16, 0xACE) := rfl
theorem at_ACE : prog 0xACE = some (.vprord 15 15 16, 0xAD5) := rfl
theorem at_AD5 : prog 0xAD5 = some (.vpaddd 8 8 12, 0xADB) := rfl
theorem at_ADB : prog 0xADB = some (.vpaddd 9 9 13, 0xAE1) := rfl
theorem at_AE1 : prog 0xAE1 = some (.vpaddd 10 10 14, 0xAE7) := rfl
theorem at_AE7 : prog 0xAE7 = some (.vpaddd 11 11 15, 0xAED) := rfl
theorem at_AED : prog 0xAED = some (.vpxord 4 4 8, 0xAF3) := rfl
theorem at_AF3 : prog 0xAF3 = some (.vpxord 5 5 9, 0xAF9) := rfl
theorem at_AF9 : prog 0xAF9 = some (.vpxord 6 6 10, 0xAFF) := rfl
theorem at_AFF : prog 0xAFF = some (.vpxord 7 7 11, 0xB05) := rfl
theorem at_B05 : prog 0xB05 = some (.vprord 4 4 12, 0xB0C) := rfl
theorem at_B0C : prog 0xB0C = some (.vprord 5 5 12, 0xB13) := rfl
theorem at_B13 : prog 0xB13 = some (.vprord 6 6 12, 0xB1A) := rfl
theorem at_B1A : prog 0xB1A = some (.vprord 7 7 12, 0xB21) := rfl
theorem at_B21 : prog 0xB21 = some (.vpaddd 0 0 20, 0xB27) := rfl
theorem at_B27 : prog 0xB27 = some (.vpaddd 1 1 28, 0xB2D) := rfl
theorem at_B2D : prog 0xB2D = some (.vpaddd 2 2 18, 0xB33) := rfl
theorem at_B33 : prog 0xB33 = some (.vpaddd 3 3 30, 0xB39) := rfl
theorem at_B39 : prog 0xB39 = some (.vpaddd 0 0 4, 0xB3F) := rfl
theorem at_B3F : prog 0xB3F = some (.vpaddd 1 1 5, 0xB45) := rfl
theorem at_B45 : prog 0xB45 = some (.vpaddd 2 2 6, 0xB4B) := rfl
theorem at_B4B : prog 0xB4B = some (.vpaddd 3 3 7, 0xB51) := rfl
theorem at_B51 : prog 0xB51 = some (.vpxord 12 12 0, 0xB57) := rfl
theorem at_B57 : prog 0xB57 = some (.vpxord 13 13 1, 0xB5D) := rfl
theorem at_B5D : prog 0xB5D = some (.vpxord 14 14 2, 0xB63) := rfl
theorem at_B63 : prog 0xB63 = some (.vpxord 15 15 3, 0xB69) := rfl
theorem at_B69 : prog 0xB69 = some (.vprord 12 12 8, 0xB70) := rfl
theorem at_B70 : prog 0xB70 = some (.vprord 13 13 8, 0xB77) := rfl
theorem at_B77 : prog 0xB77 = some (.vprord 14 14 8, 0xB7E) := rfl
theorem at_B7E : prog 0xB7E = some (.vprord 15 15 8, 0xB85) := rfl
theorem at_B85 : prog 0xB85 = some (.vpaddd 8 8 12, 0xB8B) := rfl
theorem at_B8B : prog 0xB8B = some (.vpaddd 9 9 13, 0xB91) := rfl
theorem at_B91 : prog 0xB91 = some (.vpaddd 10 10 14, 0xB97) := rfl
theorem at_B97 : prog 0xB97 = some (.vpaddd 11 11 15, 0xB9D) := rfl
theorem at_B9D : prog 0xB9D = some (.vpxord 4 4 8, 0xBA3) := rfl
theorem at_BA3 : prog 0xBA3 = some (.vpxord 5 5 9, 0xBA9) := rfl
theorem at_BA9 : prog 0xBA9 = some (.vpxord 6 6 10, 0xBAF) := rfl
theorem at_BAF : prog 0xBAF = some (.vpxord 7 7 11, 0xBB5) := rfl
theorem at_BB5 : prog 0xBB5 = some (.vprord 4 4 7, 0xBBC) := rfl
theorem at_BBC : prog 0xBBC = some (.vprord 5 5 7, 0xBC3) := rfl
theorem at_BC3 : prog 0xBC3 = some (.vprord 6 6 7, 0xBCA) := rfl
theorem at_BCA : prog 0xBCA = some (.vprord 7 7 7, 0xBD1) := rfl
theorem at_BD1 : prog 0xBD1 = some (.vpaddd 0 0 22, 0xBD7) := rfl
theorem at_BD7 : prog 0xBD7 = some (.vpaddd 1 1 25, 0xBDD) := rfl
theorem at_BDD : prog 0xBDD = some (.vpaddd 2 2 27, 0xBE3) := rfl
theorem at_BE3 : prog 0xBE3 = some (.vpaddd 3 3 24, 0xBE9) := rfl
theorem at_BE9 : prog 0xBE9 = some (.vpaddd 0 0 5, 0xBEF) := rfl
theorem at_BEF : prog 0xBEF = some (.vpaddd 1 1 6, 0xBF5) := rfl
theorem at_BF5 : prog 0xBF5 = some (.vpaddd 2 2 7, 0xBFB) := rfl
theorem at_BFB : prog 0xBFB = some (.vpaddd 3 3 4, 0xC01) := rfl
theorem at_C01 : prog 0xC01 = some (.vpxord 15 15 0, 0xC07) := rfl
theorem at_C07 : prog 0xC07 = some (.vpxord 12 12 1, 0xC0D) := rfl
theorem at_C0D : prog 0xC0D = some (.vpxord 13 13 2, 0xC13) := rfl
theorem at_C13 : prog 0xC13 = some (.vpxord 14 14 3, 0xC19) := rfl
theorem at_C19 : prog 0xC19 = some (.vprord 15 15 16, 0xC20) := rfl
theorem at_C20 : prog 0xC20 = some (.vprord 12 12 16, 0xC27) := rfl
theorem at_C27 : prog 0xC27 = some (.vprord 13 13 16, 0xC2E) := rfl
theorem at_C2E : prog 0xC2E = some (.vprord 14 14 16, 0xC35) := rfl
theorem at_C35 : prog 0xC35 = some (.vpaddd 10 10 15, 0xC3B) := rfl
theorem at_C3B : prog 0xC3B = some (.vpaddd 11 11 12, 0xC41) := rfl
theorem at_C41 : prog 0xC41 = some (.vpaddd 8 8 13, 0xC47) := rfl
theorem at_C47 : prog 0xC47 = some (.vpaddd 9 9 14, 0xC4D) := rfl
theorem at_C4D : prog 0xC4D = some (.vpxord 5 5 10, 0xC53) := rfl
theorem at_C53 : prog 0xC53 = some (.vpxord 6 6 11, 0xC59) := rfl
theorem at_C59 : prog 0xC59 = some (.vpxord 7 7 8, 0xC5F) := rfl
theorem at_C5F : prog 0xC5F = some (.vpxord 4 4 9, 0xC65) := rfl
theorem at_C65 : prog 0xC65 = some (.vprord 5 5 12, 0xC6C) := rfl
theorem at_C6C : prog 0xC6C = some (.vprord 6 6 12, 0xC73) := rfl
theorem at_C73 : prog 0xC73 = some (.vprord 7 7 12, 0xC7A) := rfl
theorem at_C7A : prog 0xC7A = some (.vprord 4 4 12, 0xC81) := rfl
theorem at_C81 : prog 0xC81 = some (.vpaddd 0 0 21, 0xC87) := rfl
theorem at_C87 : prog 0xC87 = some (.vpaddd 1 1 16, 0xC8D) := rfl
theorem at_C8D : prog 0xC8D = some (.vpaddd 2 2 31, 0xC93) := rfl
theorem at_C93 : prog 0xC93 = some (.vpaddd 3 3 17, 0xC99) := rfl
theorem at_C99 : prog 0xC99 = some (.vpaddd 0 0 5, 0xC9F) := rfl
theorem at_C9F : prog 0xC9F = some (.vpaddd 1 1 6, 0xCA5) := rfl
theorem at_CA5 : prog 0xCA5 = some (.vpaddd 2 2 7, 0xCAB) := rfl
theorem at_CAB : prog 0xCAB = some (.vpaddd 3 3 4, 0xCB1) := rfl
theorem at_CB1 : prog 0xCB1 = some (.vpxord 15 15 0, 0xCB7) := rfl
theorem at_CB7 : prog 0xCB7 = some (.vpxord 12 12 1, 0xCBD) := rfl
theorem at_CBD : prog 0xCBD = some (.vpxord 13 13 2, 0xCC3) := rfl
theorem at_CC3 : prog 0xCC3 = some (.vpxord 14 14 3, 0xCC9) := rfl
theorem at_CC9 : prog 0xCC9 = some (.vprord 15 15 8, 0xCD0) := rfl
theorem at_CD0 : prog 0xCD0 = some (.vprord 12 12 8, 0xCD7) := rfl
theorem at_CD7 : prog 0xCD7 = some (.vprord 13 13 8, 0xCDE) := rfl
theorem at_CDE : prog 0xCDE = some (.vprord 14 14 8, 0xCE5) := rfl
theorem at_CE5 : prog 0xCE5 = some (.vpaddd 10 10 15, 0xCEB) := rfl
theorem at_CEB : prog 0xCEB = some (.vpaddd 11 11 12, 0xCF1) := rfl
theorem at_CF1 : prog 0xCF1 = some (.vpaddd 8 8 13, 0xCF7) := rfl
theorem at_CF7 : prog 0xCF7 = some (.vpaddd 9 9 14, 0xCFD) := rfl
theorem at_CFD : prog 0xCFD = some (.vpxord 5 5 10, 0xD03) := rfl
theorem at_D03 : prog 0xD03 = some (.vpxord 6 6 11, 0xD09) := rfl
theorem at_D09 : prog 0xD09 = some (.vpxord 7 7 8, 0xD0F) := rfl
theorem at_D0F : prog 0xD0F = some (.vpxord 4 4 9, 0xD15) := rfl
theorem at_D15 : prog 0xD15 = some (.vprord 5 5 7, 0xD1C) := rfl
theorem at_D1C : prog 0xD1C = some (.vprord 6 6 7, 0xD23) := rfl
theorem at_D23 : prog 0xD23 = some (.vprord 7 7 7, 0xD2A) := rfl
theorem at_D2A : prog 0xD2A = some (.vprord 4 4 7, 0xD31) := rfl
theorem at_D31 : prog 0xD31 = some (.vpaddd 0 0 26, 0xD37) := rfl
theorem at_D37 : prog 0xD37 = some (.vpaddd 1 1 28, 0xD3D) := rfl
theorem at_D3D : prog 0xD3D = some (.vpaddd 2 2 30, 0xD43) := rfl
theorem at_D43 : prog 0xD43 = some (.vpaddd 3 3 29, 0xD49) := rfl
theorem at_D49 : prog 0xD49 = some (.vpaddd 0 0 4, 0xD4F) := rfl
theorem at_D4F : prog 0xD4F = some (.vpaddd 1 1 5, 0xD55) := rfl
theorem at_D55 : prog 0xD55 = some (.vpaddd 2 2 6, 0xD5B) := rfl
theorem at_D5B : prog 0xD5B = some (.vpaddd 3 3 7, 0xD61) := rfl
theorem at_D61 : prog 0xD61 = some (.vpxord 12 12 0, 0xD67) := rfl
theorem at_D67 : prog 0xD67 = some (.vpxord 13 13 1, 0xD6D) := rfl
theorem at_D6D : prog 0xD6D = some (.vpxord 14 14 2, 0xD73) := rfl
theorem at_D73 : prog 0xD73 = some (.vpxord 15 15 3, 0xD79) := rfl
theorem at_D79 : prog 0xD79 = some (.vprord 12 12 16, 0xD80) := rfl
theorem at_D80 : prog 0xD80 = some (.vprord 13 13 16, 0xD87) := rfl
theorem at_D87 : prog 0xD87 = some (.vprord 14 14 16, 0xD8E) := rfl
theorem at_D8E : prog 0xD8E = some (.vprord 15 15 16, 0xD95) := rfl
theorem at_D95 : prog 0xD95 = some (.vpaddd 8 8 12, 0xD9B) := rfl
theorem at_D9B : prog 0xD9B = some (.vpaddd 9 9 13, 0xDA1) := rfl
theorem at_DA1 : prog 0xDA1 = some (.vpaddd 10 10 14, 0xDA7) := rfl
theorem at_DA7 : prog 0xDA7 = some (.vpaddd 11 11 15, 0xDAD) := rfl
theorem at_DAD : prog 0xDAD = some (.vpxord 4 4 8, 0xDB3) := rfl
theorem at_DB3 : prog 0xDB3 = some (.vpxord 5 5 9, 0xDB9) := rfl
theorem at_DB9 : prog 0xDB9 = some (.vpxord 6 6 10, 0xDBF) := rfl
theorem at_DBF : prog 0xDBF = some (.vpxord 7 7 11, 0xDC5) := rfl
theorem at_DC5 : prog 0xDC5 = some (.vprord 4 4 12, 0xDCC) := rfl
theorem at_DCC : prog 0xDCC = some (.vprord 5 5 12, 0xDD3) := rfl
theorem at_DD3 : prog 0xDD3 = some (.vprord 6 6 12, 0xDDA) := rfl
theorem at_DDA : prog 0xDDA = some (.vprord 7 7 12, 0xDE1) := rfl
theorem at_DE1 : prog 0xDE1 = some (.vpaddd 0 0 23, 0xDE7) := rfl
theorem at_DE7 : prog 0xDE7 = some (.vpaddd 1 1 25, 0xDED) := rfl
theorem at_DED : prog 0xDED = some (.vpaddd 2 2 19, 0xDF3) := rfl
theorem at_DF3 : prog 0xDF3 = some (.vpaddd 3 3 31, 0xDF9) := rfl
theorem at_DF9 : prog 0xDF9 = some (.vpaddd 0 0 4, 0xDFF) := rfl
theorem at_DFF : prog 0xDFF = some (.vpaddd 1 1 5, 0xE05) := rfl
theorem at_E05 : prog 0xE05 = some (.vpaddd 2 2 6, 0xE0B) := rfl
theorem at_E0B : prog 0xE0B = some (.vpaddd 3 3 7, 0xE11) := rfl
theorem at_E11 : prog 0xE11 = some (.vpxord 12 12 0, 0xE17) := rfl
theorem at_E17 : prog 0xE17 = some (.vpxord 13 13 1, 0xE1D) := rfl
theorem at_E1D : prog 0xE1D = some (.vpxord 14 14 2, 0xE23) := rfl
theorem at_E23 : prog 0xE23 = some (.vpxord 15 15 3, 0xE29) := rfl
theorem at_E29 : prog 0xE29 = some (.vprord 12 12 8, 0xE30) := rfl
theorem at_E30 : prog 0xE30 = some (.vprord 13 13 8, 0xE37) := rfl
theorem at_E37 : prog 0xE37 = some (.vprord 14 14 8, 0xE3E) := rfl
theorem at_E3E : prog 0xE3E = some (.vprord 15 15 8, 0xE45) := rfl
theorem at_E45 : prog 0xE45 = some (.vpaddd 8 8 12, 0xE4B) := rfl
theorem at_E4B : prog 0xE4B = some (.vpaddd 9 9 13, 0xE51) := rfl
theorem at_E51 : prog 0xE51 = some (.vpaddd 10 10 14, 0xE57) := rfl
theorem at_E57 : prog 0xE57 = some (.vpaddd 11 11 15, 0xE5D) := rfl
theorem at_E5D : prog 0xE5D = some (.vpxord 4 4 8, 0xE63) := rfl
theorem at_E63 : prog 0xE63 = some (.vpxord 5 5 9, 0xE69) := rfl
theorem at_E69 : prog 0xE69 = some (.vpxord 6 6 10, 0xE6F) := rfl
theorem at_E6F : prog 0xE6F = some (.vpxord 7 7 11, 0xE75) := rfl
theorem at_E75 : prog 0xE75 = some (.vprord 4 4 7, 0xE7C) := rfl
theorem at_E7C : prog 0xE7C = some (.vprord 5 5 7, 0xE83) := rfl
theorem at_E83 : prog 0xE83 = some (.vprord 6 6 7, 0xE8A) := rfl
theorem at_E8A : prog 0xE8A = some (.vprord 7 7 7, 0xE91) := rfl
theorem at_E91 : prog 0xE91 = some (.vpaddd 0 0 20, 0xE97) := rfl
theorem at_E97 : prog 0xE97 = some (.vpaddd 1 1 27, 0xE9D) := rfl
theorem at_E9D : prog 0xE9D = some (.vpaddd 2 2 21, 0xEA3) := rfl
theorem at_EA3 : prog 0xEA3 = some (.vpaddd 3 3 17, 0xEA9) := rfl
theorem at_EA9 : prog 0xEA9 = some (.vpaddd 0 0 5, 0xEAF) := rfl
theorem at_EAF : prog 0xEAF = some (.vpaddd 1 1 6, 0xEB5) := rfl
theorem at_EB5 : prog 0xEB5 = some (.vpaddd 2 2 7, 0xEBB) := rfl
theorem at_EBB : prog 0xEBB = some (.vpaddd 3 3 4, 0xEC1) := rfl
theorem at_EC1 : prog 0xEC1 = some (.vpxord 15 15 0, 0xEC7) := rfl
theorem at_EC7 : prog 0xEC7 = some (.vpxord 12 12 1, 0xECD) := rfl
theorem at_ECD : prog 0xECD = some (.vpxord 13 13 2, 0xED3) := rfl
theorem at_ED3 : prog 0xED3 = some (.vpxord 14 14 3, 0xED9) := rfl
theorem at_ED9 : prog 0xED9 = some (.vprord 15 15 16, 0xEE0) := rfl
theorem at_EE0 : prog 0xEE0 = some (.vprord 12 12 16, 0xEE7) := rfl
theorem at_EE7 : prog 0xEE7 = some (.vprord 13 13 16, 0xEEE) := rfl
theorem at_EEE : prog 0xEEE = some (.vprord 14 14 16, 0xEF5) := rfl
theorem at_EF5 : prog 0xEF5 = some (.vpaddd 10 10 15, 0xEFB) := rfl
theorem at_EFB : prog 0xEFB = some (.vpaddd 11 11 12, 0xF01) := rfl
theorem at_F01 : prog 0xF01 = some (.vpaddd 8 8 13, 0xF07) := rfl
theorem at_F07 : prog 0xF07 = some (.vpaddd 9 9 14, 0xF0D) := rfl
theorem at_F0D : prog 0xF0D = some (.vpxord 5 5 10, 0xF13) := rfl
theorem at_F13 : prog 0xF13 = some (.vpxord 6 6 11, 0xF19) := rfl
theorem at_F19 : prog 0xF19 = some (.vpxord 7 7 8, 0xF1F) := rfl
theorem at_F1F : prog 0xF1F = some (.vpxord 4 4 9, 0xF25) := rfl
theorem at_F25 : prog 0xF25 = some (.vprord 5 5 12, 0xF2C) := rfl
theorem at_F2C : prog 0xF2C = some (.vprord 6 6 12, 0xF33) := rfl
theorem at_F33 : prog 0xF33 = some (.vprord 7 7 12, 0xF3A) := rfl
theorem at_F3A : prog 0xF3A = some (.vprord 4 4 12, 0xF41) := rfl
theorem at_F41 : prog 0xF41 = some (.vpaddd 0 0 16, 0xF47) := rfl
theorem at_F47 : prog 0xF47 = some (.vpaddd 1 1 18, 0xF4D) := rfl
theorem at_F4D : prog 0xF4D = some (.vpaddd 2 2 24, 0xF53) := rfl
theorem at_F53 : prog 0xF53 = some (.vpaddd 3 3 22, 0xF59) := rfl
theorem at_F59 : prog 0xF59 = some (.vpaddd 0 0 5, 0xF5F) := rfl
theorem at_F5F : prog 0xF5F = some (.vpaddd 1 1 6, 0xF65) := rfl
theorem at_F65 : prog 0xF65 = some (.vpaddd 2 2 7, 0xF6B) := rfl
theorem at_F6B : prog 0xF6B = some (.vpaddd 3 3 4, 0xF71) := rfl
theorem at_F71 : prog 0xF71 = some (.vpxord 15 15 0, 0xF77) := rfl
theorem at_F77 : prog 0xF77 = some (.vpxord 12 12 1, 0xF7D) := rfl
theorem at_F7D : prog 0xF7D = some (.vpxord 13 13 2, 0xF83) := rfl
theorem at_F83 : prog 0xF83 = some (.vpxord 14 14 3, 0xF89) := rfl
theorem at_F89 : prog 0xF89 = some (.vprord 15 15 8, 0xF90) := rfl
theorem at_F90 : prog 0xF90 = some (.vprord 12 12 8, 0xF97) := rfl
theorem at_F97 : prog 0xF97 = some (.vprord 13 13 8, 0xF9E) := rfl
theorem at_F9E : prog 0xF9E = some (.vprord 14 14 8, 0xFA5) := rfl
theorem at_FA5 : prog 0xFA5 = some (.vpaddd 10 10 15, 0xFAB) := rfl
theorem at_FAB : prog 0xFAB = some (.vpaddd 11 11 12, 0xFB1) := rfl
theorem at_FB1 : prog 0xFB1 = some (.vpaddd 8 8 13, 0xFB7) := rfl
theorem at_FB7 : prog 0xFB7 = some (.vpaddd 9 9 14, 0xFBD) := rfl
theorem at_FBD : prog 0xFBD = some (.vpxord 5 5 10, 0xFC3) := rfl
theorem at_FC3 : prog 0xFC3 = some (.vpxord 6 6 11, 0xFC9) := rfl
theorem at_FC9 : prog 0xFC9 = some (.vpxord 7 7 8, 0xFCF) := rfl
theorem at_FCF : prog 0xFCF = some (.vpxord 4 4 9, 0xFD5) := rfl
theorem at_FD5 : prog 0xFD5 = some (.vprord 5 5 7, 0xFDC) := rfl
theorem at_FDC : prog 0xFDC = some (.vprord 6 6 7, 0xFE3) := rfl
theorem at_FE3 : prog 0xFE3 = some (.vprord 7 7 7, 0xFEA) := rfl
theorem at_FEA : prog 0xFEA = some (.vprord 4 4 7, 0xFF1) := rfl
theorem at_FF1 : prog 0xFF1 = some (.vpaddd 0 0 28, 0xFF7) := rfl
theorem at_FF7 : prog 0xFF7 = some (.vpaddd 1 1 25, 0xFFD) := rfl
theorem at_FFD : prog 0xFFD = some (.vpaddd 2 2 31, 0x1003) := rfl
theorem at_1003 : prog 0x1003 = some (.vpaddd 3 3 30, 0x1009) := rfl
theorem at_1009 : prog 0x1009 = some (.vpaddd 0 0 4, 0x100F) := rfl
theorem at_100F : prog 0x100F = some (.vpaddd 1 1 5, 0x1015) := rfl
theorem at_1015 : prog 0x1015 = some (.vpaddd 2 2 6, 0x101B) := rfl
theorem at_101B : prog 0x101B = some (.vpaddd 3 3 7, 0x1021) := rfl
theorem at_1021 : prog 0x1021 = some (.vpxord 12 12 0, 0x1027) := rfl
theorem at_1027 : prog 0x1027 = some (.vpxord 13 13 1, 0x102D) := rfl
theorem at_102D : prog 0x102D = some (.vpxord 14 14 2, 0x1033) := rfl
theorem at_1033 : prog 0x1033 = some (.vpxord 15 15 3, 0x1039) := rfl
theorem at_1039 : prog 0x1039 = some (.vprord 12 12 16, 0x1040) := rfl
theorem at_1040 : prog 0x1040 = some (.vprord 13 13 16, 0x1047) := rfl
theorem at_1047 : prog 0x1047 = some (.vprord 14 14 16, 0x104E) := rfl
theorem at_104E : prog 0x104E = some (.vprord 15 15 16, 0x1055) := rfl
theorem at_1055 : prog 0x1055 = some (.vpaddd 8 8 12, 0x105B) := rfl
theorem at_105B : prog 0x105B = some (.vpaddd 9 9 13, 0x1061) := rfl
theorem at_1061 : prog 0x1061 = some (.vpaddd 10 10 14, 0x1067) := rfl
theorem at_1067 : prog 0x1067 = some (.vpaddd 11 11 15, 0x106D) := rfl
theorem at_106D : prog 0x106D = some (.vpxord 4 4 8, 0x1073) := rfl
theorem at_1073 : prog 0x1073 = some (.vpxord 5 5 9, 0x1079) := rfl
theorem at_1079 : prog 0x1079 = some (.vpxord 6 6 10, 0x107F) := rfl
theorem at_107F : prog 0x107F = some (.vpxord 7 7 11, 0x1085) := rfl
theorem at_1085 : prog 0x1085 = some (.vprord 4 4 12, 0x108C) := rfl
theorem at_108C : prog 0x108C = some (.vprord 5 5 12, 0x1093) := rfl
theorem at_1093 : prog 0x1093 = some (.vprord 6 6 12, 0x109A) := rfl
theorem at_109A : prog 0x109A = some (.vprord 7 7 12, 0x10A1) := rfl
theorem at_10A1 : prog 0x10A1 = some (.vpaddd 0 0 29, 0x10A7) := rfl
theorem at_10A7 : prog 0x10A7 = some (.vpaddd 1 1 27, 0x10AD) := rfl
theorem at_10AD : prog 0x10AD = some (.vpaddd 2 2 26, 0x10B3) := rfl
theorem at_10B3 : prog 0x10B3 = some (.vpaddd 3 3 24, 0x10B9) := rfl
theorem at_10B9 : prog 0x10B9 = some (.vpaddd 0 0 4, 0x10BF) := rfl
theorem at_10BF : prog 0x10BF = some (.vpaddd 1 1 5, 0x10C5) := rfl
theorem at_10C5 : prog 0x10C5 = some (.vpaddd 2 2 6, 0x10CB) := rfl
theorem at_10CB : prog 0x10CB = some (.vpaddd 3 3 7, 0x10D1) := rfl
theorem at_10D1 : prog 0x10D1 = some (.vpxord 12 12 0, 0x10D7) := rfl
theorem at_10D7 : prog 0x10D7 = some (.vpxord 13 13 1, 0x10DD) := rfl
theorem at_10DD : prog 0x10DD = some (.vpxord 14 14 2, 0x10E3) := rfl
theorem at_10E3 : prog 0x10E3 = some (.vpxord 15 15 3, 0x10E9) := rfl
theorem at_10E9 : prog 0x10E9 = some (.vprord 12 12 8, 0x10F0) := rfl
theorem at_10F0 : prog 0x10F0 = some (.vprord 13 13 8, 0x10F7) := rfl
theorem at_10F7 : prog 0x10F7 = some (.vprord 14 14 8, 0x10FE) := rfl
theorem at_10FE : prog 0x10FE = some (.vprord 15 15 8, 0x1105) := rfl
theorem at_1105 : prog 0x1105 = some (.vpaddd 8 8 12, 0x110B) := rfl
theorem at_110B : prog 0x110B = some (.vpaddd 9 9 13, 0x1111) := rfl
theorem at_1111 : prog 0x1111 = some (.vpaddd 10 10 14, 0x1117) := rfl
theorem at_1117 : prog 0x1117 = some (.vpaddd 11 11 15, 0x111D) := rfl
theorem at_111D : prog 0x111D = some (.vpxord 4 4 8, 0x1123) := rfl
theorem at_1123 : prog 0x1123 = some (.vpxord 5 5 9, 0x1129) := rfl
theorem at_1129 : prog 0x1129 = some (.vpxord 6 6 10, 0x112F) := rfl
theorem at_112F : prog 0x112F = some (.vpxord 7 7 11, 0x1135) := rfl
theorem at_1135 : prog 0x1135 = some (.vprord 4 4 7, 0x113C) := rfl
theorem at_113C : prog 0x113C = some (.vprord 5 5 7, 0x1143) := rfl
theorem at_1143 : prog 0x1143 = some (.vprord 6 6 7, 0x114A) := rfl
theorem at_114A : prog 0x114A = some (.vprord 7 7 7, 0x1151) := rfl
theorem at_1151 : prog 0x1151 = some (.vpaddd 0 0 23, 0x1157) := rfl
theorem at_1157 : prog 0x1157 = some (.vpaddd 1 1 21, 0x115D) := rfl
theorem at_115D : prog 0x115D = some (.vpaddd 2 2 16, 0x1163) := rfl
theorem at_1163 : prog 0x1163 = some (.vpaddd 3 3 22, 0x1169) := rfl
theorem at_1169 : prog 0x1169 = some (.vpaddd 0 0 5, 0x116F) := rfl
theorem at_116F : prog 0x116F = some (.vpaddd 1 1 6, 0x1175) := rfl
theorem at_1175 : prog 0x1175 = some (.vpaddd 2 2 7, 0x117B) := rfl
theorem at_117B : prog 0x117B = some (.vpaddd 3 3 4, 0x1181) := rfl
theorem at_1181 : prog 0x1181 = some (.vpxord 15 15 0, 0x1187) := rfl
theorem at_1187 : prog 0x1187 = some (.vpxord 12 12 1, 0x118D) := rfl
theorem at_118D : prog 0x118D = some (.vpxord 13 13 2, 0x1193) := rfl
theorem at_1193 : prog 0x1193 = some (.vpxord 14 14 3, 0x1199) := rfl
theorem at_1199 : prog 0x1199 = some (.vprord 15 15 16, 0x11A0) := rfl
theorem at_11A0 : prog 0x11A0 = some (.vprord 12 12 16, 0x11A7) := rfl
theorem at_11A7 : prog 0x11A7 = some (.vprord 13 13 16, 0x11AE) := rfl
theorem at_11AE : prog 0x11AE = some (.vprord 14 14 16, 0x11B5) := rfl
theorem at_11B5 : prog 0x11B5 = some (.vpaddd 10 10 15, 0x11BB) := rfl
theorem at_11BB : prog 0x11BB = some (.vpaddd 11 11 12, 0x11C1) := rfl
theorem at_11C1 : prog 0x11C1 = some (.vpaddd 8 8 13, 0x11C7) := rfl
theorem at_11C7 : prog 0x11C7 = some (.vpaddd 9 9 14, 0x11CD) := rfl
theorem at_11CD : prog 0x11CD = some (.vpxord 5 5 10, 0x11D3) := rfl
theorem at_11D3 : prog 0x11D3 = some (.vpxord 6 6 11, 0x11D9) := rfl
theorem at_11D9 : prog 0x11D9 = some (.vpxord 7 7 8, 0x11DF) := rfl
theorem at_11DF : prog 0x11DF = some (.vpxord 4 4 9, 0x11E5) := rfl
theorem at_11E5 : prog 0x11E5 = some (.vprord 5 5 12, 0x11EC) := rfl
theorem at_11EC : prog 0x11EC = some (.vprord 6 6 12, 0x11F3) := rfl
theorem at_11F3 : prog 0x11F3 = some (.vprord 7 7 12, 0x11FA) := rfl
theorem at_11FA : prog 0x11FA = some (.vprord 4 4 12, 0x1201) := rfl
theorem at_1201 : prog 0x1201 = some (.vpaddd 0 0 18, 0x1207) := rfl
theorem at_1207 : prog 0x1207 = some (.vpaddd 1 1 19, 0x120D) := rfl
theorem at_120D : prog 0x120D = some (.vpaddd 2 2 17, 0x1213) := rfl
theorem at_1213 : prog 0x1213 = some (.vpaddd 3 3 20, 0x1219) := rfl
theorem at_1219 : prog 0x1219 = some (.vpaddd 0 0 5, 0x121F) := rfl
theorem at_121F : prog 0x121F = some (.vpaddd 1 1 6, 0x1225) := rfl
theorem at_1225 : prog 0x1225 = some (.vpaddd 2 2 7, 0x122B) := rfl
theorem at_122B : prog 0x122B = some (.vpaddd 3 3 4, 0x1231) := rfl
theorem at_1231 : prog 0x1231 = some (.vpxord 15 15 0, 0x1237) := rfl
theorem at_1237 : prog 0x1237 = some (.vpxord 12 12 1, 0x123D) := rfl
theorem at_123D : prog 0x123D = some (.vpxord 13 13 2, 0x1243) := rfl
theorem at_1243 : prog 0x1243 = some (.vpxord 14 14 3, 0x1249) := rfl
theorem at_1249 : prog 0x1249 = some (.vprord 15 15 8, 0x1250) := rfl
theorem at_1250 : prog 0x1250 = some (.vprord 12 12 8, 0x1257) := rfl
theorem at_1257 : prog 0x1257 = some (.vprord 13 13 8, 0x125E) := rfl
theorem at_125E : prog 0x125E = some (.vprord 14 14 8, 0x1265) := rfl
theorem at_1265 : prog 0x1265 = some (.vpaddd 10 10 15, 0x126B) := rfl
theorem at_126B : prog 0x126B = some (.vpaddd 11 11 12, 0x1271) := rfl
theorem at_1271 : prog 0x1271 = some (.vpaddd 8 8 13, 0x1277) := rfl
theorem at_1277 : prog 0x1277 = some (.vpaddd 9 9 14, 0x127D) := rfl
theorem at_127D : prog 0x127D = some (.vpxord 5 5 10, 0x1283) := rfl
theorem at_1283 : prog 0x1283 = some (.vpxord 6 6 11, 0x1289) := rfl
theorem at_1289 : prog 0x1289 = some (.vpxord 7 7 8, 0x128F) := rfl
theorem at_128F : prog 0x128F = some (.vpxord 4 4 9, 0x1295) := rfl
theorem at_1295 : prog 0x1295 = some (.vprord 5 5 7, 0x129C) := rfl
theorem at_129C : prog 0x129C = some (.vprord 6 6 7, 0x12A3) := rfl
theorem at_12A3 : prog 0x12A3 = some (.vprord 7 7 7, 0x12AA) := rfl
theorem at_12AA : prog 0x12AA = some (.vprord 4 4 7, 0x12B1) := rfl
theorem at_12B1 : prog 0x12B1 = some (.vpaddd 0 0 25, 0x12B7) := rfl
theorem at_12B7 : prog 0x12B7 = some (.vpaddd 1 1 27, 0x12BD) := rfl
theorem at_12BD : prog 0x12BD = some (.vpaddd 2 2 24, 0x12C3) := rfl
theorem at_12C3 : prog 0x12C3 = some (.vpaddd 3 3 31, 0x12C9) := rfl
theorem at_12C9 : prog 0x12C9 = some (.vpaddd 0 0 4, 0x12CF) := rfl
theorem at_12CF : prog 0x12CF = some (.vpaddd 1 1 5, 0x12D5) := rfl
theorem at_12D5 : prog 0x12D5 = some (.vpaddd 2 2 6, 0x12DB) := rfl
theorem at_12DB : prog 0x12DB = some (.vpaddd 3 3 7, 0x12E1) := rfl
theorem at_12E1 : prog 0x12E1 = some (.vpxord 12 12 0, 0x12E7) := rfl
theorem at_12E7 : prog 0x12E7 = some (.vpxord 13 13 1, 0x12ED) := rfl
theorem at_12ED : prog 0x12ED = some (.vpxord 14 14 2, 0x12F3) := rfl
theorem at_12F3 : prog 0x12F3 = some (.vpxord 15 15 3, 0x12F9) := rfl
theorem at_12F9 : prog 0x12F9 = some (.vprord 12 12 16, 0x1300) := rfl
theorem at_1300 : prog 0x1300 = some (.vprord 13 13 16, 0x1307) := rfl
theorem at_1307 : prog 0x1307 = some (.vprord 14 14 16, 0x130E) := rfl
theorem at_130E : prog 0x130E = some (.vprord 15 15 16, 0x1315) := rfl
theorem at_1315 : prog 0x1315 = some (.vpaddd 8 8 12, 0x131B) := rfl
theorem at_131B : prog 0x131B = some (.vpaddd 9 9 13, 0x1321) := rfl
theorem at_1321 : prog 0x1321 = some (.vpaddd 10 10 14, 0x1327) := rfl
theorem at_1327 : prog 0x1327 = some (.vpaddd 11 11 15, 0x132D) := rfl
theorem at_132D : prog 0x132D = some (.vpxord 4 4 8, 0x1333) := rfl
theorem at_1333 : prog 0x1333 = some (.vpxord 5 5 9, 0x1339) := rfl
theorem at_1339 : prog 0x1339 = some (.vpxord 6 6 10, 0x133F) := rfl
theorem at_133F : prog 0x133F = some (.vpxord 7 7 11, 0x1345) := rfl
theorem at_1345 : prog 0x1345 = some (.vprord 4 4 12, 0x134C) := rfl
theorem at_134C : prog 0x134C = some (.vprord 5 5 12, 0x1353) := rfl
theorem at_1353 : prog 0x1353 = some (.vprord 6 6 12, 0x135A) := rfl
theorem at_135A : prog 0x135A = some (.vprord 7 7 12, 0x1361) := rfl
theorem at_1361 : prog 0x1361 = some (.vpaddd 0 0 30, 0x1367) := rfl
theorem at_1367 : prog 0x1367 = some (.vpaddd 1 1 21, 0x136D) := rfl
theorem at_136D : prog 0x136D = some (.vpaddd 2 2 28, 0x1373) := rfl
theorem at_1373 : prog 0x1373 = some (.vpaddd 3 3 17, 0x1379) := rfl
theorem at_1379 : prog 0x1379 = some (.vpaddd 0 0 4, 0x137F) := rfl
theorem at_137F : prog 0x137F = some (.vpaddd 1 1 5, 0x1385) := rfl
theorem at_1385 : prog 0x1385 = some (.vpaddd 2 2 6, 0x138B) := rfl
theorem at_138B : prog 0x138B = some (.vpaddd 3 3 7, 0x1391) := rfl
theorem at_1391 : prog 0x1391 = some (.vpxord 12 12 0, 0x1397) := rfl
theorem at_1397 : prog 0x1397 = some (.vpxord 13 13 1, 0x139D) := rfl
theorem at_139D : prog 0x139D = some (.vpxord 14 14 2, 0x13A3) := rfl
theorem at_13A3 : prog 0x13A3 = some (.vpxord 15 15 3, 0x13A9) := rfl
theorem at_13A9 : prog 0x13A9 = some (.vprord 12 12 8, 0x13B0) := rfl
theorem at_13B0 : prog 0x13B0 = some (.vprord 13 13 8, 0x13B7) := rfl
theorem at_13B7 : prog 0x13B7 = some (.vprord 14 14 8, 0x13BE) := rfl
theorem at_13BE : prog 0x13BE = some (.vprord 15 15 8, 0x13C5) := rfl
theorem at_13C5 : prog 0x13C5 = some (.vpaddd 8 8 12, 0x13CB) := rfl
theorem at_13CB : prog 0x13CB = some (.vpaddd 9 9 13, 0x13D1) := rfl
theorem at_13D1 : prog 0x13D1 = some (.vpaddd 10 10 14, 0x13D7) := rfl
theorem at_13D7 : prog 0x13D7 = some (.vpaddd 11 11 15, 0x13DD) := rfl
theorem at_13DD : prog 0x13DD = some (.vpxord 4 4 8, 0x13E3) := rfl
theorem at_13E3 : prog 0x13E3 = some (.vpxord 5 5 9, 0x13E9) := rfl
theorem at_13E9 : prog 0x13E9 = some (.vpxord 6 6 10, 0x13EF) := rfl
theorem at_13EF : prog 0x13EF = some (.vpxord 7 7 11, 0x13F5) := rfl
theorem at_13F5 : prog 0x13F5 = some (.vprord 4 4 7, 0x13FC) := rfl
theorem at_13FC : prog 0x13FC = some (.vprord 5 5 7, 0x1403) := rfl
theorem at_1403 : prog 0x1403 = some (.vprord 6 6 7, 0x140A) := rfl
theorem at_140A : prog 0x140A = some (.vprord 7 7 7, 0x1411) := rfl
theorem at_1411 : prog 0x1411 = some (.vpaddd 0 0 29, 0x1417) := rfl
theorem at_1417 : prog 0x1417 = some (.vpaddd 1 1 16, 0x141D) := rfl
theorem at_141D : prog 0x141D = some (.vpaddd 2 2 18, 0x1423) := rfl
theorem at_1423 : prog 0x1423 = some (.vpaddd 3 3 20, 0x1429) := rfl
theorem at_1429 : prog 0x1429 = some (.vpaddd 0 0 5, 0x142F) := rfl
theorem at_142F : prog 0x142F = some (.vpaddd 1 1 6, 0x1435) := rfl
theorem at_1435 : prog 0x1435 = some (.vpaddd 2 2 7, 0x143B) := rfl
theorem at_143B : prog 0x143B = some (.vpaddd 3 3 4, 0x1441) := rfl
theorem at_1441 : prog 0x1441 = some (.vpxord 15 15 0, 0x1447) := rfl
theorem at_1447 : prog 0x1447 = some (.vpxord 12 12 1, 0x144D) := rfl
theorem at_144D : prog 0x144D = some (.vpxord 13 13 2, 0x1453) := rfl
theorem at_1453 : prog 0x1453 = some (.vpxord 14 14 3, 0x1459) := rfl
theorem at_1459 : prog 0x1459 = some (.vprord 15 15 16, 0x1460) := rfl
theorem at_1460 : prog 0x1460 = some (.vprord 12 12 16, 0x1467) := rfl
theorem at_1467 : prog 0x1467 = some (.vprord 13 13 16, 0x146E) := rfl
theorem at_146E : prog 0x146E = some (.vprord 14 14 16, 0x1475) := rfl
theorem at_1475 : prog 0x1475 = some (.vpaddd 10 10 15, 0x147B) := rfl
theorem at_147B : prog 0x147B = some (.vpaddd 11 11 12, 0x1481) := rfl
theorem at_1481 : prog 0x1481 = some (.vpaddd 8 8 13, 0x1487) := rfl
theorem at_1487 : prog 0x1487 = some (.vpaddd 9 9 14, 0x148D) := rfl
theorem at_148D : prog 0x148D = some (.vpxord 5 5 10, 0x1493) := rfl
theorem at_1493 : prog 0x1493 = some (.vpxord 6 6 11, 0x1499) := rfl
theorem at_1499 : prog 0x1499 = some (.vpxord 7 7 8, 0x149F) := rfl
theorem at_149F : prog 0x149F = some (.vpxord 4 4 9, 0x14A5) := rfl
theorem at_14A5 : prog 0x14A5 = some (.vprord 5 5 12, 0x14AC) := rfl
theorem at_14AC : prog 0x14AC = some (.vprord 6 6 12, 0x14B3) := rfl
theorem at_14B3 : prog 0x14B3 = some (.vprord 7 7 12, 0x14BA) := rfl
theorem at_14BA : prog 0x14BA = some (.vprord 4 4 12, 0x14C1) := rfl
theorem at_14C1 : prog 0x14C1 = some (.vpaddd 0 0 19, 0x14C7) := rfl
theorem at_14C7 : prog 0x14C7 = some (.vpaddd 1 1 26, 0x14CD) := rfl
theorem at_14CD : prog 0x14CD = some (.vpaddd 2 2 22, 0x14D3) := rfl
theorem at_14D3 : prog 0x14D3 = some (.vpaddd 3 3 23, 0x14D9) := rfl
theorem at_14D9 : prog 0x14D9 = some (.vpaddd 0 0 5, 0x14DF) := rfl
theorem at_14DF : prog 0x14DF = some (.vpaddd 1 1 6, 0x14E5) := rfl
theorem at_14E5 : prog 0x14E5 = some (.vpaddd 2 2 7, 0x14EB) := rfl
theorem at_14EB : prog 0x14EB = some (.vpaddd 3 3 4, 0x14F1) := rfl
theorem at_14F1 : prog 0x14F1 = some (.vpxord 15 15 0, 0x14F7) := rfl
theorem at_14F7 : prog 0x14F7 = some (.vpxord 12 12 1, 0x14FD) := rfl
theorem at_14FD : prog 0x14FD = some (.vpxord 13 13 2, 0x1503) := rfl
theorem at_1503 : prog 0x1503 = some (.vpxord 14 14 3, 0x1509) := rfl
theorem at_1509 : prog 0x1509 = some (.vprord 15 15 8, 0x1510) := rfl
theorem at_1510 : prog 0x1510 = some (.vprord 12 12 8, 0x1517) := rfl
theorem at_1517 : prog 0x1517 = some (.vprord 13 13 8, 0x151E) := rfl
theorem at_151E : prog 0x151E = some (.vprord 14 14 8, 0x1525) := rfl
theorem at_1525 : prog 0x1525 = some (.vpaddd 10 10 15, 0x152B) := rfl
theorem at_152B : prog 0x152B = some (.vpaddd 11 11 12, 0x1531) := rfl
theorem at_1531 : prog 0x1531 = some (.vpaddd 8 8 13, 0x1537) := rfl
theorem at_1537 : prog 0x1537 = some (.vpaddd 9 9 14, 0x153D) := rfl
theorem at_153D : prog 0x153D = some (.vpxord 5 5 10, 0x1543) := rfl
theorem at_1543 : prog 0x1543 = some (.vpxord 6 6 11, 0x1549) := rfl
theorem at_1549 : prog 0x1549 = some (.vpxord 7 7 8, 0x154F) := rfl
theorem at_154F : prog 0x154F = some (.vpxord 4 4 9, 0x1555) := rfl
theorem at_1555 : prog 0x1555 = some (.vprord 5 5 7, 0x155C) := rfl
theorem at_155C : prog 0x155C = some (.vprord 6 6 7, 0x1563) := rfl
theorem at_1563 : prog 0x1563 = some (.vprord 7 7 7, 0x156A) := rfl
theorem at_156A : prog 0x156A = some (.vprord 4 4 7, 0x1571) := rfl
theorem at_1571 : prog 0x1571 = some (.vpaddd 0 0 27, 0x1577) := rfl
theorem at_1577 : prog 0x1577 = some (.vpaddd 1 1 21, 0x157D) := rfl
theorem at_157D : prog 0x157D = some (.vpaddd 2 2 17, 0x1583) := rfl
theorem at_1583 : prog 0x1583 = some (.vpaddd 3 3 24, 0x1589) := rfl
theorem at_1589 : prog 0x1589 = some (.vpaddd 0 0 4, 0x158F) := rfl
theorem at_158F : prog 0x158F = some (.vpaddd 1 1 5, 0x1595) := rfl
theorem at_1595 : prog 0x1595 = some (.vpaddd 2 2 6, 0x159B) := rfl
theorem at_159B : prog 0x159B = some (.vpaddd 3 3 7, 0x15A1) := rfl
theorem at_15A1 : prog 0x15A1 = some (.vpxord 12 12 0, 0x15A7) := rfl
theorem at_15A7 : prog 0x15A7 = some (.vpxord 13 13 1, 0x15AD) := rfl
theorem at_15AD : prog 0x15AD = some (.vpxord 14 14 2, 0x15B3) := rfl
theorem at_15B3 : prog 0x15B3 = some (.vpxord 15 15 3, 0x15B9) := rfl
theorem at_15B9 : prog 0x15B9 = some (.vprord 12 12 16, 0x15C0) := rfl
theorem at_15C0 : prog 0x15C0 = some (.vprord 13 13 16, 0x15C7) := rfl
theorem at_15C7 : prog 0x15C7 = some (.vprord 14 14 16, 0x15CE) := rfl
theorem at_15CE : prog 0x15CE = some (.vprord 15 15 16, 0x15D5) := rfl
theorem at_15D5 : prog 0x15D5 = some (.vpaddd 8 8 12, 0x15DB) := rfl
theorem at_15DB : prog 0x15DB = some (.vpaddd 9 9 13, 0x15E1) := rfl
theorem at_15E1 : prog 0x15E1 = some (.vpaddd 10 10 14, 0x15E7) := rfl
theorem at_15E7 : prog 0x15E7 = some (.vpaddd 11 11 15, 0x15ED) := rfl
theorem at_15ED : prog 0x15ED = some (.vpxord 4 4 8, 0x15F3) := rfl
theorem at_15F3 : prog 0x15F3 = some (.vpxord 5 5 9, 0x15F9) := rfl
theorem at_15F9 : prog 0x15F9 = some (.vpxord 6 6 10, 0x15FF) := rfl
theorem at_15FF : prog 0x15FF = some (.vpxord 7 7 11, 0x1605) := rfl
theorem at_1605 : prog 0x1605 = some (.vprord 4 4 12, 0x160C) := rfl
theorem at_160C : prog 0x160C = some (.vprord 5 5 12, 0x1613) := rfl
theorem at_1613 : prog 0x1613 = some (.vprord 6 6 12, 0x161A) := rfl
theorem at_161A : prog 0x161A = some (.vprord 7 7 12, 0x1621) := rfl
theorem at_1621 : prog 0x1621 = some (.vpaddd 0 0 31, 0x1627) := rfl
theorem at_1627 : prog 0x1627 = some (.vpaddd 1 1 16, 0x162D) := rfl
theorem at_162D : prog 0x162D = some (.vpaddd 2 2 25, 0x1633) := rfl
theorem at_1633 : prog 0x1633 = some (.vpaddd 3 3 22, 0x1639) := rfl
theorem at_1639 : prog 0x1639 = some (.vpaddd 0 0 4, 0x163F) := rfl
theorem at_163F : prog 0x163F = some (.vpaddd 1 1 5, 0x1645) := rfl
theorem at_1645 : prog 0x1645 = some (.vpaddd 2 2 6, 0x164B) := rfl
theorem at_164B : prog 0x164B = some (.vpaddd 3 3 7, 0x1651) := rfl
theorem at_1651 : prog 0x1651 = some (.vpxord 12 12 0, 0x1657) := rfl
theorem at_1657 : prog 0x1657 = some (.vpxord 13 13 1, 0x165D) := rfl
theorem at_165D : prog 0x165D = some (.vpxord 14 14 2, 0x1663) := rfl
theorem at_1663 : prog 0x1663 = some (.vpxord 15 15 3, 0x1669) := rfl
theorem at_1669 : prog 0x1669 = some (.vprord 12 12 8, 0x1670) := rfl
theorem at_1670 : prog 0x1670 = some (.vprord 13 13 8, 0x1677) := rfl
theorem at_1677 : prog 0x1677 = some (.vprord 14 14 8, 0x167E) := rfl
theorem at_167E : prog 0x167E = some (.vprord 15 15 8, 0x1685) := rfl
theorem at_1685 : prog 0x1685 = some (.vpaddd 8 8 12, 0x168B) := rfl
theorem at_168B : prog 0x168B = some (.vpaddd 9 9 13, 0x1691) := rfl
theorem at_1691 : prog 0x1691 = some (.vpaddd 10 10 14, 0x1697) := rfl
theorem at_1697 : prog 0x1697 = some (.vpaddd 11 11 15, 0x169D) := rfl
theorem at_169D : prog 0x169D = some (.vpxord 4 4 8, 0x16A3) := rfl
theorem at_16A3 : prog 0x16A3 = some (.vpxord 5 5 9, 0x16A9) := rfl
theorem at_16A9 : prog 0x16A9 = some (.vpxord 6 6 10, 0x16AF) := rfl
theorem at_16AF : prog 0x16AF = some (.vpxord 7 7 11, 0x16B5) := rfl
theorem at_16B5 : prog 0x16B5 = some (.vprord 4 4 7, 0x16BC) := rfl
theorem at_16BC : prog 0x16BC = some (.vprord 5 5 7, 0x16C3) := rfl
theorem at_16C3 : prog 0x16C3 = some (.vprord 6 6 7, 0x16CA) := rfl
theorem at_16CA : prog 0x16CA = some (.vprord 7 7 7, 0x16D1) := rfl
theorem at_16D1 : prog 0x16D1 = some (.vpaddd 0 0 30, 0x16D7) := rfl
theorem at_16D7 : prog 0x16D7 = some (.vpaddd 1 1 18, 0x16DD) := rfl
theorem at_16DD : prog 0x16DD = some (.vpaddd 2 2 19, 0x16E3) := rfl
theorem at_16E3 : prog 0x16E3 = some (.vpaddd 3 3 23, 0x16E9) := rfl
theorem at_16E9 : prog 0x16E9 = some (.vpaddd 0 0 5, 0x16EF) := rfl
theorem at_16EF : prog 0x16EF = some (.vpaddd 1 1 6, 0x16F5) := rfl
theorem at_16F5 : prog 0x16F5 = some (.vpaddd 2 2 7, 0x16FB) := rfl
theorem at_16FB : prog 0x16FB = some (.vpaddd 3 3 4, 0x1701) := rfl
theorem at_1701 : prog 0x1701 = some (.vpxord 15 15 0, 0x1707) := rfl
theorem at_1707 : prog 0x1707 = some (.vpxord 12 12 1, 0x170D) := rfl
theorem at_170D : prog 0x170D = some (.vpxord 13 13 2, 0x1713) := rfl
theorem at_1713 : prog 0x1713 = some (.vpxord 14 14 3, 0x1719) := rfl
theorem at_1719 : prog 0x1719 = some (.vprord 15 15 16, 0x1720) := rfl
theorem at_1720 : prog 0x1720 = some (.vprord 12 12 16, 0x1727) := rfl
theorem at_1727 : prog 0x1727 = some (.vprord 13 13 16, 0x172E) := rfl
theorem at_172E : prog 0x172E = some (.vprord 14 14 16, 0x1735) := rfl
theorem at_1735 : prog 0x1735 = some (.vpaddd 10 10 15, 0x173B) := rfl
theorem at_173B : prog 0x173B = some (.vpaddd 11 11 12, 0x1741) := rfl
theorem at_1741 : prog 0x1741 = some (.vpaddd 8 8 13, 0x1747) := rfl
theorem at_1747 : prog 0x1747 = some (.vpaddd 9 9 14, 0x174D) := rfl
theorem at_174D : prog 0x174D = some (.vpxord 5 5 10, 0x1753) := rfl
theorem at_1753 : prog 0x1753 = some (.vpxord 6 6 11, 0x1759) := rfl
theorem at_1759 : prog 0x1759 = some (.vpxord 7 7 8, 0x175F) := rfl
theorem at_175F : prog 0x175F = some (.vpxord 4 4 9, 0x1765) := rfl
theorem at_1765 : prog 0x1765 = some (.vprord 5 5 12, 0x176C) := rfl
theorem at_176C : prog 0x176C = some (.vprord 6 6 12, 0x1773) := rfl
theorem at_1773 : prog 0x1773 = some (.vprord 7 7 12, 0x177A) := rfl
theorem at_177A : prog 0x177A = some (.vprord 4 4 12, 0x1781) := rfl
theorem at_1781 : prog 0x1781 = some (.vpaddd 0 0 26, 0x1787) := rfl
theorem at_1787 : prog 0x1787 = some (.vpaddd 1 1 28, 0x178D) := rfl
theorem at_178D : prog 0x178D = some (.vpaddd 2 2 20, 0x1793) := rfl
theorem at_1793 : prog 0x1793 = some (.vpaddd 3 3 29, 0x1799) := rfl
theorem at_1799 : prog 0x1799 = some (.vpaddd 0 0 5, 0x179F) := rfl
theorem at_179F : prog 0x179F = some (.vpaddd 1 1 6, 0x17A5) := rfl
theorem at_17A5 : prog 0x17A5 = some (.vpaddd 2 2 7, 0x17AB) := rfl
theorem at_17AB : prog 0x17AB = some (.vpaddd 3 3 4, 0x17B1) := rfl
theorem at_17B1 : prog 0x17B1 = some (.vpxord 15 15 0, 0x17B7) := rfl
theorem at_17B7 : prog 0x17B7 = some (.vpxord 12 12 1, 0x17BD) := rfl
theorem at_17BD : prog 0x17BD = some (.vpxord 13 13 2, 0x17C3) := rfl
theorem at_17C3 : prog 0x17C3 = some (.vpxord 14 14 3, 0x17C9) := rfl
theorem at_17C9 : prog 0x17C9 = some (.vprord 15 15 8, 0x17D0) := rfl
theorem at_17D0 : prog 0x17D0 = some (.vprord 12 12 8, 0x17D7) := rfl
theorem at_17D7 : prog 0x17D7 = some (.vprord 13 13 8, 0x17DE) := rfl
theorem at_17DE : prog 0x17DE = some (.vprord 14 14 8, 0x17E5) := rfl
theorem at_17E5 : prog 0x17E5 = some (.vpaddd 10 10 15, 0x17EB) := rfl
theorem at_17EB : prog 0x17EB = some (.vpaddd 11 11 12, 0x17F1) := rfl
theorem at_17F1 : prog 0x17F1 = some (.vpaddd 8 8 13, 0x17F7) := rfl
theorem at_17F7 : prog 0x17F7 = some (.vpaddd 9 9 14, 0x17FD) := rfl
theorem at_17FD : prog 0x17FD = some (.vpxord 5 5 10, 0x1803) := rfl
theorem at_1803 : prog 0x1803 = some (.vpxord 6 6 11, 0x1809) := rfl
theorem at_1809 : prog 0x1809 = some (.vpxord 7 7 8, 0x180F) := rfl
theorem at_180F : prog 0x180F = some (.vpxord 4 4 9, 0x1815) := rfl
theorem at_1815 : prog 0x1815 = some (.vprord 5 5 7, 0x181C) := rfl
theorem at_181C : prog 0x181C = some (.vprord 6 6 7, 0x1823) := rfl
theorem at_1823 : prog 0x1823 = some (.vprord 7 7 7, 0x182A) := rfl
theorem at_182A : prog 0x182A = some (.vprord 4 4 7, 0x1831) := rfl

end Rounds
