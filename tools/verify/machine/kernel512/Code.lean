import Simd

/-! `blake3_servil_compress_in_place_avx512` of avx512.o, as llvm-objdump reads it. Written by lift_simd.py. -/

set_option maxRecDepth 100000
namespace Code
open Simd

def entry : Nat := 0x3700

def table : List (Nat × Instr × Nat) := [
  (0x3700, .movv 0 (.m .rdi 0x0), 0x3704),  -- c5 fa 6f 07              vmovdqu xmm0, xmmword ptr [rdi]
  (0x3704, .movv 1 (.m .rdi 0x10), 0x3709),  -- c5 fa 6f 4f 10           vmovdqu xmm1, xmmword ptr [rdi + 0x10]
  (0x3709, .movzx8 .rax .r8, 0x370D),  -- 41 0f b6 c0              movzx eax, r8b
  (0x370D, .movzx8 .rdx .rdx, 0x3710),  -- 0f b6 d2                 movzx edx, dl
  (0x3710, .shl64 .rax 32, 0x3714),  -- 48 c1 e0 20              shl rax, 0x20
  (0x3714, .add64 .rdx .rax, 0x3717),  -- 48 01 c2                 add rdx, rax
  (0x3717, .movq 3 .rcx, 0x371C),  -- c4 e1 f9 6e d9           vmovq xmm3, rcx
  (0x371C, .movq 4 .rdx, 0x3721),  -- c4 e1 f9 6e e2           vmovq xmm4, rdx
  (0x3721, .vpunpcklqdq 3 3 (.x 4), 0x3725),  -- c5 e1 6c dc              vpunpcklqdq xmm3, xmm3, xmm4
  (0x3725, .movv 2 (.c 0xA54FF53A3C6EF372BB67AE856A09E667#128), 0x372D),  -- c5 f8 28 15 00 00 00 00  vmovaps xmm2, xmmword ptr [rip]
  (0x372D, .movv 8 (.m .rsi 0x0), 0x3731),  -- c5 78 10 06              vmovups xmm8, xmmword ptr [rsi]
  (0x3731, .movv 9 (.m .rsi 0x10), 0x3736),  -- c5 78 10 4e 10           vmovups xmm9, xmmword ptr [rsi + 0x10]
  (0x3736, .vshufps 4 8 (.x 9) 136, 0x373C),  -- c4 c1 38 c6 e1 88        vshufps xmm4, xmm8, xmm9, 0x88
  (0x373C, .vshufps 5 8 (.x 9) 221, 0x3742),  -- c4 c1 38 c6 e9 dd        vshufps xmm5, xmm8, xmm9, 0xdd
  (0x3742, .movv 8 (.m .rsi 0x20), 0x3747),  -- c5 78 10 46 20           vmovups xmm8, xmmword ptr [rsi + 0x20]
  (0x3747, .movv 9 (.m .rsi 0x30), 0x374C),  -- c5 78 10 4e 30           vmovups xmm9, xmmword ptr [rsi + 0x30]
  (0x374C, .vshufps 6 8 (.x 9) 136, 0x3752),  -- c4 c1 38 c6 f1 88        vshufps xmm6, xmm8, xmm9, 0x88
  (0x3752, .vshufps 7 8 (.x 9) 221, 0x3758),  -- c4 c1 38 c6 f9 dd        vshufps xmm7, xmm8, xmm9, 0xdd
  (0x3758, .pshufd 6 (.x 6) 147, 0x375D),  -- c5 f9 70 f6 93           vpshufd xmm6, xmm6, 0x93
  (0x375D, .pshufd 7 (.x 7) 147, 0x3762),  -- c5 f9 70 ff 93           vpshufd xmm7, xmm7, 0x93
  (0x3762, .movb .rax 7, 0x3764),  -- b0 07                    mov al, 0x7
  (0x3764, .vpaddd 0 0 (.x 4), 0x3768),  -- c5 f9 fe c4              vpaddd xmm0, xmm0, xmm4
  (0x3768, .vpaddd 0 0 (.x 1), 0x376C),  -- c5 f9 fe c1              vpaddd xmm0, xmm0, xmm1
  (0x376C, .vpxor 3 3 (.x 0), 0x3772),  -- 62 f1 65 08 ef d8        vpxord xmm3, xmm3, xmm0
  (0x3772, .vprord 3 (.x 3) 16, 0x3779),  -- 62 f1 65 08 72 c3 10     vprord xmm3, xmm3, 0x10
  (0x3779, .vpaddd 2 2 (.x 3), 0x377D),  -- c5 e9 fe d3              vpaddd xmm2, xmm2, xmm3
  (0x377D, .vpxor 1 1 (.x 2), 0x3783),  -- 62 f1 75 08 ef ca        vpxord xmm1, xmm1, xmm2
  (0x3783, .vprord 1 (.x 1) 12, 0x378A),  -- 62 f1 75 08 72 c1 0c     vprord xmm1, xmm1, 0xc
  (0x378A, .vpaddd 0 0 (.x 5), 0x378E),  -- c5 f9 fe c5              vpaddd xmm0, xmm0, xmm5
  (0x378E, .vpaddd 0 0 (.x 1), 0x3792),  -- c5 f9 fe c1              vpaddd xmm0, xmm0, xmm1
  (0x3792, .vpxor 3 3 (.x 0), 0x3798),  -- 62 f1 65 08 ef d8        vpxord xmm3, xmm3, xmm0
  (0x3798, .vprord 3 (.x 3) 8, 0x379F),  -- 62 f1 65 08 72 c3 08     vprord xmm3, xmm3, 0x8
  (0x379F, .vpaddd 2 2 (.x 3), 0x37A3),  -- c5 e9 fe d3              vpaddd xmm2, xmm2, xmm3
  (0x37A3, .vpxor 1 1 (.x 2), 0x37A9),  -- 62 f1 75 08 ef ca        vpxord xmm1, xmm1, xmm2
  (0x37A9, .vprord 1 (.x 1) 7, 0x37B0),  -- 62 f1 75 08 72 c1 07     vprord xmm1, xmm1, 0x7
  (0x37B0, .pshufd 0 (.x 0) 147, 0x37B5),  -- c5 f9 70 c0 93           vpshufd xmm0, xmm0, 0x93
  (0x37B5, .pshufd 3 (.x 3) 78, 0x37BA),  -- c5 f9 70 db 4e           vpshufd xmm3, xmm3, 0x4e
  (0x37BA, .pshufd 2 (.x 2) 57, 0x37BF),  -- c5 f9 70 d2 39           vpshufd xmm2, xmm2, 0x39
  (0x37BF, .vpaddd 0 0 (.x 6), 0x37C3),  -- c5 f9 fe c6              vpaddd xmm0, xmm0, xmm6
  (0x37C3, .vpaddd 0 0 (.x 1), 0x37C7),  -- c5 f9 fe c1              vpaddd xmm0, xmm0, xmm1
  (0x37C7, .vpxor 3 3 (.x 0), 0x37CD),  -- 62 f1 65 08 ef d8        vpxord xmm3, xmm3, xmm0
  (0x37CD, .vprord 3 (.x 3) 16, 0x37D4),  -- 62 f1 65 08 72 c3 10     vprord xmm3, xmm3, 0x10
  (0x37D4, .vpaddd 2 2 (.x 3), 0x37D8),  -- c5 e9 fe d3              vpaddd xmm2, xmm2, xmm3
  (0x37D8, .vpxor 1 1 (.x 2), 0x37DE),  -- 62 f1 75 08 ef ca        vpxord xmm1, xmm1, xmm2
  (0x37DE, .vprord 1 (.x 1) 12, 0x37E5),  -- 62 f1 75 08 72 c1 0c     vprord xmm1, xmm1, 0xc
  (0x37E5, .vpaddd 0 0 (.x 7), 0x37E9),  -- c5 f9 fe c7              vpaddd xmm0, xmm0, xmm7
  (0x37E9, .vpaddd 0 0 (.x 1), 0x37ED),  -- c5 f9 fe c1              vpaddd xmm0, xmm0, xmm1
  (0x37ED, .vpxor 3 3 (.x 0), 0x37F3),  -- 62 f1 65 08 ef d8        vpxord xmm3, xmm3, xmm0
  (0x37F3, .vprord 3 (.x 3) 8, 0x37FA),  -- 62 f1 65 08 72 c3 08     vprord xmm3, xmm3, 0x8
  (0x37FA, .vpaddd 2 2 (.x 3), 0x37FE),  -- c5 e9 fe d3              vpaddd xmm2, xmm2, xmm3
  (0x37FE, .vpxor 1 1 (.x 2), 0x3804),  -- 62 f1 75 08 ef ca        vpxord xmm1, xmm1, xmm2
  (0x3804, .vprord 1 (.x 1) 7, 0x380B),  -- 62 f1 75 08 72 c1 07     vprord xmm1, xmm1, 0x7
  (0x380B, .pshufd 0 (.x 0) 57, 0x3810),  -- c5 f9 70 c0 39           vpshufd xmm0, xmm0, 0x39
  (0x3810, .pshufd 3 (.x 3) 78, 0x3815),  -- c5 f9 70 db 4e           vpshufd xmm3, xmm3, 0x4e
  (0x3815, .pshufd 2 (.x 2) 147, 0x381A),  -- c5 f9 70 d2 93           vpshufd xmm2, xmm2, 0x93
  (0x381A, .decb .rax, 0x381C),  -- fe c8                    dec al
  (0x381C, .je 0x3863, 0x381E),  -- 74 45                    je 0x3863 <blake3_servil_compress_in_place_avx512+0x163>
  (0x381E, .vshufps 8 4 (.x 5) 214, 0x3823),  -- c5 58 c6 c5 d6           vshufps xmm8, xmm4, xmm5, 0xd6
  (0x3823, .pshufd 9 (.x 4) 15, 0x3828),  -- c5 79 70 cc 0f           vpshufd xmm9, xmm4, 0xf
  (0x3828, .pshufd 4 (.x 8) 57, 0x382E),  -- c4 c1 79 70 e0 39        vpshufd xmm4, xmm8, 0x39
  (0x382E, .vshufps 8 6 (.x 7) 250, 0x3833),  -- c5 48 c6 c7 fa           vshufps xmm8, xmm6, xmm7, 0xfa
  (0x3833, .vpblendd 9 9 (.x 8) 170, 0x3839),  -- c4 43 31 02 c8 aa        vpblendd xmm9, xmm9, xmm8, 0xaa
  (0x3839, .vpunpcklqdq 8 7 (.x 5), 0x383D),  -- c5 41 6c c5              vpunpcklqdq xmm8, xmm7, xmm5
  (0x383D, .vpblendd 8 8 (.x 6) 136, 0x3843),  -- c4 63 39 02 c6 88        vpblendd xmm8, xmm8, xmm6, 0x88
  (0x3843, .pshufd 8 (.x 8) 120, 0x3849),  -- c4 41 79 70 c0 78        vpshufd xmm8, xmm8, 0x78
  (0x3849, .vpunpckhdq 5 5 (.x 7), 0x384D),  -- c5 d1 6a ef              vpunpckhdq xmm5, xmm5, xmm7
  (0x384D, .vpunpckldq 6 6 (.x 5), 0x3851),  -- c5 c9 62 f5              vpunpckldq xmm6, xmm6, xmm5
  (0x3851, .pshufd 7 (.x 6) 30, 0x3856),  -- c5 f9 70 fe 1e           vpshufd xmm7, xmm6, 0x1e
  (0x3856, .movv 5 (.x 9), 0x385A),  -- c5 79 7f cd              vmovdqa xmm5, xmm9
  (0x385A, .movv 6 (.x 8), 0x385E),  -- c5 79 7f c6              vmovdqa xmm6, xmm8
  (0x385E, .jmp 0x3764, 0x3863),  -- e9 01 ff ff ff           jmp 0x3764 <blake3_servil_compress_in_place_avx512+0x64>
  (0x3863, .vpxor 0 0 (.x 2), 0x3867),  -- c5 f9 ef c2              vpxor xmm0, xmm0, xmm2
  (0x3867, .vpxor 1 1 (.x 3), 0x386B),  -- c5 f1 ef cb              vpxor xmm1, xmm1, xmm3
  (0x386B, .storev .rdi 0x0 0, 0x386F),  -- c5 fa 7f 07              vmovdqu xmmword ptr [rdi], xmm0
  (0x386F, .storev .rdi 0x10 1, 0x3874),  -- c5 fa 7f 4f 10           vmovdqu xmmword ptr [rdi + 0x10], xmm1
  (0x3874, .ret, 0x3875)  -- c3                       ret 
]

/-- Each instruction's bytes, in the table's order (for the cross-check against a CPU). -/
def bytes : List String := ["c5fa6f07", "c5fa6f4f10", "410fb6c0", "0fb6d2", "48c1e020", "4801c2", "c4e1f96ed9", "c4e1f96ee2", "c5e16cdc", "c5f8281500000000", "c5781006", "c578104e10", "c4c138c6e188", "c4c138c6e9dd", "c578104620", "c578104e30", "c4c138c6f188", "c4c138c6f9dd", "c5f970f693", "c5f970ff93", "b007", "c5f9fec4", "c5f9fec1", "62f16508efd8", "62f1650872c310", "c5e9fed3", "62f17508efca", "62f1750872c10c", "c5f9fec5", "c5f9fec1", "62f16508efd8", "62f1650872c308", "c5e9fed3", "62f17508efca", "62f1750872c107", "c5f970c093", "c5f970db4e", "c5f970d239", "c5f9fec6", "c5f9fec1", "62f16508efd8", "62f1650872c310", "c5e9fed3", "62f17508efca", "62f1750872c10c", "c5f9fec7", "c5f9fec1", "62f16508efd8", "62f1650872c308", "c5e9fed3", "62f17508efca", "62f1750872c107", "c5f970c039", "c5f970db4e", "c5f970d293", "fec8", "7445", "c558c6c5d6", "c57970cc0f", "c4c17970e039", "c548c6c7fa", "c4433102c8aa", "c5416cc5", "c4633902c688", "c4417970c078", "c5d16aef", "c5c962f5", "c5f970fe1e", "c5797fcd", "c5797fc6", "e901ffffff", "c5f9efc2", "c5f1efcb", "c5fa7f07", "c5fa7f4f10", "c3"]

def prog (pc : Nat) : Option (Instr × Nat) := table.lookup pc

theorem at_3700 : prog 0x3700 = some (.movv 0 (.m .rdi 0x0), 0x3704) := rfl
theorem at_3704 : prog 0x3704 = some (.movv 1 (.m .rdi 0x10), 0x3709) := rfl
theorem at_3709 : prog 0x3709 = some (.movzx8 .rax .r8, 0x370D) := rfl
theorem at_370D : prog 0x370D = some (.movzx8 .rdx .rdx, 0x3710) := rfl
theorem at_3710 : prog 0x3710 = some (.shl64 .rax 32, 0x3714) := rfl
theorem at_3714 : prog 0x3714 = some (.add64 .rdx .rax, 0x3717) := rfl
theorem at_3717 : prog 0x3717 = some (.movq 3 .rcx, 0x371C) := rfl
theorem at_371C : prog 0x371C = some (.movq 4 .rdx, 0x3721) := rfl
theorem at_3721 : prog 0x3721 = some (.vpunpcklqdq 3 3 (.x 4), 0x3725) := rfl
theorem at_3725 : prog 0x3725 = some (.movv 2 (.c 0xA54FF53A3C6EF372BB67AE856A09E667#128), 0x372D) := rfl
theorem at_372D : prog 0x372D = some (.movv 8 (.m .rsi 0x0), 0x3731) := rfl
theorem at_3731 : prog 0x3731 = some (.movv 9 (.m .rsi 0x10), 0x3736) := rfl
theorem at_3736 : prog 0x3736 = some (.vshufps 4 8 (.x 9) 136, 0x373C) := rfl
theorem at_373C : prog 0x373C = some (.vshufps 5 8 (.x 9) 221, 0x3742) := rfl
theorem at_3742 : prog 0x3742 = some (.movv 8 (.m .rsi 0x20), 0x3747) := rfl
theorem at_3747 : prog 0x3747 = some (.movv 9 (.m .rsi 0x30), 0x374C) := rfl
theorem at_374C : prog 0x374C = some (.vshufps 6 8 (.x 9) 136, 0x3752) := rfl
theorem at_3752 : prog 0x3752 = some (.vshufps 7 8 (.x 9) 221, 0x3758) := rfl
theorem at_3758 : prog 0x3758 = some (.pshufd 6 (.x 6) 147, 0x375D) := rfl
theorem at_375D : prog 0x375D = some (.pshufd 7 (.x 7) 147, 0x3762) := rfl
theorem at_3762 : prog 0x3762 = some (.movb .rax 7, 0x3764) := rfl
theorem at_3764 : prog 0x3764 = some (.vpaddd 0 0 (.x 4), 0x3768) := rfl
theorem at_3768 : prog 0x3768 = some (.vpaddd 0 0 (.x 1), 0x376C) := rfl
theorem at_376C : prog 0x376C = some (.vpxor 3 3 (.x 0), 0x3772) := rfl
theorem at_3772 : prog 0x3772 = some (.vprord 3 (.x 3) 16, 0x3779) := rfl
theorem at_3779 : prog 0x3779 = some (.vpaddd 2 2 (.x 3), 0x377D) := rfl
theorem at_377D : prog 0x377D = some (.vpxor 1 1 (.x 2), 0x3783) := rfl
theorem at_3783 : prog 0x3783 = some (.vprord 1 (.x 1) 12, 0x378A) := rfl
theorem at_378A : prog 0x378A = some (.vpaddd 0 0 (.x 5), 0x378E) := rfl
theorem at_378E : prog 0x378E = some (.vpaddd 0 0 (.x 1), 0x3792) := rfl
theorem at_3792 : prog 0x3792 = some (.vpxor 3 3 (.x 0), 0x3798) := rfl
theorem at_3798 : prog 0x3798 = some (.vprord 3 (.x 3) 8, 0x379F) := rfl
theorem at_379F : prog 0x379F = some (.vpaddd 2 2 (.x 3), 0x37A3) := rfl
theorem at_37A3 : prog 0x37A3 = some (.vpxor 1 1 (.x 2), 0x37A9) := rfl
theorem at_37A9 : prog 0x37A9 = some (.vprord 1 (.x 1) 7, 0x37B0) := rfl
theorem at_37B0 : prog 0x37B0 = some (.pshufd 0 (.x 0) 147, 0x37B5) := rfl
theorem at_37B5 : prog 0x37B5 = some (.pshufd 3 (.x 3) 78, 0x37BA) := rfl
theorem at_37BA : prog 0x37BA = some (.pshufd 2 (.x 2) 57, 0x37BF) := rfl
theorem at_37BF : prog 0x37BF = some (.vpaddd 0 0 (.x 6), 0x37C3) := rfl
theorem at_37C3 : prog 0x37C3 = some (.vpaddd 0 0 (.x 1), 0x37C7) := rfl
theorem at_37C7 : prog 0x37C7 = some (.vpxor 3 3 (.x 0), 0x37CD) := rfl
theorem at_37CD : prog 0x37CD = some (.vprord 3 (.x 3) 16, 0x37D4) := rfl
theorem at_37D4 : prog 0x37D4 = some (.vpaddd 2 2 (.x 3), 0x37D8) := rfl
theorem at_37D8 : prog 0x37D8 = some (.vpxor 1 1 (.x 2), 0x37DE) := rfl
theorem at_37DE : prog 0x37DE = some (.vprord 1 (.x 1) 12, 0x37E5) := rfl
theorem at_37E5 : prog 0x37E5 = some (.vpaddd 0 0 (.x 7), 0x37E9) := rfl
theorem at_37E9 : prog 0x37E9 = some (.vpaddd 0 0 (.x 1), 0x37ED) := rfl
theorem at_37ED : prog 0x37ED = some (.vpxor 3 3 (.x 0), 0x37F3) := rfl
theorem at_37F3 : prog 0x37F3 = some (.vprord 3 (.x 3) 8, 0x37FA) := rfl
theorem at_37FA : prog 0x37FA = some (.vpaddd 2 2 (.x 3), 0x37FE) := rfl
theorem at_37FE : prog 0x37FE = some (.vpxor 1 1 (.x 2), 0x3804) := rfl
theorem at_3804 : prog 0x3804 = some (.vprord 1 (.x 1) 7, 0x380B) := rfl
theorem at_380B : prog 0x380B = some (.pshufd 0 (.x 0) 57, 0x3810) := rfl
theorem at_3810 : prog 0x3810 = some (.pshufd 3 (.x 3) 78, 0x3815) := rfl
theorem at_3815 : prog 0x3815 = some (.pshufd 2 (.x 2) 147, 0x381A) := rfl
theorem at_381A : prog 0x381A = some (.decb .rax, 0x381C) := rfl
theorem at_381C : prog 0x381C = some (.je 0x3863, 0x381E) := rfl
theorem at_381E : prog 0x381E = some (.vshufps 8 4 (.x 5) 214, 0x3823) := rfl
theorem at_3823 : prog 0x3823 = some (.pshufd 9 (.x 4) 15, 0x3828) := rfl
theorem at_3828 : prog 0x3828 = some (.pshufd 4 (.x 8) 57, 0x382E) := rfl
theorem at_382E : prog 0x382E = some (.vshufps 8 6 (.x 7) 250, 0x3833) := rfl
theorem at_3833 : prog 0x3833 = some (.vpblendd 9 9 (.x 8) 170, 0x3839) := rfl
theorem at_3839 : prog 0x3839 = some (.vpunpcklqdq 8 7 (.x 5), 0x383D) := rfl
theorem at_383D : prog 0x383D = some (.vpblendd 8 8 (.x 6) 136, 0x3843) := rfl
theorem at_3843 : prog 0x3843 = some (.pshufd 8 (.x 8) 120, 0x3849) := rfl
theorem at_3849 : prog 0x3849 = some (.vpunpckhdq 5 5 (.x 7), 0x384D) := rfl
theorem at_384D : prog 0x384D = some (.vpunpckldq 6 6 (.x 5), 0x3851) := rfl
theorem at_3851 : prog 0x3851 = some (.pshufd 7 (.x 6) 30, 0x3856) := rfl
theorem at_3856 : prog 0x3856 = some (.movv 5 (.x 9), 0x385A) := rfl
theorem at_385A : prog 0x385A = some (.movv 6 (.x 8), 0x385E) := rfl
theorem at_385E : prog 0x385E = some (.jmp 0x3764, 0x3863) := rfl
theorem at_3863 : prog 0x3863 = some (.vpxor 0 0 (.x 2), 0x3867) := rfl
theorem at_3867 : prog 0x3867 = some (.vpxor 1 1 (.x 3), 0x386B) := rfl
theorem at_386B : prog 0x386B = some (.storev .rdi 0x0 0, 0x386F) := rfl
theorem at_386F : prog 0x386F = some (.storev .rdi 0x10 1, 0x3874) := rfl
theorem at_3874 : prog 0x3874 = some (.ret, 0x3875) := rfl

end Code
