import Simd

/-! `blake3_servil_compress_in_place_sse41` of sse41.o, as llvm-objdump reads it. Written by lift_simd.py. -/

set_option maxRecDepth 100000
namespace CodeSse
open Simd

def entry : Nat := 0x25C0

def table : List (Nat × Instr × Nat) := [
  (0x25C0, .movv 0 (.m .rdi 0x0), 0x25C3),  -- 0f 10 07                 movups xmm0, xmmword ptr [rdi]
  (0x25C3, .movv 1 (.m .rdi 0x10), 0x25C7),  -- 0f 10 4f 10              movups xmm1, xmmword ptr [rdi + 0x10]
  (0x25C7, .movv 2 (.c 0xA54FF53A3C6EF372BB67AE856A09E667#128), 0x25CE),  -- 0f 28 15 00 00 00 00     movaps xmm2, xmmword ptr [rip]
  (0x25CE, .shl64 .r8 32, 0x25D2),  -- 49 c1 e0 20              shl r8, 0x20
  (0x25D2, .add64 .rdx .r8, 0x25D5),  -- 4c 01 c2                 add rdx, r8
  (0x25D5, .movq 3 .rcx, 0x25DA),  -- 66 48 0f 6e d9           movq xmm3, rcx
  (0x25DA, .movq 4 .rdx, 0x25DF),  -- 66 48 0f 6e e2           movq xmm4, rdx
  (0x25DF, .punpcklqdq 3 (.x 4), 0x25E3),  -- 66 0f 6c dc              punpcklqdq xmm3, xmm4
  (0x25E3, .movv 4 (.m .rsi 0x0), 0x25E6),  -- 0f 10 26                 movups xmm4, xmmword ptr [rsi]
  (0x25E6, .movv 5 (.m .rsi 0x10), 0x25EA),  -- 0f 10 6e 10              movups xmm5, xmmword ptr [rsi + 0x10]
  (0x25EA, .movv 8 (.x 4), 0x25EE),  -- 44 0f 28 c4              movaps xmm8, xmm4
  (0x25EE, .shufps 4 (.x 5) 136, 0x25F2),  -- 0f c6 e5 88              shufps xmm4, xmm5, 0x88
  (0x25F2, .shufps 8 (.x 5) 221, 0x25F7),  -- 44 0f c6 c5 dd           shufps xmm8, xmm5, 0xdd
  (0x25F7, .movv 5 (.x 8), 0x25FB),  -- 41 0f 28 e8              movaps xmm5, xmm8
  (0x25FB, .movv 6 (.m .rsi 0x20), 0x25FF),  -- 0f 10 76 20              movups xmm6, xmmword ptr [rsi + 0x20]
  (0x25FF, .movv 7 (.m .rsi 0x30), 0x2603),  -- 0f 10 7e 30              movups xmm7, xmmword ptr [rsi + 0x30]
  (0x2603, .movv 8 (.x 6), 0x2607),  -- 44 0f 28 c6              movaps xmm8, xmm6
  (0x2607, .shufps 6 (.x 7) 136, 0x260B),  -- 0f c6 f7 88              shufps xmm6, xmm7, 0x88
  (0x260B, .pshufd 6 (.x 6) 147, 0x2610),  -- 66 0f 70 f6 93           pshufd xmm6, xmm6, 0x93
  (0x2610, .shufps 8 (.x 7) 221, 0x2615),  -- 44 0f c6 c7 dd           shufps xmm8, xmm7, 0xdd
  (0x2615, .pshufd 7 (.x 8) 147, 0x261B),  -- 66 41 0f 70 f8 93        pshufd xmm7, xmm8, 0x93
  (0x261B, .movv 14 (.c 0x0C0F0E0D080B0A090407060500030201#128), 0x2623),  -- 44 0f 28 35 00 00 00 00  movaps xmm14, xmmword ptr [rip]
  (0x2623, .movv 15 (.c 0x0D0C0F0E09080B0A0504070601000302#128), 0x262B),  -- 44 0f 28 3d 00 00 00 00  movaps xmm15, xmmword ptr [rip]
  (0x262B, .movb .rax 7, 0x262D),  -- b0 07                    mov al, 0x7
  (0x262D, .paddd 0 (.x 4), 0x2631),  -- 66 0f fe c4              paddd xmm0, xmm4
  (0x2631, .paddd 0 (.x 1), 0x2635),  -- 66 0f fe c1              paddd xmm0, xmm1
  (0x2635, .pxor 3 (.x 0), 0x2639),  -- 66 0f ef d8              pxor xmm3, xmm0
  (0x2639, .pshufb 3 (.x 15), 0x263F),  -- 66 41 0f 38 00 df        pshufb xmm3, xmm15
  (0x263F, .paddd 2 (.x 3), 0x2643),  -- 66 0f fe d3              paddd xmm2, xmm3
  (0x2643, .pxor 1 (.x 2), 0x2647),  -- 66 0f ef ca              pxor xmm1, xmm2
  (0x2647, .movv 11 (.x 1), 0x264C),  -- 66 44 0f 6f d9           movdqa xmm11, xmm1
  (0x264C, .pslld 1 20, 0x2651),  -- 66 0f 72 f1 14           pslld xmm1, 0x14
  (0x2651, .psrld 11 12, 0x2657),  -- 66 41 0f 72 d3 0c        psrld xmm11, 0xc
  (0x2657, .por 1 (.x 11), 0x265C),  -- 66 41 0f eb cb           por xmm1, xmm11
  (0x265C, .paddd 0 (.x 5), 0x2660),  -- 66 0f fe c5              paddd xmm0, xmm5
  (0x2660, .paddd 0 (.x 1), 0x2664),  -- 66 0f fe c1              paddd xmm0, xmm1
  (0x2664, .pxor 3 (.x 0), 0x2668),  -- 66 0f ef d8              pxor xmm3, xmm0
  (0x2668, .pshufb 3 (.x 14), 0x266E),  -- 66 41 0f 38 00 de        pshufb xmm3, xmm14
  (0x266E, .paddd 2 (.x 3), 0x2672),  -- 66 0f fe d3              paddd xmm2, xmm3
  (0x2672, .pxor 1 (.x 2), 0x2676),  -- 66 0f ef ca              pxor xmm1, xmm2
  (0x2676, .movv 11 (.x 1), 0x267B),  -- 66 44 0f 6f d9           movdqa xmm11, xmm1
  (0x267B, .pslld 1 25, 0x2680),  -- 66 0f 72 f1 19           pslld xmm1, 0x19
  (0x2680, .psrld 11 7, 0x2686),  -- 66 41 0f 72 d3 07        psrld xmm11, 0x7
  (0x2686, .por 1 (.x 11), 0x268B),  -- 66 41 0f eb cb           por xmm1, xmm11
  (0x268B, .pshufd 0 (.x 0) 147, 0x2690),  -- 66 0f 70 c0 93           pshufd xmm0, xmm0, 0x93
  (0x2690, .pshufd 3 (.x 3) 78, 0x2695),  -- 66 0f 70 db 4e           pshufd xmm3, xmm3, 0x4e
  (0x2695, .pshufd 2 (.x 2) 57, 0x269A),  -- 66 0f 70 d2 39           pshufd xmm2, xmm2, 0x39
  (0x269A, .paddd 0 (.x 6), 0x269E),  -- 66 0f fe c6              paddd xmm0, xmm6
  (0x269E, .paddd 0 (.x 1), 0x26A2),  -- 66 0f fe c1              paddd xmm0, xmm1
  (0x26A2, .pxor 3 (.x 0), 0x26A6),  -- 66 0f ef d8              pxor xmm3, xmm0
  (0x26A6, .pshufb 3 (.x 15), 0x26AC),  -- 66 41 0f 38 00 df        pshufb xmm3, xmm15
  (0x26AC, .paddd 2 (.x 3), 0x26B0),  -- 66 0f fe d3              paddd xmm2, xmm3
  (0x26B0, .pxor 1 (.x 2), 0x26B4),  -- 66 0f ef ca              pxor xmm1, xmm2
  (0x26B4, .movv 11 (.x 1), 0x26B9),  -- 66 44 0f 6f d9           movdqa xmm11, xmm1
  (0x26B9, .pslld 1 20, 0x26BE),  -- 66 0f 72 f1 14           pslld xmm1, 0x14
  (0x26BE, .psrld 11 12, 0x26C4),  -- 66 41 0f 72 d3 0c        psrld xmm11, 0xc
  (0x26C4, .por 1 (.x 11), 0x26C9),  -- 66 41 0f eb cb           por xmm1, xmm11
  (0x26C9, .paddd 0 (.x 7), 0x26CD),  -- 66 0f fe c7              paddd xmm0, xmm7
  (0x26CD, .paddd 0 (.x 1), 0x26D1),  -- 66 0f fe c1              paddd xmm0, xmm1
  (0x26D1, .pxor 3 (.x 0), 0x26D5),  -- 66 0f ef d8              pxor xmm3, xmm0
  (0x26D5, .pshufb 3 (.x 14), 0x26DB),  -- 66 41 0f 38 00 de        pshufb xmm3, xmm14
  (0x26DB, .paddd 2 (.x 3), 0x26DF),  -- 66 0f fe d3              paddd xmm2, xmm3
  (0x26DF, .pxor 1 (.x 2), 0x26E3),  -- 66 0f ef ca              pxor xmm1, xmm2
  (0x26E3, .movv 11 (.x 1), 0x26E8),  -- 66 44 0f 6f d9           movdqa xmm11, xmm1
  (0x26E8, .pslld 1 25, 0x26ED),  -- 66 0f 72 f1 19           pslld xmm1, 0x19
  (0x26ED, .psrld 11 7, 0x26F3),  -- 66 41 0f 72 d3 07        psrld xmm11, 0x7
  (0x26F3, .por 1 (.x 11), 0x26F8),  -- 66 41 0f eb cb           por xmm1, xmm11
  (0x26F8, .pshufd 0 (.x 0) 57, 0x26FD),  -- 66 0f 70 c0 39           pshufd xmm0, xmm0, 0x39
  (0x26FD, .pshufd 3 (.x 3) 78, 0x2702),  -- 66 0f 70 db 4e           pshufd xmm3, xmm3, 0x4e
  (0x2702, .pshufd 2 (.x 2) 147, 0x2707),  -- 66 0f 70 d2 93           pshufd xmm2, xmm2, 0x93
  (0x2707, .decb .rax, 0x2709),  -- fe c8                    dec al
  (0x2709, .je 0x2765, 0x270B),  -- 74 5a                    je 0x2765 <blake3_servil_compress_in_place_sse41+0x1a5>
  (0x270B, .movv 8 (.x 4), 0x2710),  -- 66 44 0f 6f c4           movdqa xmm8, xmm4
  (0x2710, .shufps 8 (.x 5) 214, 0x2715),  -- 44 0f c6 c5 d6           shufps xmm8, xmm5, 0xd6
  (0x2715, .pshufd 9 (.x 4) 15, 0x271B),  -- 66 44 0f 70 cc 0f        pshufd xmm9, xmm4, 0xf
  (0x271B, .pshufd 4 (.x 8) 57, 0x2721),  -- 66 41 0f 70 e0 39        pshufd xmm4, xmm8, 0x39
  (0x2721, .movv 8 (.x 6), 0x2726),  -- 66 44 0f 6f c6           movdqa xmm8, xmm6
  (0x2726, .shufps 8 (.x 7) 250, 0x272B),  -- 44 0f c6 c7 fa           shufps xmm8, xmm7, 0xfa
  (0x272B, .pblendw 9 (.x 8) 204, 0x2732),  -- 66 45 0f 3a 0e c8 cc     pblendw xmm9, xmm8, 0xcc
  (0x2732, .movv 8 (.x 7), 0x2737),  -- 66 44 0f 6f c7           movdqa xmm8, xmm7
  (0x2737, .punpcklqdq 8 (.x 5), 0x273C),  -- 66 44 0f 6c c5           punpcklqdq xmm8, xmm5
  (0x273C, .pblendw 8 (.x 6) 192, 0x2743),  -- 66 44 0f 3a 0e c6 c0     pblendw xmm8, xmm6, 0xc0
  (0x2743, .pshufd 8 (.x 8) 120, 0x2749),  -- 66 45 0f 70 c0 78        pshufd xmm8, xmm8, 0x78
  (0x2749, .punpckhdq 5 (.x 7), 0x274D),  -- 66 0f 6a ef              punpckhdq xmm5, xmm7
  (0x274D, .punpckldq 6 (.x 5), 0x2751),  -- 66 0f 62 f5              punpckldq xmm6, xmm5
  (0x2751, .pshufd 7 (.x 6) 30, 0x2756),  -- 66 0f 70 fe 1e           pshufd xmm7, xmm6, 0x1e
  (0x2756, .movv 5 (.x 9), 0x275B),  -- 66 41 0f 6f e9           movdqa xmm5, xmm9
  (0x275B, .movv 6 (.x 8), 0x2760),  -- 66 41 0f 6f f0           movdqa xmm6, xmm8
  (0x2760, .jmp 0x262D, 0x2765),  -- e9 c8 fe ff ff           jmp 0x262d <blake3_servil_compress_in_place_sse41+0x6d>
  (0x2765, .pxor 0 (.x 2), 0x2769),  -- 66 0f ef c2              pxor xmm0, xmm2
  (0x2769, .pxor 1 (.x 3), 0x276D),  -- 66 0f ef cb              pxor xmm1, xmm3
  (0x276D, .storev .rdi 0x0 0, 0x2770),  -- 0f 11 07                 movups xmmword ptr [rdi], xmm0
  (0x2770, .storev .rdi 0x10 1, 0x2774),  -- 0f 11 4f 10              movups xmmword ptr [rdi + 0x10], xmm1
  (0x2774, .ret, 0x2775)  -- c3                       ret 
]

/-- Each instruction's bytes, in the table's order (for the cross-check against a CPU). -/
def bytes : List String := ["0f1007", "0f104f10", "0f281500000000", "49c1e020", "4c01c2", "66480f6ed9", "66480f6ee2", "660f6cdc", "0f1026", "0f106e10", "440f28c4", "0fc6e588", "440fc6c5dd", "410f28e8", "0f107620", "0f107e30", "440f28c6", "0fc6f788", "660f70f693", "440fc6c7dd", "66410f70f893", "440f283500000000", "440f283d00000000", "b007", "660ffec4", "660ffec1", "660fefd8", "66410f3800df", "660ffed3", "660fefca", "66440f6fd9", "660f72f114", "66410f72d30c", "66410febcb", "660ffec5", "660ffec1", "660fefd8", "66410f3800de", "660ffed3", "660fefca", "66440f6fd9", "660f72f119", "66410f72d307", "66410febcb", "660f70c093", "660f70db4e", "660f70d239", "660ffec6", "660ffec1", "660fefd8", "66410f3800df", "660ffed3", "660fefca", "66440f6fd9", "660f72f114", "66410f72d30c", "66410febcb", "660ffec7", "660ffec1", "660fefd8", "66410f3800de", "660ffed3", "660fefca", "66440f6fd9", "660f72f119", "66410f72d307", "66410febcb", "660f70c039", "660f70db4e", "660f70d293", "fec8", "745a", "66440f6fc4", "440fc6c5d6", "66440f70cc0f", "66410f70e039", "66440f6fc6", "440fc6c7fa", "66450f3a0ec8cc", "66440f6fc7", "66440f6cc5", "66440f3a0ec6c0", "66450f70c078", "660f6aef", "660f62f5", "660f70fe1e", "66410f6fe9", "66410f6ff0", "e9c8feffff", "660fefc2", "660fefcb", "0f1107", "0f114f10", "c3"]

def prog (pc : Nat) : Option (Instr × Nat) := table.lookup pc

theorem at_25C0 : prog 0x25C0 = some (.movv 0 (.m .rdi 0x0), 0x25C3) := rfl
theorem at_25C3 : prog 0x25C3 = some (.movv 1 (.m .rdi 0x10), 0x25C7) := rfl
theorem at_25C7 : prog 0x25C7 = some (.movv 2 (.c 0xA54FF53A3C6EF372BB67AE856A09E667#128), 0x25CE) := rfl
theorem at_25CE : prog 0x25CE = some (.shl64 .r8 32, 0x25D2) := rfl
theorem at_25D2 : prog 0x25D2 = some (.add64 .rdx .r8, 0x25D5) := rfl
theorem at_25D5 : prog 0x25D5 = some (.movq 3 .rcx, 0x25DA) := rfl
theorem at_25DA : prog 0x25DA = some (.movq 4 .rdx, 0x25DF) := rfl
theorem at_25DF : prog 0x25DF = some (.punpcklqdq 3 (.x 4), 0x25E3) := rfl
theorem at_25E3 : prog 0x25E3 = some (.movv 4 (.m .rsi 0x0), 0x25E6) := rfl
theorem at_25E6 : prog 0x25E6 = some (.movv 5 (.m .rsi 0x10), 0x25EA) := rfl
theorem at_25EA : prog 0x25EA = some (.movv 8 (.x 4), 0x25EE) := rfl
theorem at_25EE : prog 0x25EE = some (.shufps 4 (.x 5) 136, 0x25F2) := rfl
theorem at_25F2 : prog 0x25F2 = some (.shufps 8 (.x 5) 221, 0x25F7) := rfl
theorem at_25F7 : prog 0x25F7 = some (.movv 5 (.x 8), 0x25FB) := rfl
theorem at_25FB : prog 0x25FB = some (.movv 6 (.m .rsi 0x20), 0x25FF) := rfl
theorem at_25FF : prog 0x25FF = some (.movv 7 (.m .rsi 0x30), 0x2603) := rfl
theorem at_2603 : prog 0x2603 = some (.movv 8 (.x 6), 0x2607) := rfl
theorem at_2607 : prog 0x2607 = some (.shufps 6 (.x 7) 136, 0x260B) := rfl
theorem at_260B : prog 0x260B = some (.pshufd 6 (.x 6) 147, 0x2610) := rfl
theorem at_2610 : prog 0x2610 = some (.shufps 8 (.x 7) 221, 0x2615) := rfl
theorem at_2615 : prog 0x2615 = some (.pshufd 7 (.x 8) 147, 0x261B) := rfl
theorem at_261B : prog 0x261B = some (.movv 14 (.c 0x0C0F0E0D080B0A090407060500030201#128), 0x2623) := rfl
theorem at_2623 : prog 0x2623 = some (.movv 15 (.c 0x0D0C0F0E09080B0A0504070601000302#128), 0x262B) := rfl
theorem at_262B : prog 0x262B = some (.movb .rax 7, 0x262D) := rfl
theorem at_262D : prog 0x262D = some (.paddd 0 (.x 4), 0x2631) := rfl
theorem at_2631 : prog 0x2631 = some (.paddd 0 (.x 1), 0x2635) := rfl
theorem at_2635 : prog 0x2635 = some (.pxor 3 (.x 0), 0x2639) := rfl
theorem at_2639 : prog 0x2639 = some (.pshufb 3 (.x 15), 0x263F) := rfl
theorem at_263F : prog 0x263F = some (.paddd 2 (.x 3), 0x2643) := rfl
theorem at_2643 : prog 0x2643 = some (.pxor 1 (.x 2), 0x2647) := rfl
theorem at_2647 : prog 0x2647 = some (.movv 11 (.x 1), 0x264C) := rfl
theorem at_264C : prog 0x264C = some (.pslld 1 20, 0x2651) := rfl
theorem at_2651 : prog 0x2651 = some (.psrld 11 12, 0x2657) := rfl
theorem at_2657 : prog 0x2657 = some (.por 1 (.x 11), 0x265C) := rfl
theorem at_265C : prog 0x265C = some (.paddd 0 (.x 5), 0x2660) := rfl
theorem at_2660 : prog 0x2660 = some (.paddd 0 (.x 1), 0x2664) := rfl
theorem at_2664 : prog 0x2664 = some (.pxor 3 (.x 0), 0x2668) := rfl
theorem at_2668 : prog 0x2668 = some (.pshufb 3 (.x 14), 0x266E) := rfl
theorem at_266E : prog 0x266E = some (.paddd 2 (.x 3), 0x2672) := rfl
theorem at_2672 : prog 0x2672 = some (.pxor 1 (.x 2), 0x2676) := rfl
theorem at_2676 : prog 0x2676 = some (.movv 11 (.x 1), 0x267B) := rfl
theorem at_267B : prog 0x267B = some (.pslld 1 25, 0x2680) := rfl
theorem at_2680 : prog 0x2680 = some (.psrld 11 7, 0x2686) := rfl
theorem at_2686 : prog 0x2686 = some (.por 1 (.x 11), 0x268B) := rfl
theorem at_268B : prog 0x268B = some (.pshufd 0 (.x 0) 147, 0x2690) := rfl
theorem at_2690 : prog 0x2690 = some (.pshufd 3 (.x 3) 78, 0x2695) := rfl
theorem at_2695 : prog 0x2695 = some (.pshufd 2 (.x 2) 57, 0x269A) := rfl
theorem at_269A : prog 0x269A = some (.paddd 0 (.x 6), 0x269E) := rfl
theorem at_269E : prog 0x269E = some (.paddd 0 (.x 1), 0x26A2) := rfl
theorem at_26A2 : prog 0x26A2 = some (.pxor 3 (.x 0), 0x26A6) := rfl
theorem at_26A6 : prog 0x26A6 = some (.pshufb 3 (.x 15), 0x26AC) := rfl
theorem at_26AC : prog 0x26AC = some (.paddd 2 (.x 3), 0x26B0) := rfl
theorem at_26B0 : prog 0x26B0 = some (.pxor 1 (.x 2), 0x26B4) := rfl
theorem at_26B4 : prog 0x26B4 = some (.movv 11 (.x 1), 0x26B9) := rfl
theorem at_26B9 : prog 0x26B9 = some (.pslld 1 20, 0x26BE) := rfl
theorem at_26BE : prog 0x26BE = some (.psrld 11 12, 0x26C4) := rfl
theorem at_26C4 : prog 0x26C4 = some (.por 1 (.x 11), 0x26C9) := rfl
theorem at_26C9 : prog 0x26C9 = some (.paddd 0 (.x 7), 0x26CD) := rfl
theorem at_26CD : prog 0x26CD = some (.paddd 0 (.x 1), 0x26D1) := rfl
theorem at_26D1 : prog 0x26D1 = some (.pxor 3 (.x 0), 0x26D5) := rfl
theorem at_26D5 : prog 0x26D5 = some (.pshufb 3 (.x 14), 0x26DB) := rfl
theorem at_26DB : prog 0x26DB = some (.paddd 2 (.x 3), 0x26DF) := rfl
theorem at_26DF : prog 0x26DF = some (.pxor 1 (.x 2), 0x26E3) := rfl
theorem at_26E3 : prog 0x26E3 = some (.movv 11 (.x 1), 0x26E8) := rfl
theorem at_26E8 : prog 0x26E8 = some (.pslld 1 25, 0x26ED) := rfl
theorem at_26ED : prog 0x26ED = some (.psrld 11 7, 0x26F3) := rfl
theorem at_26F3 : prog 0x26F3 = some (.por 1 (.x 11), 0x26F8) := rfl
theorem at_26F8 : prog 0x26F8 = some (.pshufd 0 (.x 0) 57, 0x26FD) := rfl
theorem at_26FD : prog 0x26FD = some (.pshufd 3 (.x 3) 78, 0x2702) := rfl
theorem at_2702 : prog 0x2702 = some (.pshufd 2 (.x 2) 147, 0x2707) := rfl
theorem at_2707 : prog 0x2707 = some (.decb .rax, 0x2709) := rfl
theorem at_2709 : prog 0x2709 = some (.je 0x2765, 0x270B) := rfl
theorem at_270B : prog 0x270B = some (.movv 8 (.x 4), 0x2710) := rfl
theorem at_2710 : prog 0x2710 = some (.shufps 8 (.x 5) 214, 0x2715) := rfl
theorem at_2715 : prog 0x2715 = some (.pshufd 9 (.x 4) 15, 0x271B) := rfl
theorem at_271B : prog 0x271B = some (.pshufd 4 (.x 8) 57, 0x2721) := rfl
theorem at_2721 : prog 0x2721 = some (.movv 8 (.x 6), 0x2726) := rfl
theorem at_2726 : prog 0x2726 = some (.shufps 8 (.x 7) 250, 0x272B) := rfl
theorem at_272B : prog 0x272B = some (.pblendw 9 (.x 8) 204, 0x2732) := rfl
theorem at_2732 : prog 0x2732 = some (.movv 8 (.x 7), 0x2737) := rfl
theorem at_2737 : prog 0x2737 = some (.punpcklqdq 8 (.x 5), 0x273C) := rfl
theorem at_273C : prog 0x273C = some (.pblendw 8 (.x 6) 192, 0x2743) := rfl
theorem at_2743 : prog 0x2743 = some (.pshufd 8 (.x 8) 120, 0x2749) := rfl
theorem at_2749 : prog 0x2749 = some (.punpckhdq 5 (.x 7), 0x274D) := rfl
theorem at_274D : prog 0x274D = some (.punpckldq 6 (.x 5), 0x2751) := rfl
theorem at_2751 : prog 0x2751 = some (.pshufd 7 (.x 6) 30, 0x2756) := rfl
theorem at_2756 : prog 0x2756 = some (.movv 5 (.x 9), 0x275B) := rfl
theorem at_275B : prog 0x275B = some (.movv 6 (.x 8), 0x2760) := rfl
theorem at_2760 : prog 0x2760 = some (.jmp 0x262D, 0x2765) := rfl
theorem at_2765 : prog 0x2765 = some (.pxor 0 (.x 2), 0x2769) := rfl
theorem at_2769 : prog 0x2769 = some (.pxor 1 (.x 3), 0x276D) := rfl
theorem at_276D : prog 0x276D = some (.storev .rdi 0x0 0, 0x2770) := rfl
theorem at_2770 : prog 0x2770 = some (.storev .rdi 0x10 1, 0x2774) := rfl
theorem at_2774 : prog 0x2774 = some (.ret, 0x2775) := rfl

end CodeSse
