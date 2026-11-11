import Machine

/-! `blake3_servil_compress_in_place_avx512`, as llvm-objdump reads it, placed at 0x30000. Written by lift_one.py. -/

set_option maxRecDepth 100000
namespace Avx
open X86

def entry : Nat := 0x30000

def table : List (Nat × Instr × Nat) := [
  (0x30000, .movv false 0 (.m .rdi 0x0), 0x30004),  -- c5 fa 6f 07                vmovdqu xmm0, xmmword ptr [rdi]
  (0x30004, .movv false 1 (.m .rdi 0x10), 0x30009),  -- c5 fa 6f 4f 10             vmovdqu xmm1, xmmword ptr [rdi + 0x10]
  (0x30009, .movzx8 .rax (.reg .r8), 0x3000D),  -- 41 0f b6 c0                movzx eax, r8b
  (0x3000D, .movzx8 .rdx (.reg .rdx), 0x30010),  -- 0f b6 d2                   movzx edx, dl
  (0x30010, .shl64 .rax 32, 0x30014),  -- 48 c1 e0 20                shl rax, 0x20
  (0x30014, .add 64 (.reg .rdx) (.reg .rax), 0x30017),  -- 48 01 c2                   add rdx, rax
  (0x30017, .movq 3 .rcx, 0x3001C),  -- c4 e1 f9 6e d9             vmovq xmm3, rcx
  (0x3001C, .movq 4 .rdx, 0x30021),  -- c4 e1 f9 6e e2             vmovq xmm4, rdx
  (0x30021, .vpunpcklqdq 3 3 (.x 4), 0x30025),  -- c5 e1 6c dc                vpunpcklqdq xmm3, xmm3, xmm4
  (0x30025, .movv false 2 (.c 0xA54FF53A3C6EF372BB67AE856A09E667#128), 0x3002D),  -- c5 f8 28 15 00 00 00 00    vmovaps xmm2, xmmword ptr [rip]
  (0x3002D, .movv false 8 (.m .rsi 0x0), 0x30031),  -- c5 78 10 06                vmovups xmm8, xmmword ptr [rsi]
  (0x30031, .movv false 9 (.m .rsi 0x10), 0x30036),  -- c5 78 10 4e 10             vmovups xmm9, xmmword ptr [rsi + 0x10]
  (0x30036, .vshufps 4 8 (.x 9) 136, 0x3003C),  -- c4 c1 38 c6 e1 88          vshufps xmm4, xmm8, xmm9, 0x88
  (0x3003C, .vshufps 5 8 (.x 9) 221, 0x30042),  -- c4 c1 38 c6 e9 dd          vshufps xmm5, xmm8, xmm9, 0xdd
  (0x30042, .movv false 8 (.m .rsi 0x20), 0x30047),  -- c5 78 10 46 20             vmovups xmm8, xmmword ptr [rsi + 0x20]
  (0x30047, .movv false 9 (.m .rsi 0x30), 0x3004C),  -- c5 78 10 4e 30             vmovups xmm9, xmmword ptr [rsi + 0x30]
  (0x3004C, .vshufps 6 8 (.x 9) 136, 0x30052),  -- c4 c1 38 c6 f1 88          vshufps xmm6, xmm8, xmm9, 0x88
  (0x30052, .vshufps 7 8 (.x 9) 221, 0x30058),  -- c4 c1 38 c6 f9 dd          vshufps xmm7, xmm8, xmm9, 0xdd
  (0x30058, .pshufd 6 (.x 6) 147, 0x3005D),  -- c5 f9 70 f6 93             vpshufd xmm6, xmm6, 0x93
  (0x3005D, .pshufd 7 (.x 7) 147, 0x30062),  -- c5 f9 70 ff 93             vpshufd xmm7, xmm7, 0x93
  (0x30062, .mov 8 (.reg .rax) (.imm 0x7), 0x30064),  -- b0 07                      mov al, 0x7
  (0x30064, .vpaddd 0 0 (.x 4), 0x30068),  -- c5 f9 fe c4                vpaddd xmm0, xmm0, xmm4
  (0x30068, .vpaddd 0 0 (.x 1), 0x3006C),  -- c5 f9 fe c1                vpaddd xmm0, xmm0, xmm1
  (0x3006C, .vpxor 3 3 (.x 0), 0x30072),  -- 62 f1 65 08 ef d8          vpxord xmm3, xmm3, xmm0
  (0x30072, .vprord 3 (.x 3) 16, 0x30079),  -- 62 f1 65 08 72 c3 10       vprord xmm3, xmm3, 0x10
  (0x30079, .vpaddd 2 2 (.x 3), 0x3007D),  -- c5 e9 fe d3                vpaddd xmm2, xmm2, xmm3
  (0x3007D, .vpxor 1 1 (.x 2), 0x30083),  -- 62 f1 75 08 ef ca          vpxord xmm1, xmm1, xmm2
  (0x30083, .vprord 1 (.x 1) 12, 0x3008A),  -- 62 f1 75 08 72 c1 0c       vprord xmm1, xmm1, 0xc
  (0x3008A, .vpaddd 0 0 (.x 5), 0x3008E),  -- c5 f9 fe c5                vpaddd xmm0, xmm0, xmm5
  (0x3008E, .vpaddd 0 0 (.x 1), 0x30092),  -- c5 f9 fe c1                vpaddd xmm0, xmm0, xmm1
  (0x30092, .vpxor 3 3 (.x 0), 0x30098),  -- 62 f1 65 08 ef d8          vpxord xmm3, xmm3, xmm0
  (0x30098, .vprord 3 (.x 3) 8, 0x3009F),  -- 62 f1 65 08 72 c3 08       vprord xmm3, xmm3, 0x8
  (0x3009F, .vpaddd 2 2 (.x 3), 0x300A3),  -- c5 e9 fe d3                vpaddd xmm2, xmm2, xmm3
  (0x300A3, .vpxor 1 1 (.x 2), 0x300A9),  -- 62 f1 75 08 ef ca          vpxord xmm1, xmm1, xmm2
  (0x300A9, .vprord 1 (.x 1) 7, 0x300B0),  -- 62 f1 75 08 72 c1 07       vprord xmm1, xmm1, 0x7
  (0x300B0, .pshufd 0 (.x 0) 147, 0x300B5),  -- c5 f9 70 c0 93             vpshufd xmm0, xmm0, 0x93
  (0x300B5, .pshufd 3 (.x 3) 78, 0x300BA),  -- c5 f9 70 db 4e             vpshufd xmm3, xmm3, 0x4e
  (0x300BA, .pshufd 2 (.x 2) 57, 0x300BF),  -- c5 f9 70 d2 39             vpshufd xmm2, xmm2, 0x39
  (0x300BF, .vpaddd 0 0 (.x 6), 0x300C3),  -- c5 f9 fe c6                vpaddd xmm0, xmm0, xmm6
  (0x300C3, .vpaddd 0 0 (.x 1), 0x300C7),  -- c5 f9 fe c1                vpaddd xmm0, xmm0, xmm1
  (0x300C7, .vpxor 3 3 (.x 0), 0x300CD),  -- 62 f1 65 08 ef d8          vpxord xmm3, xmm3, xmm0
  (0x300CD, .vprord 3 (.x 3) 16, 0x300D4),  -- 62 f1 65 08 72 c3 10       vprord xmm3, xmm3, 0x10
  (0x300D4, .vpaddd 2 2 (.x 3), 0x300D8),  -- c5 e9 fe d3                vpaddd xmm2, xmm2, xmm3
  (0x300D8, .vpxor 1 1 (.x 2), 0x300DE),  -- 62 f1 75 08 ef ca          vpxord xmm1, xmm1, xmm2
  (0x300DE, .vprord 1 (.x 1) 12, 0x300E5),  -- 62 f1 75 08 72 c1 0c       vprord xmm1, xmm1, 0xc
  (0x300E5, .vpaddd 0 0 (.x 7), 0x300E9),  -- c5 f9 fe c7                vpaddd xmm0, xmm0, xmm7
  (0x300E9, .vpaddd 0 0 (.x 1), 0x300ED),  -- c5 f9 fe c1                vpaddd xmm0, xmm0, xmm1
  (0x300ED, .vpxor 3 3 (.x 0), 0x300F3),  -- 62 f1 65 08 ef d8          vpxord xmm3, xmm3, xmm0
  (0x300F3, .vprord 3 (.x 3) 8, 0x300FA),  -- 62 f1 65 08 72 c3 08       vprord xmm3, xmm3, 0x8
  (0x300FA, .vpaddd 2 2 (.x 3), 0x300FE),  -- c5 e9 fe d3                vpaddd xmm2, xmm2, xmm3
  (0x300FE, .vpxor 1 1 (.x 2), 0x30104),  -- 62 f1 75 08 ef ca          vpxord xmm1, xmm1, xmm2
  (0x30104, .vprord 1 (.x 1) 7, 0x3010B),  -- 62 f1 75 08 72 c1 07       vprord xmm1, xmm1, 0x7
  (0x3010B, .pshufd 0 (.x 0) 57, 0x30110),  -- c5 f9 70 c0 39             vpshufd xmm0, xmm0, 0x39
  (0x30110, .pshufd 3 (.x 3) 78, 0x30115),  -- c5 f9 70 db 4e             vpshufd xmm3, xmm3, 0x4e
  (0x30115, .pshufd 2 (.x 2) 147, 0x3011A),  -- c5 f9 70 d2 93             vpshufd xmm2, xmm2, 0x93
  (0x3011A, .decb .rax, 0x3011C),  -- fe c8                      dec al
  (0x3011C, .je 0x30163, 0x3011E),  -- 74 45                      je 0x3863 <blake3_servil_compress_in_place_avx512+0x163>
  (0x3011E, .vshufps 8 4 (.x 5) 214, 0x30123),  -- c5 58 c6 c5 d6             vshufps xmm8, xmm4, xmm5, 0xd6
  (0x30123, .pshufd 9 (.x 4) 15, 0x30128),  -- c5 79 70 cc 0f             vpshufd xmm9, xmm4, 0xf
  (0x30128, .pshufd 4 (.x 8) 57, 0x3012E),  -- c4 c1 79 70 e0 39          vpshufd xmm4, xmm8, 0x39
  (0x3012E, .vshufps 8 6 (.x 7) 250, 0x30133),  -- c5 48 c6 c7 fa             vshufps xmm8, xmm6, xmm7, 0xfa
  (0x30133, .vpblendd 9 9 (.x 8) 170, 0x30139),  -- c4 43 31 02 c8 aa          vpblendd xmm9, xmm9, xmm8, 0xaa
  (0x30139, .vpunpcklqdq 8 7 (.x 5), 0x3013D),  -- c5 41 6c c5                vpunpcklqdq xmm8, xmm7, xmm5
  (0x3013D, .vpblendd 8 8 (.x 6) 136, 0x30143),  -- c4 63 39 02 c6 88          vpblendd xmm8, xmm8, xmm6, 0x88
  (0x30143, .pshufd 8 (.x 8) 120, 0x30149),  -- c4 41 79 70 c0 78          vpshufd xmm8, xmm8, 0x78
  (0x30149, .vpunpckhdq 5 5 (.x 7), 0x3014D),  -- c5 d1 6a ef                vpunpckhdq xmm5, xmm5, xmm7
  (0x3014D, .vpunpckldq 6 6 (.x 5), 0x30151),  -- c5 c9 62 f5                vpunpckldq xmm6, xmm6, xmm5
  (0x30151, .pshufd 7 (.x 6) 30, 0x30156),  -- c5 f9 70 fe 1e             vpshufd xmm7, xmm6, 0x1e
  (0x30156, .movv false 5 (.x 9), 0x3015A),  -- c5 79 7f cd                vmovdqa xmm5, xmm9
  (0x3015A, .movv false 6 (.x 8), 0x3015E),  -- c5 79 7f c6                vmovdqa xmm6, xmm8
  (0x3015E, .jmp 0x30064, 0x30163),  -- e9 01 ff ff ff             jmp 0x3764 <blake3_servil_compress_in_place_avx512+0x64>
  (0x30163, .vpxor 0 0 (.x 2), 0x30167),  -- c5 f9 ef c2                vpxor xmm0, xmm0, xmm2
  (0x30167, .vpxor 1 1 (.x 3), 0x3016B),  -- c5 f1 ef cb                vpxor xmm1, xmm1, xmm3
  (0x3016B, .storev false .rdi 0x0 0, 0x3016F),  -- c5 fa 7f 07                vmovdqu xmmword ptr [rdi], xmm0
  (0x3016F, .storev false .rdi 0x10 1, 0x30174),  -- c5 fa 7f 4f 10             vmovdqu xmmword ptr [rdi + 0x10], xmm1
  (0x30174, .ret, 0x30175)  -- c3                         ret 
]

end Avx
