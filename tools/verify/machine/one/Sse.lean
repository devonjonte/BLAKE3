import Machine

/-! `blake3_servil_compress_in_place_sse41`, as llvm-objdump reads it, placed at 0x20000. Written by lift_one.py. -/

set_option maxRecDepth 100000
namespace Sse
open X86

def entry : Nat := 0x20000

def table : List (Nat × Instr × Nat) := [
  (0x20000, .movv false 0 (.m .rdi 0x0), 0x20003),  -- 0f 10 07                   movups xmm0, xmmword ptr [rdi]
  (0x20003, .movv false 1 (.m .rdi 0x10), 0x20007),  -- 0f 10 4f 10                movups xmm1, xmmword ptr [rdi + 0x10]
  (0x20007, .movv false 2 (.c 0xA54FF53A3C6EF372BB67AE856A09E667#128), 0x2000E),  -- 0f 28 15 00 00 00 00       movaps xmm2, xmmword ptr [rip]
  (0x2000E, .shl64 .r8 32, 0x20012),  -- 49 c1 e0 20                shl r8, 0x20
  (0x20012, .add 64 (.reg .rdx) (.reg .r8), 0x20015),  -- 4c 01 c2                   add rdx, r8
  (0x20015, .movq 3 .rcx, 0x2001A),  -- 66 48 0f 6e d9             movq xmm3, rcx
  (0x2001A, .movq 4 .rdx, 0x2001F),  -- 66 48 0f 6e e2             movq xmm4, rdx
  (0x2001F, .punpcklqdq 3 (.x 4), 0x20023),  -- 66 0f 6c dc                punpcklqdq xmm3, xmm4
  (0x20023, .movv false 4 (.m .rsi 0x0), 0x20026),  -- 0f 10 26                   movups xmm4, xmmword ptr [rsi]
  (0x20026, .movv false 5 (.m .rsi 0x10), 0x2002A),  -- 0f 10 6e 10                movups xmm5, xmmword ptr [rsi + 0x10]
  (0x2002A, .movv false 8 (.x 4), 0x2002E),  -- 44 0f 28 c4                movaps xmm8, xmm4
  (0x2002E, .shufps 4 (.x 5) 136, 0x20032),  -- 0f c6 e5 88                shufps xmm4, xmm5, 0x88
  (0x20032, .shufps 8 (.x 5) 221, 0x20037),  -- 44 0f c6 c5 dd             shufps xmm8, xmm5, 0xdd
  (0x20037, .movv false 5 (.x 8), 0x2003B),  -- 41 0f 28 e8                movaps xmm5, xmm8
  (0x2003B, .movv false 6 (.m .rsi 0x20), 0x2003F),  -- 0f 10 76 20                movups xmm6, xmmword ptr [rsi + 0x20]
  (0x2003F, .movv false 7 (.m .rsi 0x30), 0x20043),  -- 0f 10 7e 30                movups xmm7, xmmword ptr [rsi + 0x30]
  (0x20043, .movv false 8 (.x 6), 0x20047),  -- 44 0f 28 c6                movaps xmm8, xmm6
  (0x20047, .shufps 6 (.x 7) 136, 0x2004B),  -- 0f c6 f7 88                shufps xmm6, xmm7, 0x88
  (0x2004B, .pshufd 6 (.x 6) 147, 0x20050),  -- 66 0f 70 f6 93             pshufd xmm6, xmm6, 0x93
  (0x20050, .shufps 8 (.x 7) 221, 0x20055),  -- 44 0f c6 c7 dd             shufps xmm8, xmm7, 0xdd
  (0x20055, .pshufd 7 (.x 8) 147, 0x2005B),  -- 66 41 0f 70 f8 93          pshufd xmm7, xmm8, 0x93
  (0x2005B, .movv false 14 (.c 0x0C0F0E0D080B0A090407060500030201#128), 0x20063),  -- 44 0f 28 35 00 00 00 00    movaps xmm14, xmmword ptr [rip]
  (0x20063, .movv false 15 (.c 0x0D0C0F0E09080B0A0504070601000302#128), 0x2006B),  -- 44 0f 28 3d 00 00 00 00    movaps xmm15, xmmword ptr [rip]
  (0x2006B, .mov 8 (.reg .rax) (.imm 0x7), 0x2006D),  -- b0 07                      mov al, 0x7
  (0x2006D, .paddd 0 (.x 4), 0x20071),  -- 66 0f fe c4                paddd xmm0, xmm4
  (0x20071, .paddd 0 (.x 1), 0x20075),  -- 66 0f fe c1                paddd xmm0, xmm1
  (0x20075, .pxor 3 (.x 0), 0x20079),  -- 66 0f ef d8                pxor xmm3, xmm0
  (0x20079, .pshufb 3 (.x 15), 0x2007F),  -- 66 41 0f 38 00 df          pshufb xmm3, xmm15
  (0x2007F, .paddd 2 (.x 3), 0x20083),  -- 66 0f fe d3                paddd xmm2, xmm3
  (0x20083, .pxor 1 (.x 2), 0x20087),  -- 66 0f ef ca                pxor xmm1, xmm2
  (0x20087, .movv false 11 (.x 1), 0x2008C),  -- 66 44 0f 6f d9             movdqa xmm11, xmm1
  (0x2008C, .pslld 1 20, 0x20091),  -- 66 0f 72 f1 14             pslld xmm1, 0x14
  (0x20091, .psrld 11 12, 0x20097),  -- 66 41 0f 72 d3 0c          psrld xmm11, 0xc
  (0x20097, .por 1 (.x 11), 0x2009C),  -- 66 41 0f eb cb             por xmm1, xmm11
  (0x2009C, .paddd 0 (.x 5), 0x200A0),  -- 66 0f fe c5                paddd xmm0, xmm5
  (0x200A0, .paddd 0 (.x 1), 0x200A4),  -- 66 0f fe c1                paddd xmm0, xmm1
  (0x200A4, .pxor 3 (.x 0), 0x200A8),  -- 66 0f ef d8                pxor xmm3, xmm0
  (0x200A8, .pshufb 3 (.x 14), 0x200AE),  -- 66 41 0f 38 00 de          pshufb xmm3, xmm14
  (0x200AE, .paddd 2 (.x 3), 0x200B2),  -- 66 0f fe d3                paddd xmm2, xmm3
  (0x200B2, .pxor 1 (.x 2), 0x200B6),  -- 66 0f ef ca                pxor xmm1, xmm2
  (0x200B6, .movv false 11 (.x 1), 0x200BB),  -- 66 44 0f 6f d9             movdqa xmm11, xmm1
  (0x200BB, .pslld 1 25, 0x200C0),  -- 66 0f 72 f1 19             pslld xmm1, 0x19
  (0x200C0, .psrld 11 7, 0x200C6),  -- 66 41 0f 72 d3 07          psrld xmm11, 0x7
  (0x200C6, .por 1 (.x 11), 0x200CB),  -- 66 41 0f eb cb             por xmm1, xmm11
  (0x200CB, .pshufd 0 (.x 0) 147, 0x200D0),  -- 66 0f 70 c0 93             pshufd xmm0, xmm0, 0x93
  (0x200D0, .pshufd 3 (.x 3) 78, 0x200D5),  -- 66 0f 70 db 4e             pshufd xmm3, xmm3, 0x4e
  (0x200D5, .pshufd 2 (.x 2) 57, 0x200DA),  -- 66 0f 70 d2 39             pshufd xmm2, xmm2, 0x39
  (0x200DA, .paddd 0 (.x 6), 0x200DE),  -- 66 0f fe c6                paddd xmm0, xmm6
  (0x200DE, .paddd 0 (.x 1), 0x200E2),  -- 66 0f fe c1                paddd xmm0, xmm1
  (0x200E2, .pxor 3 (.x 0), 0x200E6),  -- 66 0f ef d8                pxor xmm3, xmm0
  (0x200E6, .pshufb 3 (.x 15), 0x200EC),  -- 66 41 0f 38 00 df          pshufb xmm3, xmm15
  (0x200EC, .paddd 2 (.x 3), 0x200F0),  -- 66 0f fe d3                paddd xmm2, xmm3
  (0x200F0, .pxor 1 (.x 2), 0x200F4),  -- 66 0f ef ca                pxor xmm1, xmm2
  (0x200F4, .movv false 11 (.x 1), 0x200F9),  -- 66 44 0f 6f d9             movdqa xmm11, xmm1
  (0x200F9, .pslld 1 20, 0x200FE),  -- 66 0f 72 f1 14             pslld xmm1, 0x14
  (0x200FE, .psrld 11 12, 0x20104),  -- 66 41 0f 72 d3 0c          psrld xmm11, 0xc
  (0x20104, .por 1 (.x 11), 0x20109),  -- 66 41 0f eb cb             por xmm1, xmm11
  (0x20109, .paddd 0 (.x 7), 0x2010D),  -- 66 0f fe c7                paddd xmm0, xmm7
  (0x2010D, .paddd 0 (.x 1), 0x20111),  -- 66 0f fe c1                paddd xmm0, xmm1
  (0x20111, .pxor 3 (.x 0), 0x20115),  -- 66 0f ef d8                pxor xmm3, xmm0
  (0x20115, .pshufb 3 (.x 14), 0x2011B),  -- 66 41 0f 38 00 de          pshufb xmm3, xmm14
  (0x2011B, .paddd 2 (.x 3), 0x2011F),  -- 66 0f fe d3                paddd xmm2, xmm3
  (0x2011F, .pxor 1 (.x 2), 0x20123),  -- 66 0f ef ca                pxor xmm1, xmm2
  (0x20123, .movv false 11 (.x 1), 0x20128),  -- 66 44 0f 6f d9             movdqa xmm11, xmm1
  (0x20128, .pslld 1 25, 0x2012D),  -- 66 0f 72 f1 19             pslld xmm1, 0x19
  (0x2012D, .psrld 11 7, 0x20133),  -- 66 41 0f 72 d3 07          psrld xmm11, 0x7
  (0x20133, .por 1 (.x 11), 0x20138),  -- 66 41 0f eb cb             por xmm1, xmm11
  (0x20138, .pshufd 0 (.x 0) 57, 0x2013D),  -- 66 0f 70 c0 39             pshufd xmm0, xmm0, 0x39
  (0x2013D, .pshufd 3 (.x 3) 78, 0x20142),  -- 66 0f 70 db 4e             pshufd xmm3, xmm3, 0x4e
  (0x20142, .pshufd 2 (.x 2) 147, 0x20147),  -- 66 0f 70 d2 93             pshufd xmm2, xmm2, 0x93
  (0x20147, .decb .rax, 0x20149),  -- fe c8                      dec al
  (0x20149, .je 0x201A5, 0x2014B),  -- 74 5a                      je 0x2765 <blake3_servil_compress_in_place_sse41+0x1a5>
  (0x2014B, .movv false 8 (.x 4), 0x20150),  -- 66 44 0f 6f c4             movdqa xmm8, xmm4
  (0x20150, .shufps 8 (.x 5) 214, 0x20155),  -- 44 0f c6 c5 d6             shufps xmm8, xmm5, 0xd6
  (0x20155, .pshufd 9 (.x 4) 15, 0x2015B),  -- 66 44 0f 70 cc 0f          pshufd xmm9, xmm4, 0xf
  (0x2015B, .pshufd 4 (.x 8) 57, 0x20161),  -- 66 41 0f 70 e0 39          pshufd xmm4, xmm8, 0x39
  (0x20161, .movv false 8 (.x 6), 0x20166),  -- 66 44 0f 6f c6             movdqa xmm8, xmm6
  (0x20166, .shufps 8 (.x 7) 250, 0x2016B),  -- 44 0f c6 c7 fa             shufps xmm8, xmm7, 0xfa
  (0x2016B, .pblendw 9 (.x 8) 204, 0x20172),  -- 66 45 0f 3a 0e c8 cc       pblendw xmm9, xmm8, 0xcc
  (0x20172, .movv false 8 (.x 7), 0x20177),  -- 66 44 0f 6f c7             movdqa xmm8, xmm7
  (0x20177, .punpcklqdq 8 (.x 5), 0x2017C),  -- 66 44 0f 6c c5             punpcklqdq xmm8, xmm5
  (0x2017C, .pblendw 8 (.x 6) 192, 0x20183),  -- 66 44 0f 3a 0e c6 c0       pblendw xmm8, xmm6, 0xc0
  (0x20183, .pshufd 8 (.x 8) 120, 0x20189),  -- 66 45 0f 70 c0 78          pshufd xmm8, xmm8, 0x78
  (0x20189, .punpckhdq 5 (.x 7), 0x2018D),  -- 66 0f 6a ef                punpckhdq xmm5, xmm7
  (0x2018D, .punpckldq 6 (.x 5), 0x20191),  -- 66 0f 62 f5                punpckldq xmm6, xmm5
  (0x20191, .pshufd 7 (.x 6) 30, 0x20196),  -- 66 0f 70 fe 1e             pshufd xmm7, xmm6, 0x1e
  (0x20196, .movv false 5 (.x 9), 0x2019B),  -- 66 41 0f 6f e9             movdqa xmm5, xmm9
  (0x2019B, .movv false 6 (.x 8), 0x201A0),  -- 66 41 0f 6f f0             movdqa xmm6, xmm8
  (0x201A0, .jmp 0x2006D, 0x201A5),  -- e9 c8 fe ff ff             jmp 0x262d <blake3_servil_compress_in_place_sse41+0x6d>
  (0x201A5, .pxor 0 (.x 2), 0x201A9),  -- 66 0f ef c2                pxor xmm0, xmm2
  (0x201A9, .pxor 1 (.x 3), 0x201AD),  -- 66 0f ef cb                pxor xmm1, xmm3
  (0x201AD, .storev false .rdi 0x0 0, 0x201B0),  -- 0f 11 07                   movups xmmword ptr [rdi], xmm0
  (0x201B0, .storev false .rdi 0x10 1, 0x201B4),  -- 0f 11 4f 10                movups xmmword ptr [rdi + 0x10], xmm1
  (0x201B4, .ret, 0x201B5)  -- c3                         ret 
]

end Sse
