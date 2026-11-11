import Machine

/-! `b3l_hex`, as llvm-objdump reads it, placed at 0x50000. Written by lift_one.py. -/

set_option maxRecDepth 100000
namespace Lifted_hex
open X86

def entry : Nat := 0x50000

def table : List (Nat × Instr × Nat) := [
  (0x50000, .movv false 0 (.m .rsi 0x0), 0x50004),  -- f3 0f 6f 06                movdqu xmm0, xmmword ptr [rsi]
  (0x50004, .movv false 1 (.m .rsi 0x10), 0x50009),  -- f3 0f 6f 4e 10             movdqu xmm1, xmmword ptr [rsi + 0x10]
  (0x50009, .movv false 5 (.c 0x0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F#128), 0x50011),  -- 66 0f 6f 2d 00 00 00 00    movdqa xmm5, xmmword ptr [rip]
  (0x50011, .movv false 6 (.c 0x09090909090909090909090909090909#128), 0x50019),  -- 66 0f 6f 35 00 00 00 00    movdqa xmm6, xmmword ptr [rip]
  (0x50019, .movv false 7 (.c 0x27272727272727272727272727272727#128), 0x50021),  -- 66 0f 6f 3d 00 00 00 00    movdqa xmm7, xmmword ptr [rip]
  (0x50021, .movv false 8 (.c 0x30303030303030303030303030303030#128), 0x5002A),  -- 66 44 0f 6f 05 00 00 00 00 movdqa xmm8, xmmword ptr [rip]
  (0x5002A, .movv false 2 (.x 0), 0x5002E),  -- 66 0f 6f d0                movdqa xmm2, xmm0
  (0x5002E, .psrlw 2 4, 0x50033),  -- 66 0f 71 d2 04             psrlw xmm2, 0x4
  (0x50033, .pand 2 (.x 5), 0x50037),  -- 66 0f db d5                pand xmm2, xmm5
  (0x50037, .pand 0 (.x 5), 0x5003B),  -- 66 0f db c5                pand xmm0, xmm5
  (0x5003B, .movv false 3 (.x 2), 0x5003F),  -- 66 0f 6f da                movdqa xmm3, xmm2
  (0x5003F, .punpcklbw 3 (.x 0), 0x50043),  -- 66 0f 60 d8                punpcklbw xmm3, xmm0
  (0x50043, .punpckhbw 2 (.x 0), 0x50047),  -- 66 0f 68 d0                punpckhbw xmm2, xmm0
  (0x50047, .movv false 4 (.x 3), 0x5004B),  -- 66 0f 6f e3                movdqa xmm4, xmm3
  (0x5004B, .pcmpgtb 4 (.x 6), 0x5004F),  -- 66 0f 64 e6                pcmpgtb xmm4, xmm6
  (0x5004F, .pand 4 (.x 7), 0x50053),  -- 66 0f db e7                pand xmm4, xmm7
  (0x50053, .paddb 3 (.x 4), 0x50057),  -- 66 0f fc dc                paddb xmm3, xmm4
  (0x50057, .paddb 3 (.x 8), 0x5005C),  -- 66 41 0f fc d8             paddb xmm3, xmm8
  (0x5005C, .movv false 4 (.x 2), 0x50060),  -- 66 0f 6f e2                movdqa xmm4, xmm2
  (0x50060, .pcmpgtb 4 (.x 6), 0x50064),  -- 66 0f 64 e6                pcmpgtb xmm4, xmm6
  (0x50064, .pand 4 (.x 7), 0x50068),  -- 66 0f db e7                pand xmm4, xmm7
  (0x50068, .paddb 2 (.x 4), 0x5006C),  -- 66 0f fc d4                paddb xmm2, xmm4
  (0x5006C, .paddb 2 (.x 8), 0x50071),  -- 66 41 0f fc d0             paddb xmm2, xmm8
  (0x50071, .storev false .rdi 0x0 3, 0x50075),  -- f3 0f 7f 1f                movdqu xmmword ptr [rdi], xmm3
  (0x50075, .storev false .rdi 0x10 2, 0x5007A),  -- f3 0f 7f 57 10             movdqu xmmword ptr [rdi + 0x10], xmm2
  (0x5007A, .movv false 2 (.x 1), 0x5007E),  -- 66 0f 6f d1                movdqa xmm2, xmm1
  (0x5007E, .psrlw 2 4, 0x50083),  -- 66 0f 71 d2 04             psrlw xmm2, 0x4
  (0x50083, .pand 2 (.x 5), 0x50087),  -- 66 0f db d5                pand xmm2, xmm5
  (0x50087, .pand 1 (.x 5), 0x5008B),  -- 66 0f db cd                pand xmm1, xmm5
  (0x5008B, .movv false 3 (.x 2), 0x5008F),  -- 66 0f 6f da                movdqa xmm3, xmm2
  (0x5008F, .punpcklbw 3 (.x 1), 0x50093),  -- 66 0f 60 d9                punpcklbw xmm3, xmm1
  (0x50093, .punpckhbw 2 (.x 1), 0x50097),  -- 66 0f 68 d1                punpckhbw xmm2, xmm1
  (0x50097, .movv false 4 (.x 3), 0x5009B),  -- 66 0f 6f e3                movdqa xmm4, xmm3
  (0x5009B, .pcmpgtb 4 (.x 6), 0x5009F),  -- 66 0f 64 e6                pcmpgtb xmm4, xmm6
  (0x5009F, .pand 4 (.x 7), 0x500A3),  -- 66 0f db e7                pand xmm4, xmm7
  (0x500A3, .paddb 3 (.x 4), 0x500A7),  -- 66 0f fc dc                paddb xmm3, xmm4
  (0x500A7, .paddb 3 (.x 8), 0x500AC),  -- 66 41 0f fc d8             paddb xmm3, xmm8
  (0x500AC, .movv false 4 (.x 2), 0x500B0),  -- 66 0f 6f e2                movdqa xmm4, xmm2
  (0x500B0, .pcmpgtb 4 (.x 6), 0x500B4),  -- 66 0f 64 e6                pcmpgtb xmm4, xmm6
  (0x500B4, .pand 4 (.x 7), 0x500B8),  -- 66 0f db e7                pand xmm4, xmm7
  (0x500B8, .paddb 2 (.x 4), 0x500BC),  -- 66 0f fc d4                paddb xmm2, xmm4
  (0x500BC, .paddb 2 (.x 8), 0x500C1),  -- 66 41 0f fc d0             paddb xmm2, xmm8
  (0x500C1, .storev false .rdi 0x20 3, 0x500C6),  -- f3 0f 7f 5f 20             movdqu xmmword ptr [rdi + 0x20], xmm3
  (0x500C6, .storev false .rdi 0x30 2, 0x500CB),  -- f3 0f 7f 57 30             movdqu xmmword ptr [rdi + 0x30], xmm2
  (0x500CB, .ret, 0x500CC)  -- c3                         ret 
]

end Lifted_hex
