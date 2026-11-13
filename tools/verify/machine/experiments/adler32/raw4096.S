// Printed by odec.py from raw4096.ode. Not written or edited by hand.
#if defined(__ELF__) && defined(__linux__)
.section .note.GNU-stack,"",%progbits
#endif
#ifdef __APPLE__
#define CALL(f) _##f
#else
#define CALL(f) f@PLT
#endif
.intel_syntax noprefix
#ifdef __APPLE__
.static_data
#else
.section .rodata
#endif
.p2align 6
.Lode_data_weights4096:
    .long 1027489600
    .long 960117564
    .long 892745528
    .long 825373492
    .long 758001456
    .long 690629420
    .long 623257384
    .long 555885348
    .long 488513312
    .long 421141276
    .long 353769240
    .long 286397204
    .long 219025168
    .long 151653132
    .long 84281096
    .long 16909060
.p2align 6
.Lode_data_ones4096:
    .long 16843009
    .long 16843009
    .long 16843009
    .long 16843009
    .long 16843009
    .long 16843009
    .long 16843009
    .long 16843009
    .long 16843009
    .long 16843009
    .long 16843009
    .long 16843009
    .long 16843009
    .long 16843009
    .long 16843009
    .long 16843009
.text
.text
.global b3l_raw4096
.global _b3l_raw4096
.p2align 4
b3l_raw4096:
_b3l_raw4096:
    vpxord zmm0, zmm0, zmm0
    vpxord zmm1, zmm1, zmm1
    vpxord zmm2, zmm2, zmm2
    vpxord zmm3, zmm3, zmm3
    vpxord zmm4, zmm4, zmm4
    vpxord zmm5, zmm5, zmm5
    vpxord zmm6, zmm6, zmm6
    vpxord zmm7, zmm7, zmm7
    vpxord zmm8, zmm8, zmm8
    vpxord zmm9, zmm9, zmm9
    vpxord zmm10, zmm10, zmm10
    vpxord zmm11, zmm11, zmm11
    vmovdqa64 zmm12, zmmword ptr [rip + .Lode_data_weights4096]
    vmovdqa64 zmm13, zmmword ptr [rip + .Lode_data_ones4096]
    vpaddd zmm8, zmm8, zmm0
    vmovdqu64 zmm14, zmmword ptr [rdi + 0*256]
    vpdpbusd zmm4, zmm14, zmm12
    vpdpbusd zmm0, zmm14, zmm13
    vpaddd zmm9, zmm9, zmm1
    vmovdqu64 zmm14, zmmword ptr [rdi + 0*256 + 64]
    vpdpbusd zmm5, zmm14, zmm12
    vpdpbusd zmm1, zmm14, zmm13
    vpaddd zmm10, zmm10, zmm2
    vmovdqu64 zmm14, zmmword ptr [rdi + 0*256 + 128]
    vpdpbusd zmm6, zmm14, zmm12
    vpdpbusd zmm2, zmm14, zmm13
    vpaddd zmm11, zmm11, zmm3
    vmovdqu64 zmm14, zmmword ptr [rdi + 0*256 + 192]
    vpdpbusd zmm7, zmm14, zmm12
    vpdpbusd zmm3, zmm14, zmm13
    vpaddd zmm8, zmm8, zmm0
    vmovdqu64 zmm14, zmmword ptr [rdi + 1*256]
    vpdpbusd zmm4, zmm14, zmm12
    vpdpbusd zmm0, zmm14, zmm13
    vpaddd zmm9, zmm9, zmm1
    vmovdqu64 zmm14, zmmword ptr [rdi + 1*256 + 64]
    vpdpbusd zmm5, zmm14, zmm12
    vpdpbusd zmm1, zmm14, zmm13
    vpaddd zmm10, zmm10, zmm2
    vmovdqu64 zmm14, zmmword ptr [rdi + 1*256 + 128]
    vpdpbusd zmm6, zmm14, zmm12
    vpdpbusd zmm2, zmm14, zmm13
    vpaddd zmm11, zmm11, zmm3
    vmovdqu64 zmm14, zmmword ptr [rdi + 1*256 + 192]
    vpdpbusd zmm7, zmm14, zmm12
    vpdpbusd zmm3, zmm14, zmm13
    vpaddd zmm8, zmm8, zmm0
    vmovdqu64 zmm14, zmmword ptr [rdi + 2*256]
    vpdpbusd zmm4, zmm14, zmm12
    vpdpbusd zmm0, zmm14, zmm13
    vpaddd zmm9, zmm9, zmm1
    vmovdqu64 zmm14, zmmword ptr [rdi + 2*256 + 64]
    vpdpbusd zmm5, zmm14, zmm12
    vpdpbusd zmm1, zmm14, zmm13
    vpaddd zmm10, zmm10, zmm2
    vmovdqu64 zmm14, zmmword ptr [rdi + 2*256 + 128]
    vpdpbusd zmm6, zmm14, zmm12
    vpdpbusd zmm2, zmm14, zmm13
    vpaddd zmm11, zmm11, zmm3
    vmovdqu64 zmm14, zmmword ptr [rdi + 2*256 + 192]
    vpdpbusd zmm7, zmm14, zmm12
    vpdpbusd zmm3, zmm14, zmm13
    vpaddd zmm8, zmm8, zmm0
    vmovdqu64 zmm14, zmmword ptr [rdi + 3*256]
    vpdpbusd zmm4, zmm14, zmm12
    vpdpbusd zmm0, zmm14, zmm13
    vpaddd zmm9, zmm9, zmm1
    vmovdqu64 zmm14, zmmword ptr [rdi + 3*256 + 64]
    vpdpbusd zmm5, zmm14, zmm12
    vpdpbusd zmm1, zmm14, zmm13
    vpaddd zmm10, zmm10, zmm2
    vmovdqu64 zmm14, zmmword ptr [rdi + 3*256 + 128]
    vpdpbusd zmm6, zmm14, zmm12
    vpdpbusd zmm2, zmm14, zmm13
    vpaddd zmm11, zmm11, zmm3
    vmovdqu64 zmm14, zmmword ptr [rdi + 3*256 + 192]
    vpdpbusd zmm7, zmm14, zmm12
    vpdpbusd zmm3, zmm14, zmm13
    vpaddd zmm8, zmm8, zmm0
    vmovdqu64 zmm14, zmmword ptr [rdi + 4*256]
    vpdpbusd zmm4, zmm14, zmm12
    vpdpbusd zmm0, zmm14, zmm13
    vpaddd zmm9, zmm9, zmm1
    vmovdqu64 zmm14, zmmword ptr [rdi + 4*256 + 64]
    vpdpbusd zmm5, zmm14, zmm12
    vpdpbusd zmm1, zmm14, zmm13
    vpaddd zmm10, zmm10, zmm2
    vmovdqu64 zmm14, zmmword ptr [rdi + 4*256 + 128]
    vpdpbusd zmm6, zmm14, zmm12
    vpdpbusd zmm2, zmm14, zmm13
    vpaddd zmm11, zmm11, zmm3
    vmovdqu64 zmm14, zmmword ptr [rdi + 4*256 + 192]
    vpdpbusd zmm7, zmm14, zmm12
    vpdpbusd zmm3, zmm14, zmm13
    vpaddd zmm8, zmm8, zmm0
    vmovdqu64 zmm14, zmmword ptr [rdi + 5*256]
    vpdpbusd zmm4, zmm14, zmm12
    vpdpbusd zmm0, zmm14, zmm13
    vpaddd zmm9, zmm9, zmm1
    vmovdqu64 zmm14, zmmword ptr [rdi + 5*256 + 64]
    vpdpbusd zmm5, zmm14, zmm12
    vpdpbusd zmm1, zmm14, zmm13
    vpaddd zmm10, zmm10, zmm2
    vmovdqu64 zmm14, zmmword ptr [rdi + 5*256 + 128]
    vpdpbusd zmm6, zmm14, zmm12
    vpdpbusd zmm2, zmm14, zmm13
    vpaddd zmm11, zmm11, zmm3
    vmovdqu64 zmm14, zmmword ptr [rdi + 5*256 + 192]
    vpdpbusd zmm7, zmm14, zmm12
    vpdpbusd zmm3, zmm14, zmm13
    vpaddd zmm8, zmm8, zmm0
    vmovdqu64 zmm14, zmmword ptr [rdi + 6*256]
    vpdpbusd zmm4, zmm14, zmm12
    vpdpbusd zmm0, zmm14, zmm13
    vpaddd zmm9, zmm9, zmm1
    vmovdqu64 zmm14, zmmword ptr [rdi + 6*256 + 64]
    vpdpbusd zmm5, zmm14, zmm12
    vpdpbusd zmm1, zmm14, zmm13
    vpaddd zmm10, zmm10, zmm2
    vmovdqu64 zmm14, zmmword ptr [rdi + 6*256 + 128]
    vpdpbusd zmm6, zmm14, zmm12
    vpdpbusd zmm2, zmm14, zmm13
    vpaddd zmm11, zmm11, zmm3
    vmovdqu64 zmm14, zmmword ptr [rdi + 6*256 + 192]
    vpdpbusd zmm7, zmm14, zmm12
    vpdpbusd zmm3, zmm14, zmm13
    vpaddd zmm8, zmm8, zmm0
    vmovdqu64 zmm14, zmmword ptr [rdi + 7*256]
    vpdpbusd zmm4, zmm14, zmm12
    vpdpbusd zmm0, zmm14, zmm13
    vpaddd zmm9, zmm9, zmm1
    vmovdqu64 zmm14, zmmword ptr [rdi + 7*256 + 64]
    vpdpbusd zmm5, zmm14, zmm12
    vpdpbusd zmm1, zmm14, zmm13
    vpaddd zmm10, zmm10, zmm2
    vmovdqu64 zmm14, zmmword ptr [rdi + 7*256 + 128]
    vpdpbusd zmm6, zmm14, zmm12
    vpdpbusd zmm2, zmm14, zmm13
    vpaddd zmm11, zmm11, zmm3
    vmovdqu64 zmm14, zmmword ptr [rdi + 7*256 + 192]
    vpdpbusd zmm7, zmm14, zmm12
    vpdpbusd zmm3, zmm14, zmm13
    vpaddd zmm8, zmm8, zmm0
    vmovdqu64 zmm14, zmmword ptr [rdi + 8*256]
    vpdpbusd zmm4, zmm14, zmm12
    vpdpbusd zmm0, zmm14, zmm13
    vpaddd zmm9, zmm9, zmm1
    vmovdqu64 zmm14, zmmword ptr [rdi + 8*256 + 64]
    vpdpbusd zmm5, zmm14, zmm12
    vpdpbusd zmm1, zmm14, zmm13
    vpaddd zmm10, zmm10, zmm2
    vmovdqu64 zmm14, zmmword ptr [rdi + 8*256 + 128]
    vpdpbusd zmm6, zmm14, zmm12
    vpdpbusd zmm2, zmm14, zmm13
    vpaddd zmm11, zmm11, zmm3
    vmovdqu64 zmm14, zmmword ptr [rdi + 8*256 + 192]
    vpdpbusd zmm7, zmm14, zmm12
    vpdpbusd zmm3, zmm14, zmm13
    vpaddd zmm8, zmm8, zmm0
    vmovdqu64 zmm14, zmmword ptr [rdi + 9*256]
    vpdpbusd zmm4, zmm14, zmm12
    vpdpbusd zmm0, zmm14, zmm13
    vpaddd zmm9, zmm9, zmm1
    vmovdqu64 zmm14, zmmword ptr [rdi + 9*256 + 64]
    vpdpbusd zmm5, zmm14, zmm12
    vpdpbusd zmm1, zmm14, zmm13
    vpaddd zmm10, zmm10, zmm2
    vmovdqu64 zmm14, zmmword ptr [rdi + 9*256 + 128]
    vpdpbusd zmm6, zmm14, zmm12
    vpdpbusd zmm2, zmm14, zmm13
    vpaddd zmm11, zmm11, zmm3
    vmovdqu64 zmm14, zmmword ptr [rdi + 9*256 + 192]
    vpdpbusd zmm7, zmm14, zmm12
    vpdpbusd zmm3, zmm14, zmm13
    vpaddd zmm8, zmm8, zmm0
    vmovdqu64 zmm14, zmmword ptr [rdi + 10*256]
    vpdpbusd zmm4, zmm14, zmm12
    vpdpbusd zmm0, zmm14, zmm13
    vpaddd zmm9, zmm9, zmm1
    vmovdqu64 zmm14, zmmword ptr [rdi + 10*256 + 64]
    vpdpbusd zmm5, zmm14, zmm12
    vpdpbusd zmm1, zmm14, zmm13
    vpaddd zmm10, zmm10, zmm2
    vmovdqu64 zmm14, zmmword ptr [rdi + 10*256 + 128]
    vpdpbusd zmm6, zmm14, zmm12
    vpdpbusd zmm2, zmm14, zmm13
    vpaddd zmm11, zmm11, zmm3
    vmovdqu64 zmm14, zmmword ptr [rdi + 10*256 + 192]
    vpdpbusd zmm7, zmm14, zmm12
    vpdpbusd zmm3, zmm14, zmm13
    vpaddd zmm8, zmm8, zmm0
    vmovdqu64 zmm14, zmmword ptr [rdi + 11*256]
    vpdpbusd zmm4, zmm14, zmm12
    vpdpbusd zmm0, zmm14, zmm13
    vpaddd zmm9, zmm9, zmm1
    vmovdqu64 zmm14, zmmword ptr [rdi + 11*256 + 64]
    vpdpbusd zmm5, zmm14, zmm12
    vpdpbusd zmm1, zmm14, zmm13
    vpaddd zmm10, zmm10, zmm2
    vmovdqu64 zmm14, zmmword ptr [rdi + 11*256 + 128]
    vpdpbusd zmm6, zmm14, zmm12
    vpdpbusd zmm2, zmm14, zmm13
    vpaddd zmm11, zmm11, zmm3
    vmovdqu64 zmm14, zmmword ptr [rdi + 11*256 + 192]
    vpdpbusd zmm7, zmm14, zmm12
    vpdpbusd zmm3, zmm14, zmm13
    vpaddd zmm8, zmm8, zmm0
    vmovdqu64 zmm14, zmmword ptr [rdi + 12*256]
    vpdpbusd zmm4, zmm14, zmm12
    vpdpbusd zmm0, zmm14, zmm13
    vpaddd zmm9, zmm9, zmm1
    vmovdqu64 zmm14, zmmword ptr [rdi + 12*256 + 64]
    vpdpbusd zmm5, zmm14, zmm12
    vpdpbusd zmm1, zmm14, zmm13
    vpaddd zmm10, zmm10, zmm2
    vmovdqu64 zmm14, zmmword ptr [rdi + 12*256 + 128]
    vpdpbusd zmm6, zmm14, zmm12
    vpdpbusd zmm2, zmm14, zmm13
    vpaddd zmm11, zmm11, zmm3
    vmovdqu64 zmm14, zmmword ptr [rdi + 12*256 + 192]
    vpdpbusd zmm7, zmm14, zmm12
    vpdpbusd zmm3, zmm14, zmm13
    vpaddd zmm8, zmm8, zmm0
    vmovdqu64 zmm14, zmmword ptr [rdi + 13*256]
    vpdpbusd zmm4, zmm14, zmm12
    vpdpbusd zmm0, zmm14, zmm13
    vpaddd zmm9, zmm9, zmm1
    vmovdqu64 zmm14, zmmword ptr [rdi + 13*256 + 64]
    vpdpbusd zmm5, zmm14, zmm12
    vpdpbusd zmm1, zmm14, zmm13
    vpaddd zmm10, zmm10, zmm2
    vmovdqu64 zmm14, zmmword ptr [rdi + 13*256 + 128]
    vpdpbusd zmm6, zmm14, zmm12
    vpdpbusd zmm2, zmm14, zmm13
    vpaddd zmm11, zmm11, zmm3
    vmovdqu64 zmm14, zmmword ptr [rdi + 13*256 + 192]
    vpdpbusd zmm7, zmm14, zmm12
    vpdpbusd zmm3, zmm14, zmm13
    vpaddd zmm8, zmm8, zmm0
    vmovdqu64 zmm14, zmmword ptr [rdi + 14*256]
    vpdpbusd zmm4, zmm14, zmm12
    vpdpbusd zmm0, zmm14, zmm13
    vpaddd zmm9, zmm9, zmm1
    vmovdqu64 zmm14, zmmword ptr [rdi + 14*256 + 64]
    vpdpbusd zmm5, zmm14, zmm12
    vpdpbusd zmm1, zmm14, zmm13
    vpaddd zmm10, zmm10, zmm2
    vmovdqu64 zmm14, zmmword ptr [rdi + 14*256 + 128]
    vpdpbusd zmm6, zmm14, zmm12
    vpdpbusd zmm2, zmm14, zmm13
    vpaddd zmm11, zmm11, zmm3
    vmovdqu64 zmm14, zmmword ptr [rdi + 14*256 + 192]
    vpdpbusd zmm7, zmm14, zmm12
    vpdpbusd zmm3, zmm14, zmm13
    vpaddd zmm8, zmm8, zmm0
    vmovdqu64 zmm14, zmmword ptr [rdi + 15*256]
    vpdpbusd zmm4, zmm14, zmm12
    vpdpbusd zmm0, zmm14, zmm13
    vpaddd zmm9, zmm9, zmm1
    vmovdqu64 zmm14, zmmword ptr [rdi + 15*256 + 64]
    vpdpbusd zmm5, zmm14, zmm12
    vpdpbusd zmm1, zmm14, zmm13
    vpaddd zmm10, zmm10, zmm2
    vmovdqu64 zmm14, zmmword ptr [rdi + 15*256 + 128]
    vpdpbusd zmm6, zmm14, zmm12
    vpdpbusd zmm2, zmm14, zmm13
    vpaddd zmm11, zmm11, zmm3
    vmovdqu64 zmm14, zmmword ptr [rdi + 15*256 + 192]
    vpdpbusd zmm7, zmm14, zmm12
    vpdpbusd zmm3, zmm14, zmm13
    vpaddd zmm8, zmm8, zmm9
    vpaddd zmm10, zmm10, zmm11
    vpaddd zmm8, zmm8, zmm10
    vpslld zmm8, zmm8, 8
    vpaddd zmm4, zmm4, zmm5
    vpaddd zmm6, zmm6, zmm7
    vpaddd zmm4, zmm4, zmm6
    vpaddd zmm4, zmm4, zmm8
    vpaddd zmm8, zmm0, zmm1
    vpslld zmm8, zmm8, 7
    vpaddd zmm4, zmm4, zmm8
    vpaddd zmm8, zmm0, zmm2
    vpslld zmm8, zmm8, 6
    vpaddd zmm4, zmm4, zmm8
    vpaddd zmm0, zmm0, zmm1
    vpaddd zmm2, zmm2, zmm3
    vpaddd zmm0, zmm0, zmm2
    vextracti64x4 ymm14, zmm0, 1
    vpaddd ymm0, ymm0, ymm14
    vextracti128 xmm14, ymm0, 1
    vpaddd xmm0, xmm0, xmm14
    vpshufd xmm14, xmm0, 0x4e
    vpaddd xmm0, xmm0, xmm14
    vpshufd xmm14, xmm0, 0xb1
    vpaddd xmm0, xmm0, xmm14
    vmovd eax, xmm0
    vextracti64x4 ymm14, zmm4, 1
    vpaddd ymm4, ymm4, ymm14
    vextracti128 xmm14, ymm4, 1
    vpaddd xmm4, xmm4, xmm14
    vpshufd xmm14, xmm4, 0x4e
    vpaddd xmm4, xmm4, xmm14
    vpshufd xmm14, xmm4, 0xb1
    vpaddd xmm4, xmm4, xmm14
    vmovd ecx, xmm4
    shl rcx, 32
    or rax, rcx
    vzeroupper
    ret
