// The 64 hexadecimal characters of the 32 bytes at X1, written at X0. No table, no branch, no load
// but the hash itself: nothing an observer of time or cache sees depends on the bytes.
// Uses V0-V7 and V16-V19 (all caller-saved under AAPCS64); no stack.
        .text
        .balign 4
#ifdef __APPLE__
        .globl  _b3l_hex_neon
_b3l_hex_neon:
#else
        .globl  b3l_hex_neon
        .type   b3l_hex_neon, %function
b3l_hex_neon:
#endif
        ldp     q0, q1, [x1]
        movi    v4.16b, #0x0f
        movi    v5.16b, #9
        movi    v6.16b, #39
        movi    v7.16b, #0x30
        ushr    v2.16b, v0.16b, #4
        and     v0.16b, v0.16b, v4.16b
        ushr    v3.16b, v1.16b, #4
        and     v1.16b, v1.16b, v4.16b
        zip1    v16.16b, v2.16b, v0.16b
        zip2    v17.16b, v2.16b, v0.16b
        zip1    v18.16b, v3.16b, v1.16b
        zip2    v19.16b, v3.16b, v1.16b
        cmhi    v0.16b, v16.16b, v5.16b
        cmhi    v1.16b, v17.16b, v5.16b
        cmhi    v2.16b, v18.16b, v5.16b
        cmhi    v3.16b, v19.16b, v5.16b
        and     v0.16b, v0.16b, v6.16b
        and     v1.16b, v1.16b, v6.16b
        and     v2.16b, v2.16b, v6.16b
        and     v3.16b, v3.16b, v6.16b
        add     v16.16b, v16.16b, v7.16b
        add     v17.16b, v17.16b, v7.16b
        add     v18.16b, v18.16b, v7.16b
        add     v19.16b, v19.16b, v7.16b
        add     v16.16b, v16.16b, v0.16b
        add     v17.16b, v17.16b, v1.16b
        add     v18.16b, v18.16b, v2.16b
        add     v19.16b, v19.16b, v3.16b
        stp     q16, q17, [x0]
        stp     q18, q19, [x0, #32]
        ret
