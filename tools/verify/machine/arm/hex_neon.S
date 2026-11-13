// Printed by odec.py from hasher.ode. Not written or edited by hand.
#if defined(__ELF__) && defined(__linux__)
.section .note.GNU-stack,"",%progbits
#endif
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
        ldp q0, q1, [x1]
        movz x9, #0x3130
        movk x9, #0x3332, lsl #16
        movk x9, #0x3534, lsl #32
        movk x9, #0x3736, lsl #48
        movz x10, #0x3938
        movk x10, #0x6261, lsl #16
        movk x10, #0x6463, lsl #32
        movk x10, #0x6665, lsl #48
        mov v5.d[0], x9
        mov v5.d[1], x10
        movi v4.16b, #0x0f
        ushr v2.16b, v0.16b, #4
        and v0.16b, v0.16b, v4.16b
        ushr v3.16b, v1.16b, #4
        and v1.16b, v1.16b, v4.16b
        zip1 v16.16b, v2.16b, v0.16b
        zip2 v17.16b, v2.16b, v0.16b
        zip1 v18.16b, v3.16b, v1.16b
        zip2 v19.16b, v3.16b, v1.16b
        tbl v16.16b, {v5.16b}, v16.16b
        tbl v17.16b, {v5.16b}, v17.16b
        tbl v18.16b, {v5.16b}, v18.16b
        tbl v19.16b, {v5.16b}, v19.16b
        stp q16, q17, [x0]
        stp q18, q19, [x0, #32]
        ret
