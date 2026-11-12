// Printed by odec.py from hasher.ode. Not written or edited by hand.
#if defined(__ELF__) && defined(__linux__)
.section .note.GNU-stack,"",%progbits
#endif
        .text
        .balign 4
#ifdef __APPLE__
        .globl  _b3l_push
_b3l_push:
#else
        .globl  b3l_push
        .type   b3l_push, %function
b3l_push:
#endif
        mov x16, x0
        ldr x16, [x16]
        mov x9, x16
        mov x16, x1
        mov x17, x0
        mov x8, #32
        add x17, x17, x8
        mov x8, x9
        lsl x8, x8, #5
        add x17, x17, x8
        ldp q0, q1, [x16, #0]
        stp q0, q1, [x17, #0]
        mov x16, x9
        mov x17, #1
        add x16, x16, x17
        mov x17, x0
        str x16, [x17]
        ret
