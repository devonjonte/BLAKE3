/* The cross-check of one/Machine.lean against this CPU: every instruction of the programs proved on it
 * (both one-block kernels, the parent functions, merge; its own bytes), on the random states
 * CrossOne.lean made, compared with what the Lean model says it leaves in the fourteen registers, the
 * sixteen vector registers, ZF and CF (where the model defines them) and 1024 bytes of memory. The
 * buffer is mapped at the address the model uses. Written by mk_cross_c.py.
 *   cc -O1 -o cross_one cross_one.c && ./cross_one vectors.txt
 * Exit status 0 only if every vector agrees. Needs Linux and an x86-64 CPU with AVX-512 F and VL. */
#define _GNU_SOURCE
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>

struct regs {
    uint64_t gpr[14];     /* rax rcx rdx rbx rsp rbp rsi rdi r8 r9 r12 r13 r14 r15 */
    uint64_t flags;       /* in, then out */
    uint64_t code;        /* where the instruction is */
    uint64_t xmm[16][2];  /* low half first */
};

void run_one(struct regs *r);
/* r10 holds the struct and r11 the real stack pointer: neither is in the model or the programs. */
__asm__(
    ".intel_syntax noprefix\n"
    ".globl run_one\n.globl run_back\n"
    "run_one:\n"
    "  push rbx\n  push rbp\n  push r12\n  push r13\n  push r14\n  push r15\n"
    "  mov r10, rdi\n"
    "  movdqu xmm0, [r10+128]\n"
    "  movdqu xmm1, [r10+144]\n"
    "  movdqu xmm2, [r10+160]\n"
    "  movdqu xmm3, [r10+176]\n"
    "  movdqu xmm4, [r10+192]\n"
    "  movdqu xmm5, [r10+208]\n"
    "  movdqu xmm6, [r10+224]\n"
    "  movdqu xmm7, [r10+240]\n"
    "  movdqu xmm8, [r10+256]\n"
    "  movdqu xmm9, [r10+272]\n"
    "  movdqu xmm10, [r10+288]\n"
    "  movdqu xmm11, [r10+304]\n"
    "  movdqu xmm12, [r10+320]\n"
    "  movdqu xmm13, [r10+336]\n"
    "  movdqu xmm14, [r10+352]\n"
    "  movdqu xmm15, [r10+368]\n"
    "  push qword ptr [r10+112]\n  popfq\n"
    "  mov r11, rsp\n"
    "  mov rax, [r10+0]\n"
    "  mov rcx, [r10+8]\n"
    "  mov rdx, [r10+16]\n"
    "  mov rbx, [r10+24]\n"
    "  mov rbp, [r10+40]\n"
    "  mov rsi, [r10+48]\n"
    "  mov rdi, [r10+56]\n"
    "  mov r8, [r10+64]\n"
    "  mov r9, [r10+72]\n"
    "  mov r12, [r10+80]\n"
    "  mov r13, [r10+88]\n"
    "  mov r14, [r10+96]\n"
    "  mov r15, [r10+104]\n"
    "  mov rsp, [r10+32]\n"
    "  jmp qword ptr [r10+120]\n"
    "run_back:\n"
    "  mov [r10+32], rsp\n  mov rsp, r11\n"
    "  mov [r10+0], rax\n"
    "  mov [r10+8], rcx\n"
    "  mov [r10+16], rdx\n"
    "  mov [r10+24], rbx\n"
    "  mov [r10+40], rbp\n"
    "  mov [r10+48], rsi\n"
    "  mov [r10+56], rdi\n"
    "  mov [r10+64], r8\n"
    "  mov [r10+72], r9\n"
    "  mov [r10+80], r12\n"
    "  mov [r10+88], r13\n"
    "  mov [r10+96], r14\n"
    "  mov [r10+104], r15\n"
    "  pushfq\n  pop qword ptr [r10+112]\n"
    "  movdqu [r10+128], xmm0\n"
    "  movdqu [r10+144], xmm1\n"
    "  movdqu [r10+160], xmm2\n"
    "  movdqu [r10+176], xmm3\n"
    "  movdqu [r10+192], xmm4\n"
    "  movdqu [r10+208], xmm5\n"
    "  movdqu [r10+224], xmm6\n"
    "  movdqu [r10+240], xmm7\n"
    "  movdqu [r10+256], xmm8\n"
    "  movdqu [r10+272], xmm9\n"
    "  movdqu [r10+288], xmm10\n"
    "  movdqu [r10+304], xmm11\n"
    "  movdqu [r10+320], xmm12\n"
    "  movdqu [r10+336], xmm13\n"
    "  movdqu [r10+352], xmm14\n"
    "  movdqu [r10+368], xmm15\n"
    "  pop r15\n  pop r14\n  pop r13\n  pop r12\n  pop rbp\n  pop rbx\n  ret\n"
    ".att_syntax\n");
extern char run_back[];

#define BASE 0x20001000ull
static uint64_t hex64(const char *s) { char b[17]; memcpy(b, s, 16); b[16] = 0; return strtoull(b, NULL, 16); }
static void hex128(const char *s, uint64_t out[2]) { out[1] = hex64(s); out[0] = hex64(s + 16); }

int main(int argc, char **argv) {
    FILE *f = fopen(argc > 1 ? argv[1] : "vectors.txt", "r");
    if (!f) { perror("vectors"); return 2; }
    unsigned char *code = mmap(NULL, 4096, PROT_READ | PROT_WRITE | PROT_EXEC, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    unsigned char *buf = mmap((void *)(BASE - 0x1000), 0x2000, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS | MAP_FIXED, -1, 0);
    if (code == MAP_FAILED || buf != (unsigned char *)(BASE - 0x1000)) { perror("mmap"); return 2; }
    static char line[32768];
    long tests = 0, bad = 0, skipped = 0, faults = 0, forms = 0, flagsChecked = 0;
    char last[64] = "";
    while (fgets(line, sizeof line, f)) {
        char *tok[80]; int n = 0;
        for (char *p = strtok(line, " \n"); p && n < 80; p = strtok(NULL, " \n")) tok[n++] = p;
        if (n < 2) continue;
        if (!strcmp(tok[0], "skip")) { skipped++; continue; }
        if (!strcmp(tok[0], "fault")) { faults++; printf("the model faults on %s\n", tok[1]); continue; }
        if (strcmp(tok[0], "test") || n != 68) { printf("unreadable line (%d fields)\n", n); return 2; }
        if (strcmp(last, tok[1])) { forms++; snprintf(last, sizeof last, "%s", tok[1]); }
        size_t len = strlen(tok[1]) / 2;
        for (size_t i = 0; i < len; i++) { unsigned v; sscanf(tok[1] + 2 * i, "%2x", &v); code[i] = (unsigned char)v; }
        code[len] = 0xFF; code[len + 1] = 0x25; memset(code + len + 2, 0, 4);          /* jmp [rip+0] */
        uint64_t back = (uint64_t)run_back; memcpy(code + len + 6, &back, 8);
        uint64_t seed = strtoull(tok[2], NULL, 10);
        for (uint64_t a = BASE - 512; a < BASE + 512; a++) *(unsigned char *)a = (unsigned char)((a * 2654435761ull + seed * 40503ull) / 256);
        struct regs r; memset(&r, 0, sizeof r);
        for (int i = 0; i < 14; i++) r.gpr[i] = hex64(tok[3 + i]);
        for (int i = 0; i < 16; i++) hex128(tok[17 + i], r.xmm[i]);
        r.flags = 0x2 | (tok[33][0] == '1' ? 0x40 : 0) | (tok[34][0] == '1' ? 0x1 : 0);
        r.code = (uint64_t)code;
        run_one(&r);
        int ok = 1;
        for (int i = 0; i < 14; i++) ok &= r.gpr[i] == hex64(tok[35 + i]);
        uint64_t e[2];
        for (int i = 0; i < 16; i++) { hex128(tok[49 + i], e); ok &= r.xmm[i][0] == e[0] && r.xmm[i][1] == e[1]; }
        if (tok[65][0] != '-') { ok &= ((r.flags >> 6) & 1) == (uint64_t)(tok[65][0] - '0'); flagsChecked++; }
        if (tok[66][0] != '-') { ok &= (r.flags & 1) == (uint64_t)(tok[66][0] - '0'); flagsChecked++; }
        for (int k = 0; k < 1024; k++) { unsigned v; sscanf(tok[67] + 2 * k, "%2x", &v); ok &= *(unsigned char *)(BASE - 512 + k) == v; }
        tests++;
        if (!ok) { if (bad++ < 12) printf("DIFFERS: %s (seed %s)\n", tok[1], tok[2]); }
    }
    printf("%ld vectors over %ld instruction forms: %ld differ; %ld flag values checked; %ld instructions left to the proofs; %ld model faults\n",
           tests, forms, bad, flagsChecked, skipped, faults);
    return bad || faults || !tests;
}
