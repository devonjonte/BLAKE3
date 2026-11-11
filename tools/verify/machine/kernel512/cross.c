/* The cross-check of Simd.lean against this CPU: every instruction of the two one-block kernels
 * (their own bytes), on the random states Cross.lean made, compared with what the Lean model
 * says each leaves in the registers, the six memory cells and ZF.
 *   cc -O1 -o cross cross.c && ./cross vectors.txt
 * Exit status 0 only if every vector agrees. Needs an x86-64 CPU with AVX-512 F and VL. */
#define _GNU_SOURCE
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>

struct regs {
    uint64_t gpr[4];      /* rax rcx rdx r8 */
    uint64_t rsi, rdi;    /* the block's and the chaining value's buffers */
    uint64_t flags, pad;
    uint64_t xmm[16][2];  /* low half first */
};

void run_one(struct regs *r, void *code);
__asm__(
    ".intel_syntax noprefix\n"
    ".globl run_one\n"
    "run_one:\n"
    "  push rbx\n  push r12\n  mov rbx, rdi\n  mov r12, rsi\n"
    "  movdqu xmm0, [rbx+64]\n  movdqu xmm1, [rbx+80]\n  movdqu xmm2, [rbx+96]\n  movdqu xmm3, [rbx+112]\n"
    "  movdqu xmm4, [rbx+128]\n  movdqu xmm5, [rbx+144]\n  movdqu xmm6, [rbx+160]\n  movdqu xmm7, [rbx+176]\n"
    "  movdqu xmm8, [rbx+192]\n  movdqu xmm9, [rbx+208]\n  movdqu xmm10, [rbx+224]\n  movdqu xmm11, [rbx+240]\n"
    "  movdqu xmm12, [rbx+256]\n  movdqu xmm13, [rbx+272]\n  movdqu xmm14, [rbx+288]\n  movdqu xmm15, [rbx+304]\n"
    "  mov rax, [rbx]\n  mov rcx, [rbx+8]\n  mov rdx, [rbx+16]\n  mov r8, [rbx+24]\n  mov rsi, [rbx+32]\n  mov rdi, [rbx+40]\n"
    "  call r12\n"
    "  mov [rbx], rax\n  mov [rbx+8], rcx\n  mov [rbx+16], rdx\n  mov [rbx+24], r8\n  mov [rbx+32], rsi\n  mov [rbx+40], rdi\n"
    "  pushfq\n  pop rax\n  mov [rbx+48], rax\n"
    "  movdqu [rbx+64], xmm0\n  movdqu [rbx+80], xmm1\n  movdqu [rbx+96], xmm2\n  movdqu [rbx+112], xmm3\n"
    "  movdqu [rbx+128], xmm4\n  movdqu [rbx+144], xmm5\n  movdqu [rbx+160], xmm6\n  movdqu [rbx+176], xmm7\n"
    "  movdqu [rbx+192], xmm8\n  movdqu [rbx+208], xmm9\n  movdqu [rbx+224], xmm10\n  movdqu [rbx+240], xmm11\n"
    "  movdqu [rbx+256], xmm12\n  movdqu [rbx+272], xmm13\n  movdqu [rbx+288], xmm14\n  movdqu [rbx+304], xmm15\n"
    "  pop r12\n  pop rbx\n  ret\n"
    ".att_syntax\n");

static uint64_t hex64(const char *s) {
    char b[17]; memcpy(b, s, 16); b[16] = 0; return strtoull(b, NULL, 16);
}
static void hex128(const char *s, uint64_t out[2]) { out[1] = hex64(s); out[0] = hex64(s + 16); }

int main(int argc, char **argv) {
    FILE *f = fopen(argc > 1 ? argv[1] : "vectors.txt", "r");
    if (!f) { perror("vectors"); return 2; }
    unsigned char *code = mmap(NULL, 4096, PROT_READ | PROT_WRITE | PROT_EXEC, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    uint64_t *cv = aligned_alloc(64, 64), *block = aligned_alloc(64, 128);
    static char line[8192];
    long tests = 0, bad = 0, skipped = 0, faults = 0;
    char last[64] = ""; long forms = 0;
    while (fgets(line, sizeof line, f)) {
        char *tok[64]; int n = 0;
        for (char *p = strtok(line, " \n"); p && n < 64; p = strtok(NULL, " \n")) tok[n++] = p;
        if (n < 3) continue;
        if (!strcmp(tok[0], "skip")) { skipped++; continue; }
        if (!strcmp(tok[0], "fault")) { faults++; printf("the model faults on %s %s\n", tok[1], tok[2]); continue; }
        if (strcmp(tok[0], "test") || n != 57) { printf("unreadable line (%d fields)\n", n); return 2; }
        if (strcmp(last, tok[2])) { forms++; snprintf(last, sizeof last, "%s", tok[2]); }
        size_t len = strlen(tok[2]) / 2;
        for (size_t i = 0; i < len; i++) { unsigned v; sscanf(tok[2] + 2 * i, "%2x", &v); code[i] = (unsigned char)v; }
        code[len] = 0xC3;
        struct regs r; memset(&r, 0, sizeof r);
        for (int i = 0; i < 4; i++) r.gpr[i] = hex64(tok[3 + i]);
        for (int i = 0; i < 16; i++) hex128(tok[7 + i], r.xmm[i]);
        hex128(tok[23], cv); hex128(tok[24], cv + 2);
        for (int i = 0; i < 4; i++) hex128(tok[25 + i], block + 2 * i);
        r.rsi = (uint64_t)block; r.rdi = (uint64_t)cv;
        run_one(&r, code);
        int ok = r.rsi == (uint64_t)block && r.rdi == (uint64_t)cv && !strcmp(tok[56], "kept");
        for (int i = 0; i < 4; i++) ok &= r.gpr[i] == hex64(tok[29 + i]);
        uint64_t e[2];
        for (int i = 0; i < 16; i++) { hex128(tok[33 + i], e); ok &= r.xmm[i][0] == e[0] && r.xmm[i][1] == e[1]; }
        hex128(tok[49], e); ok &= cv[0] == e[0] && cv[1] == e[1];
        hex128(tok[50], e); ok &= cv[2] == e[0] && cv[3] == e[1];
        for (int i = 0; i < 4; i++) { hex128(tok[51 + i], e); ok &= block[2 * i] == e[0] && block[2 * i + 1] == e[1]; }
        if (tok[55][0] != '-') ok &= ((r.flags >> 6) & 1) == (uint64_t)(tok[55][0] - '0');
        tests++;
        if (!ok) { if (bad++ < 12) printf("DIFFERS: %s %s\n", tok[1], tok[2]); }
    }
    printf("%ld vectors over %ld instruction forms: %ld differ; %ld instructions left to the proofs; %ld model faults\n",
           tests, forms, bad, skipped, faults);
    return bad || faults || !tests;
}
