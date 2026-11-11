/* The cross-check of X86.lean against this CPU: every instruction of the proved programs (its own
 * bytes), on the random states Cross.lean made, compared with what the Lean model says it leaves in
 * the ten registers, four vector registers, ZF and CF (where the model defines them) and 512 bytes
 * of memory. The buffer is mapped at the address the model uses.
 *   cc -O1 -o cross cross.c && ./cross vectors.txt
 * Exit status 0 only if every vector agrees. Needs an x86-64 CPU and Linux. */
#define _GNU_SOURCE
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>

struct regs {
    uint64_t gpr[10];     /* rax rcx rdx rbx rsp rbp rsi rdi r8 r9 */
    uint64_t flags;       /* in, then out */
    uint64_t code;        /* where the instruction is */
    uint64_t xmm[4][2];   /* low half first */
};

void run_one(struct regs *r);
/* r15 holds the struct, r14 the real stack pointer, r13 the instruction's address: none is in the model. */
__asm__(
    ".intel_syntax noprefix\n"
    ".globl run_one\n.globl run_back\n"
    "run_one:\n"
    "  push rbx\n  push rbp\n  push r12\n  push r13\n  push r14\n  push r15\n"
    "  mov r15, rdi\n  mov r13, [r15+88]\n"
    "  movdqu xmm0, [r15+96]\n  movdqu xmm1, [r15+112]\n  movdqu xmm2, [r15+128]\n  movdqu xmm3, [r15+144]\n"
    "  push qword ptr [r15+80]\n  popfq\n"
    "  mov r14, rsp\n"
    "  mov rax, [r15]\n  mov rcx, [r15+8]\n  mov rdx, [r15+16]\n  mov rbx, [r15+24]\n  mov rbp, [r15+40]\n"
    "  mov rsi, [r15+48]\n  mov rdi, [r15+56]\n  mov r8, [r15+64]\n  mov r9, [r15+72]\n  mov rsp, [r15+32]\n"
    "  jmp r13\n"
    "run_back:\n"
    "  mov [r15+32], rsp\n  mov rsp, r14\n"
    "  mov [r15], rax\n  mov [r15+8], rcx\n  mov [r15+16], rdx\n  mov [r15+24], rbx\n  mov [r15+40], rbp\n"
    "  mov [r15+48], rsi\n  mov [r15+56], rdi\n  mov [r15+64], r8\n  mov [r15+72], r9\n"
    "  pushfq\n  pop qword ptr [r15+80]\n"
    "  movdqu [r15+96], xmm0\n  movdqu [r15+112], xmm1\n  movdqu [r15+128], xmm2\n  movdqu [r15+144], xmm3\n"
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
    static char line[16384];
    long tests = 0, bad = 0, skipped = 0, faults = 0, forms = 0, flagsChecked = 0;
    char last[64] = "";
    while (fgets(line, sizeof line, f)) {
        char *tok[44]; int n = 0;
        for (char *p = strtok(line, " \n"); p && n < 44; p = strtok(NULL, " \n")) tok[n++] = p;
        if (n < 2) continue;
        if (!strcmp(tok[0], "skip")) { skipped++; continue; }
        if (!strcmp(tok[0], "fault")) { faults++; printf("the model faults on %s\n", tok[1]); continue; }
        if (strcmp(tok[0], "test") || n != 36) { printf("unreadable line (%d fields)\n", n); return 2; }
        if (strcmp(last, tok[1])) { forms++; snprintf(last, sizeof last, "%s", tok[1]); }
        size_t len = strlen(tok[1]) / 2;
        for (size_t i = 0; i < len; i++) { unsigned v; sscanf(tok[1] + 2 * i, "%2x", &v); code[i] = (unsigned char)v; }
        code[len] = 0xFF; code[len + 1] = 0x25; memset(code + len + 2, 0, 4);          /* jmp [rip+0] */
        uint64_t back = (uint64_t)run_back; memcpy(code + len + 6, &back, 8);
        uint64_t seed = strtoull(tok[2], NULL, 10);
        for (uint64_t a = BASE - 256; a < BASE + 256; a++) *(unsigned char *)a = (unsigned char)((a * 2654435761ull + seed * 40503ull) / 256);
        struct regs r; memset(&r, 0, sizeof r);
        for (int i = 0; i < 10; i++) r.gpr[i] = hex64(tok[3 + i]);
        for (int i = 0; i < 4; i++) hex128(tok[13 + i], r.xmm[i]);
        r.flags = 0x2 | (tok[17][0] == '1' ? 0x40 : 0) | (tok[18][0] == '1' ? 0x1 : 0);
        r.code = (uint64_t)code;
        run_one(&r);
        int ok = 1;
        for (int i = 0; i < 10; i++) ok &= r.gpr[i] == hex64(tok[19 + i]);
        uint64_t e[2];
        for (int i = 0; i < 4; i++) { hex128(tok[29 + i], e); ok &= r.xmm[i][0] == e[0] && r.xmm[i][1] == e[1]; }
        if (tok[33][0] != '-') { ok &= ((r.flags >> 6) & 1) == (uint64_t)(tok[33][0] - '0'); flagsChecked++; }
        if (tok[34][0] != '-') { ok &= (r.flags & 1) == (uint64_t)(tok[34][0] - '0'); flagsChecked++; }
        for (int k = 0; k < 512; k++) { unsigned v; sscanf(tok[35] + 2 * k, "%2x", &v); ok &= *(unsigned char *)(BASE - 256 + k) == v; }
        tests++;
        if (!ok) { if (bad++ < 12) printf("DIFFERS: %s (seed %s)\n", tok[1], tok[2]); }
    }
    printf("%ld vectors over %ld instruction forms: %ld differ; %ld flag values checked; %ld instructions left to the proofs; %ld model faults\n",
           tests, forms, bad, flagsChecked, skipped, faults);
    return bad || faults || !tests;
}
