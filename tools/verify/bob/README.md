# Bob's check: the kernels' proofs with the least to trust

Bob receives a tarball from us and hears: "every assembly kernel computes
BLAKE3's compressions as C2SP's Lean specification defines them, on Arm as
Arm's own specification defines the instructions". Bob suspects we are
lying. He has no further contact with us. What must he rely on to convince
himself?

That set, his *reliance set*, is everything whose mistakes or sabotage could
lead him to a wrong conclusion. This design makes it as small as we can.
Everything outside it is *evidence*: it can raise his confidence, and a
mistake in it cannot mislead him. Our Python provers, Z3, the fuzzing of
instruction models against CPUs, mutation testing, CI, and every claim in
our documents are evidence. (Zooko, October 22, 2026: the prover is free to
be anything; what Bob must trust is the verifier.)

## The principle

The prover is untrusted. It does the search and emits a proof that a small
trusted checker validates. A wrong proof fails the check, so a faster
prover, a new tool, or a bug in our search costs Bob nothing.

## Bob's reliance set, item by item

1. **Lean's kernel, used plainly.** No `native_decide`, which would add Lean's
   compiler, and no axioms beyond Lean's standard three. Bob checks the
   exported proof with Lean's kernel and with independent re-implementations
   (`lean4lean`, `nanoda`), so a kernel bug misleads him only if every
   kernel shares it.
2. **The statement, elaborated by Bob.** Lean's front end turns text into
   terms, and notation or an instance could make a statement mean
   something other than what it reads as. So the tarball carries a short
   statement file, using Lean core alone. Bob elaborates it himself, and
   Lean checks that our proof's theorem is that term exactly. Our proof
   files are untrusted input. The statement says:
   - the kernel's **bytes**, the **preconditions** (lengths, alignment,
     regions that do not overlap, the SME2 vector length), and the
     **result**: these output bytes, nothing else written, no fault;
   - that this holds for **every resolution of Arm's UNKNOWN and
     IMPLEMENTATION DEFINED choices**, so no choice of ours is relied on;
   - that it holds for **every address the linker could place the kernel and
     its constant tables at**, so our assembler, linker and build are not
     relied on;
   - separately, **constant time**: two runs with the same lengths and
     different data execute the same instructions and touch the same
     addresses. Bob then relies on Arm's list of data-independent-timing
     instructions and on his CPU, nothing of ours.
3. **The BLAKE3 specification, the part used.** The kernel theorems need
   C2SP's compression function and its chunk chaining, about 40 lines of
   `c2sp/BLAKE3/Blake3.lean`. The official test vectors, run in Lean, are
   evidence.
4. **Arm's ASL text, from Arm.** Arm publishes each instruction's semantics
   in the Arm Specification Language as part of its machine-readable
   architecture specification. Bob downloads it from Arm (or checks the
   tarball's copy against Arm's release, if the license lets us ship it);
   the proofs read the instructions the kernels use.
5. **Our ASL parser and interpreter, in Lean.** No formal semantics of ASL
   exists to borrow, so this part stays ours. It covers only the language
   features the used instructions reach. The parser is checked by round
   trip (the parsed tree, printed, matches Arm's text), and Bob can compare
   the interpreter with Arm's own ASL interpreter (ASLRef, in Arm's
   `herdtools7`) on random inputs, without our comparison script.
6. **The bytes he runs.** Bob takes the kernels' bytes from his own build
   or the crates.io package, with his own tools, and compares them with
   the statement's.
7. **What no proof removes:**
   - his CPU's agreement with Arm's specification, which he can test and
     never prove;
   - for x86-64, an instruction model, since no official formal
     specification exists. The best candidate is the ACL2 x86 model, far
     better tested than ours (Sail has a translation of it); Bob tests it
     on his CPU.

The checked claim is the kernels' correctness under their preconditions.
The Rust that calls them and arranges the tree is tested, not proved, so
Bob's conclusion is "the kernels compute BLAKE3's compressions" until that
Rust is proved too (#120).

## Why Arm's ASL in place of Sail or our own models

Arm's ASL reaches Lean through Sail by a long chain (`asl_to_sail`, Sail's
type checker and rewrites, its Lean backend), tens of thousands of lines.
The October 10 probe (`probe/sail-lean`) found two translation bugs in two
days (dropped tuple assignments, rems-project/sail#1772; `MOD` computing a
quotient, rems-project/sail-arm#33), the whole model ran out of memory at
81 GB, and Lean took over 40 minutes to elaborate the decoder. Our own
instruction models (the Python provers' `aarch64.py`, `vector.py`,
`sme.py`) agree with Arm's specification on 322 of 325 forms, but Bob would
have to trust our transcription. Arm's text, run by a small interpreter Bob
can read, asks less of him than either.

## Arm's text: where it comes from, and what may ship

- **The instructions' ASL** is in Arm's A64 ISA XML release, downloaded
  from `https://developer.arm.com/-/cdn-downloads/permalink/Exploration-Tools-A64-ISA/ISA_A64/ISA_A64_xml_A_profile-2026-03_96.tar.gz`
  (SHA-256 `9d138aa4dd6db8b04bd6ad3a378205537bf67172a5f99180729517d1445f1906`,
  BLAKE3 `cc29573c01df924dce36a89389f49ab1e9ff747530ab008c6ba87f8915a95109`,
  fetched October 22, 2026; Arm's other download pages answer bots with
  403). The archive holds the 2025-09 release in ASL1, the version of the
  language that Arm's reference manual and ASLRef define:
  `ISA_A64_xml_A_profile_2025-09_96-2025-09_ASL1/`, one XML file per
  instruction (decode and execute sections) and `shared_pseudocode.xml`
  (1,738 blocks, about 45,600 lines).
- **Its notice forbids reproducing any part without Arm's written
  permission.** So the repository holds none of it, not even excerpts in
  tests: the proofs read Bob's own download, named by path and checked by
  SHA-256, which is what item 4 above asks for anyway.
- **Arm's BSD-licensed edition** (AARCHMRS_BSD) carries the encodings and
  none of the semantics: every one of its 2,262 operations reads
  `// Not specified`.
- **Bob's conversion of the files to byte values** is his own one-line
  tool, as the kernel measurements below explain.
- **ASL's standard library** (`UInt`, `ZeroExtend`, `LSL`, `ROR`, ...) is not
  in the XML. It is ASLRef's `asllib/libdir/stdlib.asl` in
  github.com/herd/herdtools7 (903 lines; Arm's copyright under
  BSD-3-Clause, so it may ship), pinned by commit.
- **How much of Arm's text a proof reaches.** By name alone, `add`, `eor`,
  and `extr` reach 537 shared blocks (11,420 lines of code), through
  exception, debug and system-register paths a normal run never takes.
  The interpreter needs only the language features of the code a proof
  executes; a feature off that path fails the proof loudly. Measured once
  the parser runs.

## What Lean's kernel computes, and how fast

Without `native_decide`, every step Bob relies on is reduced by Lean's
kernel (`decide +kernel`). Measured on the VM, Lean 4.34.1 (October 22):

| work | size | time |
|---|---|---|
| count a 7-byte tag in a file, read as a Lean string (`include_str`) | 10.8 KB | 173 s |
| the same, the string's characters converted to numbers in the kernel | 10.8 KB | over 163 s (timed out) |
| the same, the file given as a list of byte values | 10.8 KB | 0.74 s |
| a loop of multiply, remainder and add on numbers | 100,000 steps | 2.6 s |

The kernel computes on number literals with GMP, but it handles each
character of a string by checking that character's validity proof, about
1.6 ms apiece. So Arm's files reach the proofs as lists of byte values,
which Bob makes from his own download with his own tool (for instance
`od -An -v -tu1`): one line of shell, the same for every file. Everything
after that (the XML's ASL sections, the parser, the interpreter, the
checker) computes on numbers and trees, at roughly 10 to 70 µs a step.

## Where the statement cuts Arm's machine

Arm's ASL describes the whole machine: memory accesses go through address
translation, alignment checks and faults; system registers and the
implemented features reach every instruction. The statement cuts it at
named places, each an assumption Bob reads:

- **Memory** at the accessor that maps a virtual address to bytes: a flat
  memory in which the accesses inside the given regions succeed.
- **System state** fixed to what a user program runs under (exception
  level 0, the settings an operating system gives it).
- **Features**: those the kernel needs are assumed implemented; the
  theorem holds for every choice of the others.

## How the proofs stay fast

Turning every proof step into Lean terms would be enormous (a kernel's
output is millions of term nodes). The proofs use a checker written in
Lean and proved sound once: symbolic evaluation of the bytes, the normal
form for 32-bit sums, xors, and rotations that `canon.py` uses today, and
bit-level checks for the small leaves (counters, lengths). Each kernel's
proof is then "the checker accepts these bytes", evaluated by Lean's
kernel. Each instruction form has one lemma, proved once: Arm's ASL for
it, interpreted, computes what the checker's fast operation computes.

## Plan

1. **The statement file**, written to be read, and Bob's check (the
   commands he runs) before any proof.
2. **Arm's ASL release**: its license, and the pseudocode of `add`, `eor`,
   and `extr` (BLAKE3's G on the integer unit) with what they call.
3. **The ASL parser and interpreter** for those, run against the CPU, and a
   proof that they compute 32-bit add, xor, and rotate.
4. **The checker** on one kernel, evaluated in Lean's kernel: how long does
   it take? This answers whether the design works without `native_decide`.
5. Then NEON, SVE and SME's ASL, the x86 model, and every kernel. The
   Python provers stay as the fast daily check until Bob's check covers
   what they cover, and then go.
