# How blake3-servil is checked

blake3-servil is a modified BLAKE3 implementation that aims to produce
exactly the official digests, faster.

Most of the extra speed comes from code written for specific processors
and from splitting work across processor cores. That is also where
mistakes are most likely, so the project checks the code in several
different ways.

## Proofs of the kernels

The fastest parts are small routines called kernels, some of them
written in assembly.

For Arm kernels, the project uses formal verification: symbolic execution
compares assembled instructions with a written specification of BLAKE3.
Each completed proof covers every input value within its stated contract.
The checks also examine memory accesses, the calling convention, and
whether input bytes or keys affect branches or addresses.

The integer and NEON kernels' supported block counts are covered. The
SME2 proofs also cover every group count in their stated ranges. Their
loop proofs establish progress to the next group, and every group's input
bytes are independent, so a kernel that read another group's bytes would
compute a different result.

On Intel and AMD processors, upstream's assembly kernels are checked the
same way. Single compressions and extended output at 1 to 32 blocks are
proved. For batch hashing, an induction proof covers every input count
in the stated range for each instruction set and calling convention, at
block lengths 1 to 16 with a fixed counter and at 16 blocks with an
incrementing counter. Each proof uses one symbolic entry-stack alignment
covering the four legal ABI alignments.

Two further checks test the prover itself. The instruction models are
run against real processors on random states, including memory
instructions and deliberate unaligned-address controls. We also plant
mistakes in the assembly (a wrong stride, a wrong rotation, a loop that
cannot finish, a write into the caller's stack) and require the proof to
reject every one.

The proofs do not cover the fork's own Intel and AMD kernels, written in
Rust, or the Rust code that prepares work and combines results.

## Tests, and tests of the tests

Everything else is tested.

The test suites compare outputs with published BLAKE3 examples, called
test vectors, and with a separate, simpler reference implementation.
They run these checks on the operating systems and processor types the
project supports.

The project also uses mutation testing to check the tests themselves.
It introduces one small mistake at a time (changing a comparison, say,
or skipping a step) and requires at least one test to fail. If no test
notices, the developers add a test or record why that mistake is
harmless. A mistake that makes a test wait forever is a third outcome:
the clock stops the test, which is recorded too, and where the code can
be made to fail instead of waiting (a loop that counts, a wait that
checks its end) it is, so the tests see the mistake. On the x86-64
machine that runs the check, every one of about 1,070 such mistakes is
caught, explained, or listed as a wait, and the list of each is in the
repository.

Each program also runs a startup self-test. Before doing real work, it
hashes a few inputs with known answers. This can catch a broken build or
a processor that does not execute the code as expected.

## Memory and thread safety

Some performance-critical Rust code is `unsafe`: there the programmer
keeps Rust's memory rules, which the compiler checks everywhere else. Assembly code needs separate checks.

- **AddressSanitizer** rebuilds the Rust and C code with extra memory
  checks. It catches reads and writes outside allocated memory and use
  of memory after it has been released.
- **ThreadSanitizer** watches access from multiple threads. It catches
  data races, where threads access the same memory without proper
  coordination and at least one of them writes.
- **Miri** runs Rust code in an interpreter that enforces Rust's memory
  rules. It is slow, but it can catch mistakes in `unsafe` code that a
  normal test run may not expose.
- **Loom** runs a small piece of threaded code under every order its
  threads could take, instead of the one order a test run happens to
  take. The place a thread waits for another's work to finish (the
  "finish handshake") is written as one word that both sides read and
  change in single steps, and Loom checks every interleaving of them:
  a wait that could never end shows up as a deadlock, at once, rather
  than as a test that hangs until a clock stops it. The mutation check
  uses the same Loom test to judge mistakes planted in that code.
- **Guard pages** cover assembly. A test places an inaccessible page of
  memory immediately beside an input or output buffer. If a kernel reads
  or writes even one byte outside that buffer, the processor faults and
  the test crashes.

These tools see different layers. None of the first three can inspect
assembly, which is why guard pages matter.

## What the checks found

The checks found eight bugs. All are fixed, and none is known to have
reached a user. Examples:

- an Arm kernel produced the wrong digest for the shortest messages;
- a function silently ignored a partial final block of input;
- a reading helper could lose bytes it had already read when a later
  operation failed;
- Miri found an unsafe pattern in code shared between threads;
- batch assembly on Intel and AMD processors read beyond the end of an
  input, which could crash a program. This bug came from upstream
  BLAKE3 and has been reported there.

The proofs have not found a bug in the Arm kernels. They did find
mistakes in some of the tools and models used to construct the proofs.

## What remains uncertain

No human has carefully reviewed every line, and nobody outside the
project has audited the code. The proofs trust the written specification,
the instruction models, Z3, and each kernel's stated memory and calling
convention. Tests cover the fork's own Intel and AMD kernels and the Rust
code around the assembly. These checks reduce risk, but they cannot
guarantee that no bug remains.

## Run the checks

```sh
git clone -b servil https://github.com/johnservil/BLAKE3
cd BLAKE3
cargo nextest run --release --lib --tests   # with cargo-nextest (https://nexte.st)
```

The [quality manual](docs/quality-manual.md) gives details for experts
and maintainers, including the limits of each check and how to run the
proofs.
