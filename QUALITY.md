# How blake3-servil is checked

blake3-servil is a fast BLAKE3 implementation. It aims to produce
exactly the official digests.

Most of the extra speed comes from code written for specific processors
and from splitting work across processor cores. That is also where
mistakes are most likely, so the code is checked in several different
ways.

## Proofs of the kernels

The fastest parts are small routines called kernels. Most kernels are
written in assembly; a few, for Intel and AMD processors, are written
in Rust.

For the assembly kernels, the project uses formal verification:
symbolic execution compares the assembled instructions with a written
specification of BLAKE3. Each completed proof covers every input value
within its stated contract. The checks also examine memory accesses,
the calling convention, and whether input bytes or keys affect
branches or addresses.

The Arm kernels are covered at every block count they support. The
SME2 kernels process data in groups of sixteen chunks, and their
proofs cover any number of groups. In those proofs, each group's bytes
are separate symbols. So if a kernel read the wrong group's bytes, its
output would not match the specification, and the proof would fail.

The Intel and AMD assembly kernels are checked the same way. Single
compressions and extended output at 1 to 32 blocks are proved. For
batch hashing, an induction proof covers every input count in the
stated range for each instruction set and calling convention, at block
lengths 1 to 16 with a fixed counter and at 16 blocks with an
incrementing counter. Each proof uses one symbolic entry-stack
alignment covering the four legal ABI alignments.

Two further checks test the prover itself. The instruction models are
run against real processors on random states, including memory
instructions and deliberate unaligned-address controls. We also plant
mistakes in the assembly (a wrong stride, a wrong rotation, a loop
that cannot finish, a write into the caller's stack) and require the
proof to reject every one.

The proofs cover the assembly kernels. The Rust kernels, and the Rust
code that prepares work and combines results, are covered by tests.

## Tests, and tests of the tests

Everything else is tested.

The test suites compare outputs with published BLAKE3 examples, called
test vectors, and with a separate, simpler reference implementation.
They run these checks on the operating systems and processor types the
project supports.

The project also uses mutation testing to check the tests themselves.
It introduces one small mistake at a time (changing a comparison, say,
or skipping a step) and requires at least one test to fail. If no test
catches the newly introduced bug, the developers add a test to catch
that bug, or figure out why it isn't actually a bug.

Each program also runs a startup self-test. Before doing real work, it
hashes a few inputs with known answers. This can catch a broken build
or a processor that does not execute the code as expected.

## Memory and thread safety

Some performance-critical Rust code is `unsafe`: there the programmer
keeps Rust's memory rules, which the compiler checks everywhere else.

- **AddressSanitizer** rebuilds the Rust and C code with extra memory
  checks. It catches reads and writes outside allocated memory and use
  of memory after it has been released.
- **ThreadSanitizer** watches access from multiple threads. It catches
  data races, where threads access the same memory without proper
  coordination and at least one of them writes.
- **Miri** runs Rust code in an interpreter that enforces Rust's
  memory rules. It is slow, but it can catch mistakes in `unsafe` code
  that a normal test run may not expose.
- **Guard pages** cover assembly. A test places an inaccessible page
  of memory immediately beside an input or output buffer. If a kernel
  reads or writes even one byte outside that buffer, the processor
  faults and the test crashes.

## What the checks found

The checks found eight bugs. All are fixed. Examples:

- an Arm kernel produced the wrong digest for the shortest messages;
- a function silently ignored a partial final block of input;
- a reading helper could lose bytes it had already read when a later
  operation failed;
- Miri found an unsafe pattern in code shared between threads;
- batch assembly on Intel and AMD processors read beyond the end of
  an input, which could crash a program.

The proofs have not found a bug in the Arm kernels. They did find
mistakes in some of the tools and models used to construct the proofs.

## What remains uncertain

No human has carefully reviewed every line, and nobody outside the
project has audited the code. The proofs trust the written
specification, the instruction models, the automated prover (Z3),
and each kernel's stated
memory and calling convention. Tests cover the Rust kernels and the
Rust code around the assembly. These checks reduce risk, but they
cannot guarantee that no bug remains.

## Run the checks

```sh
git clone -b servil https://github.com/johnservil/BLAKE3
cd BLAKE3
cargo nextest run --release --lib --tests   # with cargo-nextest (https://nexte.st)
```

The [quality manual](docs/quality-manual.md) gives details for
experts and maintainers, including the limits of each check and how
to run the proofs.
