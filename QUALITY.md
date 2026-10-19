# How we know blake3-servil computes BLAKE3

blake3-servil is new code that does something old: it computes exactly the
digests official BLAKE3 computes, faster. New code is where bugs live, so
we checked it in three independent ways, and then checked the checks.

## Three layers

**1. Proofs, for the code tests reach least.** The fork's own assembly,
the AArch64 kernels for NEON and Apple's SME2, is proved correct: for
every possible input, key, counter and flags value, each kernel computes
the BLAKE3 standard's compression, as the CPU executes it. A solver
checks the machine code (disassembled from the object file, macros
expanded) against a specification of BLAKE3 written in Lean. The same
proofs show that the kernels read and write only their own buffers, and
that their branches and memory addresses depend on lengths alone, never
on the message or the key. All of the Arm assembly but one kernel is
proved: 368 proofs.

**2. Tests, and tests of the tests.** Every digest is checked against
the official test vectors and an independent reference implementation,
on every platform CI runs. Then mutation testing plants likely bugs in
the Rust, one at a time (2,442 of them: an operator changed, a bound off
by one, a call dropped), and requires some test to fail. A planted bug
that survives either gets a new test or is listed with the reason it is
harmless (most change only speed).

**3. Memory-safety tools.** AddressSanitizer, ThreadSanitizer and Miri
run over the library's tests. Assembly is invisible to all three, so
**guard pages** take their place there: the tests put each kernel's
input and output flush against an unmapped page, so a single byte read
or written outside a buffer crashes the test.

Beneath all three, every program checks its kernels against fixed answers
when it starts: a miscompiled build or a faulty CPU stops before its first
digest.

## What they found

Eight bugs, all fixed; none is known to have reached a user.

- **Tests and coverage** found five. Two could have produced wrong
  digests: an SME2 kernel mishandling one-block messages, and a hidden
  upstream function silently dropping a partial block (also reported
  upstream).
- **Its author rereading the change** (John Servil, an AI) found one
  that could have: `update_reader` losing bytes before an error, fixed 7
  minutes after it was written.
- **Miri** found a data race by Rust's aliasing rules that no test could
  have seen as a wrong digest.
- **The proofs' model of x86 assembly**, still in progress, found that
  upstream's AVX2 and AVX-512 batch kernels read up to 48 bytes past an
  input's end. **Guard pages** then reproduced it as a crash, reachable
  from a safe public call. It is fixed here and reported upstream
  ([BLAKE3-team/BLAKE3#598](https://github.com/BLAKE3-team/BLAKE3/issues/598)).
- **The proofs** themselves found no bug in the Arm kernels. They found
  faults in the checking: a carry flag modelled wrongly, and two
  translation bugs in Arm's Sail tooling (reported upstream). Their
  contribution is the guarantee: for every input, the proved code
  computes BLAKE3.

## How far each one reaches

`tools/qa_coverage.py` measures it mechanically. These are the lines of
code each technique exercises (x86-64 Linux, October 19, 2026):

| | safe Rust | unsafe Rust | Arm assembly | x86 assembly |
|---|---:|---:|---:|---:|
| lines of code | 7,929 | 1,805 | 22,476 | 15,100 |
| test suites | 95% of what x86 compiles | 97% of what x86 compiles | run, unmeasured | run, unmeasured |
| proofs | | | 99% | none yet |
| mutation testing | 44% | 10% | | |
| Miri's paths | 26% | 49% | | |

The x86 assembly is upstream's, unchanged; its proofs are under way. The
Arm Rust's test coverage is measured on Arm, where the suites reach 93%
of its lines.

## What is not done

No human has reviewed the code line by line, and nobody has audited it.
The [README's warning](README.md) stands. Also open: proofs for the
x86-64 kernels, a test run on AVX-512 hardware, and a proof that the Rust
around the Arm kernels keeps secrets from steering a whole call (it is
tested).

## Check it yourself

```sh
git clone -b servil https://github.com/johnservil/BLAKE3 && cd BLAKE3
cargo test --release --lib --tests          # the suites, guard pages among them
pypy3 tools/verify/prove_sme2.py             # SME2 proofs, minutes (an AArch64 machine)
pypy3 tools/qa_coverage.py                   # the table above, for your machine
```

The [quality manual](docs/quality-manual.md) is for experts and
maintainers: every claim stated precisely, with what it rests on; every
command; the controls that show each tool catches what it should; and
the full story of each bug.
