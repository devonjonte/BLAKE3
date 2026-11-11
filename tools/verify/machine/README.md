# An experiment: the compiled x86-64 detection, proved in Lean (#361)

`lake build` checks, in a few seconds, one theorem (`Proof.lean`):

> From any registers and on any CPU, the 84 instructions rustc and LLVM made of
> `read_x86_features` (with `read_cpu_words` and `_xgetbv`, which it calls) run to their
> return without a fault and leave in AL the byte the rule gives for that CPU; the stack
> pointer is popped, RBX and RBP are as they were.

What a reader has to read, and trust:

- `Spec.lean`: the rule, a feature at a time (50 lines).
- `X86.lean`: the machine (200 lines): the 23 instructions this code uses, a state, one step.
  Whatever it does not model is a fault: reading a byte never written, a branch on a flag left
  undefined, a CPUID leaf other than 0, 1 and 7, XGETBV where the OS has not enabled it.
- The theorem's statement, with `words` and `entry` above it.
- That `Code.lean` is the library's machine code: `check.sh` builds the library, disassembles
  the three functions with llvm-objdump, lifts them again (`lift.py`) and compares.
- Lean, and its compiler for `bv_decide`'s checker (the `_native.bv_decide` axioms printed at
  the end; the three standard axioms otherwise).

Not to be read or trusted: `Sym.lean` and the proof's steps (Lean checks them).

`mutants.py` changes one instruction at a time, 25 times, and builds each: 23 are rejected,
and the two accepted change nothing the code computes (a test of OSXSAVE made twice; a
comparison constant between two values the compared word cannot take).
