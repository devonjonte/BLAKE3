# Experiments: compiled code proved in Lean (#361)

Five experiments, each a Lean project of its own (`lake build` in its folder). None is a gate.
Each theorem is about machine code as llvm-objdump lists it, run on a small model of x86-64
written here, against a function written in Lean.

| Folder | The code | The theorem | Check |
|---|---|---|---|
| `.` | `read_x86_features` as rustc 1.99.1 builds it (84 instructions, three functions) | on every CPU, from any registers, it returns the rule's byte (`Spec.lean`) without a fault | 3 s |
| `loop/` | `scan` of `loop/fold.rs` (15 instructions, a loop), rustc 1.99.1, `opt-level=s` | for a slice of any length: the result, the slice's new contents, no other byte changed, the stack restored; and what it lets an observer see (addresses touched, each jump's direction) is a function of the slice's address and length alone | 1 s |
| `call/` | `scan2` of `call/two.rs` (15 instructions: it calls `scan`, then jumps to it) | both slices scanned, the second from the first's fold; the registers the convention says to keep are kept; the observer's trace is a function of addresses and lengths. `scan`'s theorem is used as its contract: its code is not run again | 1 s |
| `kernel/` | `blake3_servil_compress_in_place_sse41` of `c/blake3_sse41_x86-64_unix.S` (94 instructions, 467 executed) | for every chaining value, block, counter, length and flags it leaves the first eight words of the specification's `BLAKE3_COMPRESS` (`../lean/Generic.lean` at 32-bit words) and changes nothing else | 50 s |
| `kernel512/` | `blake3_servil_compress_in_place_avx512` of `c/blake3_avx512_x86-64_unix.S` (76 instructions, 362 executed; VEX and EVEX forms on XMM registers, `vprord` among them) | the same statement | 48 s |

What a reader reads and relies on, for each:

- the specification (`Spec.lean`; `Spec` in `loop/Scan.lean`; `../lean/Generic.lean`);
- the machine (`X86.lean`, `loop/X86.lean`, `kernel/Simd.lean`): the instructions used, a state,
  one step. Whatever is not modelled is a fault;
- the theorem's statement (`Proof.lean`, the end of `loop/Scan.lean`, `kernel/Main.lean`);
- that the `Code.lean` beside it is the machine code (`lift.py`, `kernel/lift_simd.py` from
  llvm-objdump's listing; `check.sh` here rebuilds the library and compares, for the first);
- Lean, and its compiler for `bv_decide`'s checker (the `_native.bv_decide` axioms each file
  prints; otherwise the three standard axioms).

Each folder's `mutants.py` changes one instruction at a time and requires the build to fail.

Known limits, stated so nobody takes these for more than they are:

- four copies of the model, not yet one: `loop/X86.lean` (and `call/X86.lean`, with two more registers, `call` and `jmp`) has byte memory with ownership and the observer's
  trace; `kernel/Simd.lean` has 128-bit cells for memory and no trace; `X86.lean` neither;
- the kernel's theorem is against the generic text at `BitVec 32`; `../lean/Bridge.lean` proves
  that text at `UInt32` is the specification, and the step between the two word types is not
  written;
- `kernel/lift_simd.py` reads a Mach-O object (as assembled on a Mac for x86-64) and resolves
  the three RIP-relative loads to the object's data itself;
- nothing here checks the models against a CPU or against Sail, as `cross_check_x86.py` does
  for the Python models.
