# Experiments: compiled code proved in Lean (#361)

Seven experiments, each a Lean project of its own (`lake build` in its folder). None is a gate.
Each theorem is about machine code as llvm-objdump lists it, run on a small model of x86-64
written here, against a function written in Lean.

| Folder | The code | The theorem | Check |
|---|---|---|---|
| `.` | `read_x86_features` as rustc 1.99.1 builds it (84 instructions, three functions) | on every CPU, from any registers, it returns the rule's byte (`Spec.lean`) without a fault | 3 s |
| `loop/` | `scan` of `loop/fold.rs` (15 instructions, a loop), rustc 1.99.1, `opt-level=s` | for a slice of any length: the result, the slice's new contents, no other byte changed, the stack restored; and what it lets an observer see (addresses touched, each jump's direction) is a function of the slice's address and length alone | 1 s |
| `call/` | `scan2` of `call/two.rs` (15 instructions: it calls `scan`, then jumps to it) | both slices scanned, the second from the first's fold; the registers the convention says to keep are kept; the observer's trace is a function of addresses and lengths. `scan`'s theorem is used as its contract: its code is not run again | 1 s |
| `kernel/` | `blake3_servil_compress_in_place_sse41` of `c/blake3_sse41_x86-64_unix.S` (94 instructions, 467 executed) | for every chaining value, block, counter, length and flags it leaves the first eight words of the specification's `BLAKE3_COMPRESS` (`../lean/Generic.lean` at 32-bit words) and changes nothing else | 50 s |
| `kernel512/` | `blake3_servil_compress_in_place_avx512` of `c/blake3_avx512_x86-64_unix.S` (76 instructions, 362 executed; VEX and EVEX forms on XMM registers, `vprord` among them) | the same statement | 48 s |
| `wide/` | the seven rounds of `blake3_servil_hash_many_avx512`'s sixteen-lane loop (784 instructions on ZMM registers; not the loads, the loop or the stores around them) | in every lane they are the specification's seven rounds on that lane's words, the message permuted between rounds as the specification permutes it | 60 s |
| `one/` | **two functions of the core crate as rustc compiled them** (`hasher::parent_output`, 23 instructions; `Output::chaining_value`, 29, which calls a compression kernel chosen by the platform's byte) **and both one-block kernels**, 222 instructions in one program on one model (`one/Machine.lean`: 14 general and 16 XMM registers, byte memory with ownership, aligned moves that fault off alignment) | the two functions, one after the other, leave the specification's **parent chaining value** of two children under any key and flags (`parent_cv_by_the_crates_code`); the kernel's run inside `chaining_value` is taken from the kernel's contract | 105 s |

What a reader reads and relies on, for each:

- the specification (`Spec.lean`; `Spec` in `loop/Scan.lean`; `../lean/Generic.lean`);
- the machine (`X86.lean`, `loop/X86.lean`, `kernel/Simd.lean`): the instructions used, a state,
  one step. Whatever is not modelled is a fault;
- the theorem's statement (`Proof.lean`, the end of `loop/Scan.lean`, `kernel/Main.lean`);
- in `call/`, nothing about the disassembler: the program is its bytes (`Code.image`) read by a decoder written in Lean (`call/Decode.lean`, 100 lines for the 13 instruction forms), and each line of the listing is a lemma Lean checks. In the other folders:
- that the `Code.lean` beside it is the machine code (`lift.py`, `kernel/lift_simd.py` from
  llvm-objdump's listing; `check.sh` here rebuilds the library and compares, for the first);
- Lean, and its compiler for `bv_decide`'s checker (the `_native.bv_decide` axioms each file
  prints; otherwise the three standard axioms).

Each folder's `mutants.py` changes one instruction at a time and requires the build to fail.

Known limits, stated so nobody takes these for more than they are:

- `one/` is the first with one model for kernels and compiled Rust; the others still have their own copies;
- `one/`'s Rust functions come from the two-crate trial (784fb406) built by rustc 1.99.1 for x86-64 Linux; their
  listing is `one/rust-functions.s`; a call through the GOT is taken to reach the kernel its relocation names;
- `one/ParentOutputProof.lean` and `one/ChainingValueProof*.lean` were written by scripts not kept here (the list
  of each function's memory writes, in order, is all they needed); `one/gen_kernel.py` writes the kernels' proofs;

- four copies of the model, not yet one: `loop/X86.lean` (and `call/X86.lean`, with two more registers, `call` and `jmp`) has byte memory with ownership and the observer's
  trace; `kernel/Simd.lean` has 128-bit cells for memory and no trace; `X86.lean` neither;
- `one/Bridge32.lean` proves the generic text at `BitVec 32` (what every theorem here is stated with) equal, bit for
  bit, to the specification's own `Blake3.BLAKE3_COMPRESS`, and `one/ParentSpec.lean` that the parent result is
  `Blake3.parentNode … .cv`; the older folders' theorems do not import it;
- `kernel/lift_simd.py` reads a Mach-O object (as assembled on a Mac for x86-64) and resolves
  the three RIP-relative loads to the object's data itself;
- nothing here checks the models against a CPU or against Sail, as `cross_check_x86.py` does
  for the Python models.

## `a64/`: the same loop on a second machine

`fold.rs`'s `scan` as rustc 1.99.1 compiles it for AArch64 (nine instructions, a post-indexed
store, a rotation folded into the EOR). `A64.lean` (130 lines) is a model of those nine
instructions with a decoder from the instruction words, so the program is its words; `Scan.lean`
proves the same statement as `loop/`: any length, the fold in W0, the scan in the slice, no other
byte changed, and an observer's trace that is a function of the slice's address and length and
the return address. The Lean function, the memory lemmas and the proof's structure are
`loop/`'s; the port took twelve minutes. `python3 mutants.py`: 8 of 8 changed instructions
rejected. Check: 2 s.
