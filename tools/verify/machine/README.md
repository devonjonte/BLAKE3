# Experiments: compiled code proved in Lean (#361)

Fourteen folders, each a Lean project of its own (`lake build` in its folder). None is a gate.
Each theorem is about machine code as llvm-objdump lists it, run on a small model of x86-64 (one
of AArch64) written here, against a function written in Lean. The table has the first seven; the
sections after it have `lang/`, `equihash/`, `a64/`, `gen/`, `hex/`, `alg/`, `eq/`, `CvStack::merge` and the kernels'
traces (both in `one/`).

**What each theorem is about: one build's bytes.** The listings are rustc 1.99.1's plain release
build for x86-64 Linux (the test subjects of `loop/`, `call/`, `gen/` and the kernels' objects were
made on a Mac for x86-64, as each folder says). Another compiler, another
optimisation level, `codegen-units`, `target-cpu`, LTO or inlining into a user's crate give other
bytes, of which these theorems say nothing. The `other_compiler.sh` scripts (here and in `one/`)
and the paragraphs "Another compiler" and "Other build settings" below show the proofs checking,
unedited, on some of those other bytes, and where they stop.

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

**Another compiler, the first folder** (`other_compiler.sh`, `other-compilers/Code-1.98.0.lean`): rustc
1.98.0 and 1.97.0 compile `read_x86_features` with two registers exchanged and three instructions in
another order. The theorem checks on that code with no edit of the proof, in 4 s. (It did not at
first: the proof named each instruction's lemma by its address; it now takes them by an attribute,
`code_at`, as the later folders do.) 1.99.0 and the beta of November 10 give 1.99.1's bytes.

**Other build settings, the same proof** (job `detect-builds.sh` of the study, on the EPYC 9255 host):
`panic=abort`, `debug-assertions`, `overflow-checks` and `codegen-units=1` give the same 84 instructions;
`opt-level` 2 and 1 give others (19 of 85 instructions differ) and the theorem checks unedited in 7 s;
`opt-level=s` gives others again (66 of 88 differ; it keeps the frame's address in RBX, which the callee saves on the stack and restores) and
the theorem checks once the symbolic run has one more lemma, `Sym.join64` (a 64-bit value stored and
loaded is itself, as a term, so the restored pointer is still an address the run can compare);
`-C target-cpu=native` uses `bextr` and R8, which this first model does not have, so the lifter stops.

**The theorem as the test** (job `source-mutants.sh` of the study): the 62 source mutants cargo-mutants
plants in the six functions this theorem covers, each built for release, lifted and judged by building
the theorem on its bytes. 3 compile to the unmutated bytes (the three the test suite lists as the same
code); 55 are refuted: the theorem fails and, run on the model, the code returns something else than
the rule on a CPU that `bv_decide` names (50) or on one of four real CPUs (5) (`witness.py`,
`Defs.lean`'s `agrees`); 2 are not proved (the named counterexamples were spurious and the four CPUs
agree); 2 stop the lifter (they need the sign flag and R8); none is accepted. 103 s on six shards of the
EPYC 9255 host.

Known limits, stated so nobody takes these for more than they are:

- `one/` is the first with one model for kernels and compiled Rust; the others still have their own copies;
- in `one/` the two kernels are a program of their own (`KCode.lean`, by `mk_kcode.py`) and their contracts are proved
  for it (`Sse.kcontract`, `Avx.kcontract`; `gen_kernel.py` writes both proofs); `Code.prog` has them (`has_kernels`), so
  the same contracts hold there (`contract`), and a function written in `lang/` is proved in a program of its own
  instructions and the kernels' only;
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
- against processors: five of the models are checked (`kernel512/cross.sh` for the kernels' SIMD model,
  `hex/cross.sh` for the model of `gen/` and `hex/`, `one/cross_one.sh` for `Machine.lean`, `eq/cross.sh`);
  and `cross.sh` here for the first model (this folder's `X86.lean`: the 71 instructions of four builds of
  detection that are not CPUID, XGETBV, a jump, a call or a stack move); `loop/`'s and `call/`'s copies,
  `wide/`'s and `a64/`'s are not; no model is checked against Sail, as `cross_check_x86.py` does for the Python models.

## `lang/`: an implementation language of our own, whose compiler proves its assembly

What the language and its prover are for, and what a failed check must say (the code, the contract, the
compiler or the proof), is in `lang/DESIGN.md`: read that first.

The direction since November 11: no Rust in the library's own code. Functions are written in a small
language made for the job (`hasher.ode`): at the word level (variables, loads, stores, calls, `if`,
`while`; the compiler picks registers) or at the machine level (the programmer chooses every
instruction: kernels), with `def` and `for` running at compile time. `odec.py` turns the source into
values of Lean's `L.Fn` (`Lang.lean`), from which Lean prints the assembly; `Sem.lean` is an
interpreter of the word level. Written in it and run against the crate (`run.sh`, `bench/`): `push`,
`merge`, a table-free `to_hex`, the whole one-shot hash, the one-block AVX-512 compression, and `hex`.

**`./prove.sh`: from source to a checked theorem, with no proof written by hand.** For the kernel `hex`
(the hash's hexadecimal: 45 SSE2 instructions, no table, no branch) and its `contract` in the source:
the assembler and the lifter give the object's bytes back, `prove.py` writes the statement from the
contract and the proof by a recipe for straight-line kernels (a symbolic run with the observer beside
the machine; `rfl` finds the trace and fails if it mentions the bytes read; `bv_decide` for each
written vector), and Lean checks **`hex_meets_its_contract`** (`Proof_hex.lean`): the 64 bytes written
are `Hex.hex8` of the 32 read (`HexSpec.lean`), no other byte changes, the callee's registers are
kept, and what an observer sees is one list fixed by the addresses, whatever the hash is. Check: 1 s.
`python3 mutants_hex.py`: the unchanged copy is accepted (the control), 10 of 10 changed instructions
rejected. On the EPYC 9255 host it takes 1.9 ns a call where the crate's `to_hex` (a table) takes
12.8; a million random hashes agree. A candidate for the crate that uses it: branch
`candidate/sam-hex-constant-time`.

**`./prove_fn.sh`: a function and its contract, from source to a checked theorem.** `merge` (the tree
hashing's loop: while the stack holds more than `target` values, the two newest become their parent) has
its contract in Lean, written by hand for a reader: `Merge.contract` (`Spec_merge.lean`), in the one
vocabulary of `Abi.lean` (arguments, a budget of stack, regions, `requires`, `ensures`, `modifies`;
`Abi.Meets` says what meeting it means under the calling convention) and in the specification's terms:
on return the stack is `Blake3.mergeTo` of the stack at the call. `Spec_stack.lean` says how a stack
lies in memory. The source (`hasher.ode`) names the contract and gives the prover what no reader needs:
the loop's `invariant` clauses, in the contract's own terms, and what `decreases`. `prove_fn.py` writes
`Proof_merge.lean` from that and the layout the compiler prints: `Inv` over the machine's state, the
three straight-line pieces (`enter`, `turn`, `leave`) by a symbolic run on memory in cells (`Cells.lean`)
with the kernels' contracts at the calls (`Kernels.lean`), and **`merge_meets`**: for all arguments,
`Abi.Meets Code_merge.prog 0x60000 (Merge.contract ...)`, by `Abi.meets_of_triple` (`AbiProof.lean`),
`Hoare.seq` and `Hoare.loop`. About 90 s from the source. `#reading_list Proof_merge.merge_meets`
(`ReadingList.lean`) asks Lean what that statement depends on: 929 lines, of which 30 are `merge`'s and
the stack's, 47 `Abi.lean`, 118 the specification, 461 the machine, 273 the instructions of `merge` and
the two kernels it calls (`one/KCode.lean`). Lemmas written by hand: `StackLemmas.lean` (the data
structure, once) and `Lemmas_merge.lean` (the function: 71 lines). `python3 mutants_fn.py`: 14 changed
instructions, 12 false statements and 5 changed clauses, after a control: 31 rejected.
`lang/DESIGN.md` has the conventions.

**The checked entry.** What `merge` requires of its arguments is the contract's `accepts`
(`1 ≤ target ∧ flags < 256`), stated once. `#checks Merge.contract` (`Checks.lean`) reads the comparisons
out of the contract; `check_fn.py` makes from them the entry `merge_checked` (8 instructions: it tests
them, returns 2^64 − 1 if one fails, and otherwise jumps to `merge`) and the proof of
**`merge_checked_meets`**: for all arguments, `Abi.Meets Code_merge.prog 0x60150 ((Merge.contract …).checked …)`.
Nobody wrote the tests or that proof. `reading_layers.py` compares what two theorems' statements depend on
(`#reading_defs`).

Limits: one loop, not nested; a loop-carried variable lives in a register; no call or condition outside
the loop; the trace is not in this theorem; `push` and the hash itself carry no contract yet. For `hex`: the recipe covers kernels that load, compute and store with no loop; x86-64 only; the object proved is assembled on a Mac for x86-64 (the instructions' bytes
are the ELF object's; the relocations differ); the constants' alignment is the assembler's.

## `equihash/`: another project's Lean function, tied to the bytes its Rust compiles to

[craftsoldier/equihash-lean](https://github.com/craftsoldier/equihash-lean) proves Zcash's Equihash
verifiers correct against the protocol specification, on Lean functions transcribed from the Rust by
hand. This folder is a trial of the link that work leaves to trust: one of its functions,
`Params.new?` (its transcription of `Params::new` of `zakura-equihash 4.0.0`), and the thirty
instructions rustc 1.99.1 makes of that Rust function (release, x86-64; `params_new.listing`).

- `Theirs.lean`: their definition, copied character for character (Copyright 2026 Julian Abraham,
  MIT OR Apache-2.0), because their repository builds with Mathlib and Lean 4.35 and this one with
  neither. Importing it is the next step.
- `X86.lean`: the first folder's model with R8, `div r32` (a fault on a zero divisor or a quotient past
  32 bits) and one more condition. Not checked against a processor yet.
- `Proof.lean`, `params_new_code`: from any registers, with the twelve bytes at `out` apart from the
  sixteen bytes of stack used, the code returns without a fault, restores what the convention keeps,
  and writes the tag 1, `n` and `k` exactly when `accepts n k` (the condition on two `u32`s, as
  bit-vectors); otherwise the tag 0 and nothing else. One symbolic run and `bv_decide`; 10 s.
- `Bridge.lean`, `new?_eq` and **`params_new_is_new?`**: `accepts` is their `Params.new?` on the two
  numbers (which is written over the naturals: nothing wraps, since `k < n` keeps `k + 1` below
  `2^32`), so the compiled code writes `Some(Params { n, k })` exactly when `Params.new? n k` is
  `some`, for all `2^64` pairs.
- `python3 mutants.py`: of 11 changed instructions 9 are rejected; the two accepted compute the same
  function (`n <= 513` in place of 512, where `n` is a multiple of 8; `k > n` in place of `k >= n`
  for the first rejection, where `k = n` is rejected by the checks that follow).

Limits: one function, straight-line; one build (a Mach-O object for x86-64 made on a Mac); the trace
is not stated; their definition is a copy.

## `a64/`: the same loop on a second machine

`fold.rs`'s `scan` as rustc 1.99.1 compiles it for AArch64 (nine instructions, a post-indexed
store, a rotation folded into the EOR). `A64.lean` (130 lines) is a model of those nine
instructions with a decoder from the instruction words, so the program is its words; `Scan.lean`
proves the same statement as `loop/`: any length, the fold in W0, the scan in the slice, no other
byte changed, and an observer's trace that is a function of the slice's address and length and
the return address. The Lean function, the memory lemmas and the proof's structure are
`loop/`'s; the port took twelve minutes. `python3 mutants.py`: 8 of 8 changed instructions
rejected. Check: 2 s.

## `gen/`: the function is written in Lean, its Rust is printed, its proof is generated

The question: if a function is written in Lean and its Rust is printed from that, can the proof
that the compiled bytes compute the Lean function be had without writing it?

- `Lang.lean` (110 lines): a language of 32-bit words (ten constructors: the carried value, the
  word, a literal, xor, add, and, or, not, rotate, shift) with its meaning `Exp.eval`, an ordinary
  Lean function, and its printing `Exp.rust`; and one loop, `Scan`: fold the body over a slice,
  leaving each value where its word was. Eight functions are written in it.
- `Rule.lean` (105 lines): the loop's rule, proved once, for any machine (the state is a type
  parameter): if one turn of a compiled loop does one step of the function (`Turn`), the whole
  loop does the whole fold for any length, changes no byte outside the slice, and shows an
  observer only the slice's address and length. Its axioms: `propext`, `Quot.sound`.
- `make.py`: Lean prints the Rust; rustc 1.99.1 compiles it (`opt-level=s`); llvm-objdump lists
  it; for each function the script writes `Code_NAME.lean` and `Proof_NAME.lean`. It reads off
  the listing where the loop keeps the carried value, the pointer, the count and any constant
  (rustc put `mix`'s carried value in EDX, not EAX, a mask in R8, and turned `!w & m` into an
  xor); a wrong reading is a proof that does not check. The proof of `Turn` is one symbolic run
  of the loop's body and `bv_decide`; the rest is the rule.
- Result: all eight functions (139 instructions) are proved with no line of proof written for
  any of them: `NAME_is_its_lean_function`, for a slice of any length: the fold in EAX, the scan
  in the slice, the frame restored, no other byte changed, and the trace a function of the
  slice's address and length and the stack pointer. Everything from nothing: 8 s.
- `mutants.py`: of 103 changed instructions 102 are rejected and one computes the same function
  (`or` for `xor` on disjoint bits). Of fifteen changes to the printed Rust (a wrong printer or
  compiler), the three that compute the same function are accepted, seven are rejected by the
  proof, and five stop the lifter at an instruction form it does not know
  (`mutants-20261111.txt`).

Limits: one loop construct and one frame shape; the build is `opt-level=s`. At `opt-level=3` rustc
unrolls these loops by four after a remainder loop, which the rule does not cover; at `opt-level=3`
with `-C llvm-args=-unroll-runtime=false` the loops keep their shape and all eight generated proofs
check unchanged (`make.py --opt 3 --flag=-Cllvm-args=-unroll-runtime=false`). That flag on the
library's own Rust changes no machine code that bench-hashes' ten check points run (one machine);
`opt-level=s` for it makes one of the ten slower by 7% (another machine). Each
new function needed instruction forms the model lacked (`not`, a three-operand `lea`, a rotation
by one, R8 and R9: ten minutes); the listing is llvm-objdump's; x86-64 only, though the rule is
not.

## `hex/`: a function of the public API, with a loop, a table and the red zone

`blake3_servil_core::Hash::to_hex` as rustc 1.99.1 compiled it in the two-crate trial (39
instructions, 324 executed; `to_hex.listing` is llvm-objdump's, `lift_hex.py` makes `Code.lean`).

- `to_hex_is_hex`: called with the output's address in RDI and the hash's in RSI, the table
  `0123456789abcdef` where the code's relocation points, the 68 bytes below the stack pointer and
  the output's 68 bytes owned and apart: it returns with the output's address in RAX, the length
  64 and `hex` of the 32 bytes in the output, every byte outside the output and the red zone as
  it was, and an observer's trace `hexLeak`.
- `the_trace_depends_on_the_hash`: two hashes that differ in a nibble give different traces: the
  table is read at `table + nibble`. The function is not constant-time in the hash. That matters
  only where the hash is a secret (a keyed hash's tag before it is compared, a derived key); the
  upstream library's `to_hex` is the same code. The theorem that states the trace is what shows
  it.
- `Regions.lean`: memory kept by region (`over m base inside written`), so a read passes all of a
  region's writes in one step and a write changes one table. The whole proof is one symbolic run
  and three closing steps; check 12 s. `python3 mutants.py`: 36 of 36 changed instructions
  rejected (`mutants-20261111.txt`).

`cross.sh` checks the model under `gen/` and this folder against the processor: the 64 instruction forms
of the proved programs that are not jumps or stack moves, 2,560 random states, registers, ZF and CF (4,760
flag values) and 512 bytes of memory compared: no difference on an EPYC 9255 and a Xeon Gold 6330; a model
whose 32-bit writes keep the upper half differs on 1,120. Binsec 0.11.3, run on a binary that links the
crate, reports the same four instructions of `to_hex` as memory-access leaks when the hash is secret, and
the SSE4.1 one-block kernel secure; it cannot read the AVX-512 kernel.

Limits: the loop's count is fixed (sixteen turns), so the run needs no invariant; the table's
contents and address are hypotheses (the lifter turns the RIP-relative `lea` into a parameter and
does not read the object's data); the listing is llvm-objdump's.

## `alg/`: the hasher's stack computes the specification's tree (no code named)

The specification defines the tree from the top (`Blake3.tree`: split at the largest power of
two below the number of chunks). The crate's `hasher.rs` builds it from the bottom with a stack:
`push` merges the stack to as many values as the chunk counter has one bits and puts the next
subtree's chaining value on top; `final_node` folds the last chunk's node into the stack from
the top. `Stack.lean` (270 lines) states those three functions as Lean functions and proves:

- `stack_is_the_tree`: for any `n ≥ 1` chunks pushed one by one, the final node is
  `Blake3.tree`'s root;
- `pushes_give_the_tree`: the same after any run of pushes of whole subtrees of `2^a` chunks
  where `2^a` divides the chunks so far (what `feed` pushes).
- `hasher_is_blake3`: for any key, mode, input and output length, the output of the node so
  made is `Blake3.blake3`'s bytes.

Axioms: `propext`, `Quot.sound`. Check: half a second. `python3 mutants.py`: with any of eight
wrong definitions (children swapped, a merge one value early or late, a wrong count of bits) the
proof no longer checks. Nothing in it mentions Rust or machine code: a proof that the compiled
`merge`, `push` and `final_node` run these functions is what would join it to the code, and is
not written. Not covered: `final_node`'s case of an empty last chunk; that `subtree_len`'s
lengths are such powers of two.

## Checking elsewhere: what went wrong once

On an older Xeon and on an ARM VM the kernels' proofs first failed: `bv_decide` gives its SAT solver ten
seconds, and one round's problem took longer there than on the machines it was written on. The round lemmas
now allow 900 seconds. The durable fix is to keep each `bv_decide`'s certificate in the repository
(`bv_decide?` writes it, `bv_check` reads it), so that checking runs no solver; it is not done.

## `eq/`: `Hash == Hash` is equality and shows nothing of either hash

`impl PartialEq for Hash` is `constant_time_eq::constant_time_eq_32` (0.4.2), a dependency's code
that runs when a user compares hashes. `probe.rs` compiles exactly that call (rustc 1.99.1,
x86-64): fourteen instructions, in which LLVM turned the crate's xor-and-or loop into two
`pcmpeqb`, a `pand` and a `pmovmskb`. `hash_eq_is_equality`: it returns 1 in AL when the 32 bytes
are equal and 0 when not, changes no byte but the eight below the stack pointer, and its trace is
`eqLeak` of the two hashes' addresses and the stack pointer, in which no byte of either hash
occurs. Check 2 s; `python3 mutants.py`: 11 of 11 changed instructions rejected.

With `hex/` this is the pair: the comparison users are told to use is constant-time in the code
as compiled; the hexadecimal is not.

Limits: the function is compiled alone (in the crate it is inlined into its callers); x86-64 only;
`cross.sh` here runs the eleven instructions that are not the frame's push, pop and return on the
processor against this folder's model (200 random states each), with a control whose `pmovmskb` reads
the wrong bit.

## `one/Merge*.lean`: `CvStack::merge`, whole, joined to the algorithm

`merge` (hasher.rs) is the stack's loop: `for _ in target..len { cvs[len-2] = parent(cvs[len-2], cvs[len-1]); len -= 1 }`.
Its machine code in the two-crate trial (`merge.listing`; 100 instructions lifted; the three panic blocks
are left out of the program, so a jump to one is a fault) saves six registers, makes an aligned 384-byte
frame, checks each index, asserts, and calls the AVX-512 or the SSE4.1 one-block kernel through the GOT by
the platform byte.

- `MergeTurn.lean`: `turn_avx`, `turn_sse`: one turn of the loop (426 or 532 instructions): the lower slot
  gets `merged`, the first eight words of the specification's compression of the key and the two top
  values, by the kernels' contracts; the length goes down by one; nothing else changes outside the frame.
- `MergeLoop.lean`: `loop`: any number of turns, by induction: memory holds `mergeN n es`.
- `MergeWhole.lean`: `prologue`, `epilogue` and **`merge_is_mergeN`**: called with `1 ≤ target < len ≤ 55`,
  the stack's values `es` in its array, the key and the kernels' structure where its arguments say, and
  its own stack owned and apart from them: `merge` returns to its caller with RBX, RBP and R12 to R15
  restored, the length `target`, the array holding `mergeN (len - target) es`, the tag as it was, and no
  byte changed outside its stack, the array and the length. No panic site is reached.
- `MergeSpec.lean`: **`merge_runs_mergeTo`**: read as the specification's chaining values, that stack is
  `Blake3.mergeTo` of the stack before: the function `alg/Stack.lean` proves a hasher may merge with
  (`hasher_is_blake3`). So for this function the chain is whole: bytes, model, Lean function, algorithm,
  specification.

Check: about three minutes from nothing with the kernels (which take most of it); the `Merge*` files
themselves 45 s. `RegionsX.lean` is `hex/Regions.lean` for this model, with whole reads and writes
outside a region. `python3 mutants_merge.py` changes one instruction of `merge` at a time: 10 of 11 are
rejected; the eleventh changes a byte `merge` stores in its frame and nothing reads (`mutants-merge-20261111.txt`).

Limits: the call through the GOT is taken to
reach the kernel its relocation names; `push`, the function that calls `merge`, and `final_node` are not
proved, so `hasher_is_blake3` is joined to the code at this one function only; the case `len ≤ target`
(no turn) and a `None` stack are not covered; the listing is llvm-objdump's.

## `one/Leak.lean`: the one-block kernels show only addresses

`Machine.lean` has no observer. `Leak.lean` adds one without touching it: `stepL` is the model's own `step`
with what it shows recorded beside it (each address read or written; where each jump, call and return
goes), and `stepsL_core` proves the recorded run is the model's run, so a theorem about the trace is about
the same executions as the theorems about the result. `sse41_kernel_shows_only_addresses` and
`avx512_kernel_shows_only_addresses`: there is a trace, fixed by the chaining value's address, the
block's, the stack pointer and the return address, that every run of the kernel shows, whatever the
chaining value, block, counter, length and flags are. The proof leaves the trace to be found by
unification with a variable that may mention only those four, so a trace that depended on anything else
would not check (it did not, until the return address was among them). Check: 7 s for both.

**`merge`, all three in one statement** (`MergeParts.lean`, `MergeTrace.lean`, `MergeAll.lean`, written by
`leakgen.py`, `tracegen.py` and `allgen.py` from the proofs above, so the same hypotheses and the same
symbolic runs carry the trace). Each part's trace is a definition (`pre_avx_shows self arr keyp fp len`, …)
whose text Lean was asked for and which compiles only because it mentions nothing but those arguments;
the kernels' traces come from the two theorems above; `loopShows` puts the turns together.
**`merge_whole`**: with `merge_is_mergeN`'s hypotheses, the recorded run of the whole function, the
kernels' instructions included, ends with `merge_is_mergeN`'s result, and its trace is
`mergeShows plat self p keyp rsp0 fp ra len target`: a function of where the arguments, the stack and the
caller are, of the platform byte, the stack's length and the target. The stack's values, the key and the
flags are not among its arguments. So for this one function of the crate the three properties hold of the
same executions: the result the specification's algorithm asks for, no byte touched that it does not own
or changed that it should not, and nothing secret in what it shows. Check: 45 s beyond `merge`'s own.

Not done the same way: the parent functions.

**Another compiler** (`other_compiler.sh`, `other-compilers/merge-1.98.0.listing`, `recode.py`). rustc 1.98.0
compiles `merge` to the same hundred instructions as 1.99.1 but for two stores: the other order, and
`movups` where 1.99.1 has `movaps`. The script lifts that listing in place of 1.99.1's and builds every
theorem about `merge` again: the table and its lemmas are written again by script, Lean is asked again
what each part shows, and **no proof text is edited**: `merge_is_mergeN`, `merge_runs_mergeTo` and
`merge_whole` check for 1.98.0's code (the trace differs in the order of two addresses, as the code
does). About three minutes. What this does not show: a compiler that restructures a function (the
beta of November 10 no longer inlines the pushes in `to_hex`: 49 instructions and two calls a byte where
1.99.1 has 39 and none) needs a new proof, not a re-run.

`cross_one.sh` checks `Machine.lean`, the model under all of this folder's theorems, against the
processor: every instruction of the five programs (258 distinct; 225 once jumps, calls, the stack's
moves and the constants the linker places are left to the proofs), forty random states each, comparing
fourteen registers, sixteen vector registers, ZF and CF where the model defines them, and 1024 bytes
of memory; then a control whose 32-bit writes keep the upper half. Needs AVX-512 F and VL.
