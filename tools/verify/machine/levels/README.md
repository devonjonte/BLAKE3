# The tree's levels: another design beside the stack (an experiment, November 12, 2026)

Sam's design, from earlier work on BLAKE3, set beside the stack of `../lang/hasher.ode` to see what the
two share: code, contracts, tests, proofs.

**The stack** (`push`, `merge`): one value a pending subtree; a parent is written where its left child
was; values are merged as they arrive, so the caller holds back whatever may be the root, and tells
`merge` how far to go (`target`: the count's one bits).

**The levels** (`ladd`, `lroot`; `levels.ode`):
1. **A parent has memory of its own.** Each level has two places side by side: a pair there *is* its
   parent's 64-byte block, and the parent is written to the level above, never over a child.
2. **No pair is hashed while it may be the root's.** The two newest values wait at the bottom until a
   third arrives; above the bottom a pair becomes its parent at once, for by then a later value exists.
   So every chunk's value is added, the last too, and `lroot` makes the root by one fold.

**In the proof's words** (and now the code's): the levels are a counter in binary. A level that has
received an odd number of values holds the newest of them in its first place; each pair it received
went, as the pair's parent, to the level above. The newest chunk of all waits in the bottom's free place.
`ladd` settles the value that waited (while a level is full, its pair goes up) and puts the new chunk in
its place; `lroot` folds each level that holds a value onto the one that waits.

**Both are proved** (x86-64, as assembled, for all arguments): `Proof_ladd.ladd_meets` and
`Proof_lroot.lroot_meets`, below.

**Memory** (Sam, November 12: its cost is in lines and pages touched, not in bytes). The levels are 3520
bytes and the stack 1792. Counted from the layouts, not measured, for 64-byte lines (x86-64): a level is
one cache line, so a parent reads one line and writes half of another; the stack's values are 32 bytes
from byte 32, so every second pair lies across two lines. Over 1024 values the levels touch 11 lines (the
count's and ten levels), the stack 6 and its two scratch buffers; the levels above are never touched. On
Apple's processors a line is 128 bytes and a page 16 KiB: two levels a line, and everything here in one
page. Both structures are on a 64-byte boundary in what is timed below: in the standalone trial by the
harness, and inside `hash` and `hash2` by `buf ... align 64` (the compiler has it since this experiment;
putting them on the boundary moved no time by more than run-to-run differences).
What the bytes do cost: `hash2`'s frame is 5232 bytes against `hash`'s 3920, so on 4 KiB pages its hot
buffers lie on two pages, because the levels' untouched tail lies between them. Ordering the frame (the
cold tail last) would undo that; not done, and no warm timing shows it.

## Tried (Threadripper 7975WX; single runs: inventory, no speed verdict)

| | |
|---|---|
| `model.py`: the design against the specification's tree | every count of chunks from 2 to 3000 |
| `ladd`, `lroot` as assembled, against the tree (the crate's kernel) | 2,455 roots: every count to 700, others to 5000; three modes |
| `hash2` (the whole hash on the levels) against the crate | 8,154 inputs agree |
| `hash2` against **`Hash.byteContract`, the stack hash's contract, unchanged** (`try_hash2.sh`) | 105 examples meet it, 0 do not; the control holds on 105 |

| | the stack | the levels |
|---|---|---|
| a value added, and the root at the end (1024 values) | 43.5 ns a value | 41.0 ns (-5.8%) |
| the hash of 2 KiB, 4 KiB, 16 KiB, 32 KiB | 746, 1,007, 2,276, 4,611 ns | 753, 1,009, 2,232, 4,520 ns (+0.9% to -2.0%) |
| copies of 32 bytes a parent | 4, and two scratch buffers | 1 (the key), no scratch |
| instructions | `push` 27, `merge` 89; the root's fold is inside `hash` | `ladd` 96, `lroot` 108 |
| the caller | holds back the last chunk; computes `target` | adds every value; asks for the root |

(`hash2` is 560 instructions against `hash`'s 810, but it has no 32-chunk path: not a comparison. The
times are of the code as `ladd`'s proof left it (`ladd` was 121 instructions and `lroot` 157 before), on a
machine not quite idle: every column, the crate's too, is about 2% above the run before the change, and the
levels stand to the stack as they did.)

## The proof of `ladd`, beside the stack's (November 12)

    ladd_meets : ∀ lv key flags plat cv k chunks new,
      Abi.Meets Code_ladd.prog 0xB0000 (Ladd.contract lv key flags plat cv k chunks new)

(`../lang/Spec_levels.lean`, `Spec_ladd.lean` the statement; `Lemmas_ladd.lean` by hand; `Proof_ladd.lean`
written by the compiler; `./prove_fn.sh` with `SOURCE=../levels/levels.ode ODEMOD=LevelsOde`, as
`../prove_all.sh` runs it.) `ladd` does what `add` does on the stack (`push`, then `merge`), and its
contract says more: the levels hold the specification's subtrees, where the stack's contracts say `mergeTo`
and leave the tree to `alg/Stack.lean`. So the fair comparison is with `push`, `merge`, `add` and the
stack's part of the tree's proof together:

| | the stack (`push` + `merge` + `add`) | the levels (`ladd`) |
|---|---|---|
| instructions under the theorem | 26 + 88 + 32 | 95 |
| the statement, by hand (contract and layout) | 91 lines (4 files) | 63 lines (2 files) |
| lemmas, by hand | 226 lines for the code, and about 220 of `alg/Stack.lean` and `AddTree.lean` for the tree | 376 lines, the tree included |
| the proof the compiler writes | 67 + 245 + 147 lines | 262 lines |
| Lean's check of it (Threadripper 7975WX) | 24 s, 143 s, and `add`'s within 99 s | 167 s |
| a reader of the theorem reads | 935 lines (`add_meets_bytes`; the tree not reached) | 854 lines (the tree reached) |
| axioms beyond Lean's three (`bv_decide`) | 718 | 377 |
| examples run in the machine model before the proof | 4 + 8 + 5 | 9 (8 meet the contract, 1 is refused as not an example) |
| each instruction made a no-op in turn | `push` 26 of 26 refused; `add` 30 of 32 (two redundant moves) | 94 of 95 refused (one redundant move: a value loaded again that the register still holds); 88 already refuted by an example |

From the first line of the contract to the checked theorem took under an hour, with the compiler's proof
generator as it was for `merge` and four additions to it (below); `merge`'s own took an evening, generator
included. The lemmas checked on their first compilation but one (a search that did not end).

**What the system lacked, and now has:**
- the machine model had no shift right: `shr64` (one line of meaning in `../one/Machine.lean`; its two forms
  here are in the processor cross-check, 10,080 vectors over 252 forms, none differs; a model that shifts
  by one bit less is found). Every x86-64 theorem's reading list grew by four lines;
- the proof generator: facts at hand from the first instruction in a function with a loop (`enter know`),
  an invariant's fact taken apart after the loop (`leave open`), and a variable read from memory before
  the loop used in what follows (its value is what the invariant says it is);
- `prove_fn.sh`, the examples and the audit took a source file other than `hasher.ode`; a layout with
  parameters (`Levels.layout k mode`) has its sample.

**What the code's shape owes to the prover** (a cost, said): the generator takes one loop, at the top of
the function, with no branch before it. So "nothing added yet" is not a branch around the loop but a value
(`x = ln | ((ln - 1) >> 63)`: the count, or 1 for none), and the loop asks only whether `x` is even.

**What the proof gave the code:** the counter. With it `ladd`'s loop needs one variable (121 instructions
became 95), and `lroot` lost its special case for the bottom pair (157 became 121): the newest chunk's
value is taken first, and every level that holds a value, the bottom included, is folded onto it the
same way.

## The proof of `lroot` (November 12)

    lroot_meets : ∀ out lv key flags plat k chunks,
      Abi.Meets Code_lroot.prog 0xC0000 (Lroot.contract out lv key flags plat k chunks)

For levels over two chunks or more, the 32 bytes at `out` become the first eight words of the
specification's output for the tree over them (`Levels.rootCv`: the root node's compression with the `ROOT`
flag), and the levels and the key are as they were. The stack has no counterpart under a theorem: its
root is folded inside `hash`.

| | `lroot` |
|---|---|
| instructions under the theorem | 107 |
| the statement, by hand | 26 lines (`Spec_lroot.lean`), on `Spec_levels.lean`'s 43 |
| lemmas, by hand | 271 lines (`Lemmas_lroot.lean`), the tree's fold included (the specification's own split, `go_split`) |
| the proof the compiler writes | 390 lines; five ways through a turn (the root's parent or another, each by either kernel; a level that holds nothing) |
| Lean's check of it | about three minutes (181 s and 209 s, the machine busy both times) |
| a reader of the theorem reads | 888 lines |
| axioms beyond Lean's three (`bv_decide`) | 783 |
| examples run in the machine model before the proof | 8 (7 meet the contract: two to eight chunks, both kernels; 1 is refused as not an example) |
| each instruction made a no-op in turn | of 107: 103 refused, 3 accepted, 1 without a verdict (below); 98 refuted by an example |

Twenty minutes from the contract's first line to the checked theorem, four additions to the proof
generator included: a buffer of the frame named in an invariant (`acc` holds the fold across turns); a
lemma a way through the turn (`by A | B | C`: the first that applies); an invariant that is made, not
kept, at entry (`from`); a fact only one branch has (`open ... when`). The proofs of `merge`, `push`,
`merge_steps` and `ladd` are written the same to the letter by the changed generator.

One thing the first run found: the function fills `out` at the end, so the invariant must say the bytes
at `out` are the program's through the loop (`invariant Region(out, 32)`); the contract says it at the
call only.

**What the audit found, and what was removed for it.** The first proved `lroot` was 111 instructions. Made
no-ops one at a time, the proof still checked without these (of the first 82 tried):
- two that set a variable to zero before the loop (`var f = 0`, mine, to declare it): dead; the variable is
  now declared where it is first set. (And `odec.py` now refuses an assignment to a variable never declared:
  it had taken one silently.)
- a jump over an empty `else`: the compiler (`Lang.lean`) no longer emits one. In `hasher.ode` that changes
  `hash` alone (nine instructions fewer), and both designs still agree with the crate on 8,154 inputs.
- two loads of a value the register still holds (the constant 1 after the comparison before; a buffer's
  address after the copy before): the compiler does not know what a register holds, as with `add`'s two
  and `ladd`'s one. Left.
So 111 became 107.

The audit of the 107 (from nothing, `../prove_all.sh` with `AUDIT=1`): 103 refused. Accepted: three moves of
a value the register still holds (the two above, and `mov rax, rbp` straight after `mov rbp, rax`). No
verdict in fifteen minutes for one: the jump after the AVX-512 kernel's call made a no-op, so that the
SSE4.1 kernel is called as well; an example refutes it (the root is wrong), the proof attempt did not end.
A changed program that the examples refute and Lean does not refuse within its time is counted as neither.

**Not done:** the contracts in bytes (`../spec/LevelsContract.lean`, in the same words) joined to these;
both functions on AArch64.

## The whole hash, proved: `hashl` (November 13)

`hash2` above has `ladd`'s and `lroot`'s text a second time, as macros, and calls the many-input kernels.
`hashl` is the whole hash another way: small functions, each one loop at most, each called by its contract
and by nothing else, one block at a time through the two one-block kernels (which are proved in `../one/`).
Slow, and every instruction of it under a theorem.

    hashl(out, input, len, key, flags, plat)        the whole hash
      chunk_node(nd, input, len, counter, flags, plat)   a chunk's node, as the specification has it
        pad(block, src, n)                               the last block, zero-padded
      node_out(out, nd, root, plat)                      a node's compression: its value, or the root's output
      ladd(lv, key, flags, plat, cv)                     a chunk's value added to the levels
      lroot(out, lv, key, flags, plat)                   the root of two chunks or more

**The theorem** (`../lang/Proof_hashl.lean`, written by the compiler; the contract is `../lang/Spec_hashl.lean`):

    hashl_meets : ∀ out input len key flags plat k bytes,
      Abi.Meets Code_hashl.prog 0x40000 (Hashl.contract out input len key flags plat k bytes)

For any message shorter than 2^64 - 1024 bytes, any key and any mode's flags below 256: with the message's
bytes at `input` and the key at `key`, the 32 bytes at `out` become the first eight words of the output of
the root of the specification's tree over the message's chunks (`Hash.words`: `Blake3.rootWords
(Blake3.tree k mode (Blake3.chunksOf k mode message))`); the message and the key are unchanged; nothing
else is written but the function's own stack, 4608 bytes at most. `Code_hashl.prog` holds every instruction
that can run: `hashl`'s 108, the five functions' 380 and the two kernels'.

And in the words a user reads (`../lang/Meets_hashl_bytes.lean`; `../spec/HashContract.lean` names no machine):

    hashl_meets_bytes : msg.length < 2 ^ 64 - 1024 →
      Abi.Meets Code_hashl.prog 0x40000 (Abi.ofBytes (Hash.byteContract out inp len key plat msg) 4608#64)

with the specification's IV at `key` and no flags, the 32 bytes at `out` become `Blake3.hashBytes msg`:
C2SP's `Blake3.hash` of the message.

| function | instructions | Lean's check | examples that meet its contract | each instruction made a no-op |
|---|---|---|---|---|
| `pad` | 39 | 14 to 22 s | 5 (and 2 refused as not examples) | 38 of 39 refused (36 by an example, 2 by the proof); 1 accepted |
| `node_out` | 58 | 158 to 164 s | 5 (2) | 56 of 58 (51, 5); 2 accepted |
| `chunk_node` | 81 | 121 to 186 s | 9 (2) | 81 of 81 (74, 7) |
| `ladd` | 95 | 194 to 233 s | 8 (1) | 94 of 95 (88, 6); 1 accepted |
| `lroot` | 107 | 269 to 406 s | 7 (1) | 104 of 107 (98, 6); 3 accepted |
| `hashl` | 108 | 342 s | 7 (1): 0 to 5120 bytes, both kernels, keyed | see `../prove_all.sh`'s `audit-hashl` |

The accepted ones are each a move of a value its register still holds (the compiler does not know what a
register holds).

What it took beyond `ladd` and `lroot`:
- **The node in memory is the specification's own** (`Blake3.Node`: `h`, the block, the counter, the block
  length, the flags; `../lang/Spec_node.lean`). `chunk_node`'s contract is `Blake3.chunkNode` word for word;
  whether the chunk is the root is decided where it is known, by `hashl`.
- **Three facts about the specification alone** (`../alg/Chunk.lean`, `../spec/HashBytes.lean`): a chunk's
  node is a fold over its blocks; BLAKE3's 32 bytes are the bytes of the root's first eight output words;
  `Blake3.hashBytes` is those bytes.
- **A message's bytes in memory are the words the specification reads** (`../lang/Lemmas_block.lean`), once,
  for every function that hashes bytes.
- **Bytes as a third kind of cell** (`../lang/Cells.lean`), for `pad`.
- **The generator** learned: calls and conditions after a loop; a callee that calls functions of ours; facts
  a call needs from a lemma named at it (`know`); a region kept across a call.

What it does not say: nothing about time or what an observer sees (no "quietly" theorem for the hash);
x86-64 only; one block at a time (the many-input kernels are not behind Lean contracts yet); the frame is
not on a boundary (the generator does not follow an aligned frame yet); the limits of everything here
(`bv_decide`'s axioms, the listing read by a disassembler and a script).

## The contracts in bytes (`../spec/LevelsContract.lean`; no theorem about these yet)

    ladd:  the levels over `chunks` become the levels over `chunks` and the new chunk
    lroot: the 32 bytes at `out` become the specification's output for the tree over `chunks`

What a reader of each design's contracts reads (`reading.py` on Lean's lists, `../lang/LevelsReading.lean`):

| | lines |
|---|---|
| the stack's three contracts (`push`, `merge`, `add`) | 186 |
| the levels' two (`ladd`, `lroot`) | 227 |
| read for both (the specification's compression, what a contract is, a value's bytes) | 137 |
| only the stack's (the three contracts 27, `mergeTo` and `Merge.merged` 13, the stack's layout 9) | 49 |
| only the levels' (the two contracts 19, the levels' layout 22, two words of `Contract` 4, **the specification's tree and output 45**) | 90 |

The 45 lines are the point: the levels' contracts say "the specification's tree"; the stack's say
"`mergeTo`". So the 186 and the 228 are not like for like. A reader who wants to know that the stack
makes BLAKE3's tree must also read the statement that says so (`Blake3.stack_is_the_tree`):

| to know "this makes the specification's tree" | lines |
|---|---|
| the stack's three contracts and `stack_is_the_tree` | 225 |
| the levels' two contracts | 227, of which 14 go further than the stack's (the root's output bytes) |

And on the stack's side two things are then still in no statement: that the caller passes the count's
one bits as `target` and holds back the last chunk, and the fold that makes the root (code inside
`hash`). Neither count matters to a reader of the user's contract once the whole hash is proved: that
reader reads `Hash.byteContract`'s list and no inner contract. These lines are what a maintainer or an
auditor of the part reads.

## What the two share, and what they do not

- **Shared whole:** the contract of the function a user calls (`Hash.byteContract`) and its trial; the
  kernels and their contracts; what a contract is; a chaining value's bytes; the machine and what
  meeting a contract means.
- **Not shared:** the data structure's layout (`Stack.Holds`, `Levels.Holds`), the contracts of the
  functions on it, and (not written for the levels) the algorithm's proof: `../alg/Stack.lean`'s 293
  lines are about the stack.
- **The proofs:** the table above. Writes that never land on what is still to be read did help: `ladd`'s
  lemma for a turn (`Levels.Mid.carry`) needs "every byte but the 32 written is as it was" and no more.

## A first form, and what it taught

The first form waited at every level, not only the bottom (commit 5ee78c4a). It agreed with BLAKE3 on
the same tests and ran as fast as the stack (42.6 ns a value), but its root needed three cases a level
(a pair, a pair joined by a parent from below, a value left over): `lroot` 272 instructions against 157,
and the only part of either form I had to check against a model before I believed it. Waiting at the
bottom alone is enough for the reason to wait: a pair is known not to be the root's as soon as any
later value exists.

## Again

    bash run_levels.sh CRATE_DIR WORK_DIR   # model, assemble both designs, agree, time, count (x86-64)
    bash try_hash2.sh                        # hash2 against Hash.byteContract
