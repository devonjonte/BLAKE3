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

3520 bytes against the stack's 1792.

## Tried (Threadripper 7975WX; single runs: inventory, no speed verdict)

| | |
|---|---|
| `model.py`: the design against the specification's tree | every count of chunks from 2 to 3000 |
| `ladd`, `lroot` as assembled, against the tree (the crate's kernel) | 2,455 roots: every count to 700, others to 5000; three modes |
| `hash2` (the whole hash on the levels) against the crate | 8,154 inputs agree |
| `hash2` against **`Hash.byteContract`, the stack hash's contract, unchanged** (`try_hash2.sh`) | 105 examples meet it, 0 do not; the control holds on 105 |

| | the stack | the levels |
|---|---|---|
| a value added, and the root at the end (1024 values) | 42.5 ns a value | 40.1 ns (-5.6%) |
| the hash of 2 KiB, 4 KiB, 16 KiB, 32 KiB | 728, 982, 2,210, 4,483 ns | 726, 976, 2,163, 4,406 ns (-0.3% to -2.2%) |
| copies of 32 bytes a parent | 4, and two scratch buffers | 1 (the key), no scratch |
| instructions | `push` 27, `merge` 89; the root's fold is inside `hash` | `ladd` 121, `lroot` 157 |
| the caller | holds back the last chunk; computes `target` | adds every value; asks for the root |

(`hash2` is 630 instructions against `hash`'s 815, but it has no 32-chunk path: not a comparison.)

## The contracts (`../spec/LevelsContract.lean`; no theorem yet)

    ladd:  the levels over `chunks` become the levels over `chunks` and the new chunk
    lroot: the 32 bytes at `out` become the specification's output for the tree over `chunks`

What a reader of each design's contracts reads (`reading.py` on Lean's lists, `../lang/LevelsReading.lean`):

| | lines |
|---|---|
| the stack's three contracts (`push`, `merge`, `add`) | 186 |
| the levels' two (`ladd`, `lroot`) | 228 |
| read for both (the specification's compression, what a contract is, a value's bytes) | 137 |
| only the stack's (the three contracts 27, `mergeTo` and `Merge.merged` 13, the stack's layout 9) | 49 |
| only the levels' (the two contracts 19, the levels' layout and counts 23, two words of `Contract` 4, **the specification's tree and output 45**) | 91 |

The 45 lines are the point: the levels' contracts say "the specification's tree"; the stack's say
"`mergeTo`", and that the stack makes the tree is other theorems (`stack_is_the_tree`,
`Add.keeps_the_tree`: 139 lines to read on their own) and the caller's business.

## What the two share, and what they do not

- **Shared whole:** the contract of the function a user calls (`Hash.byteContract`) and its trial; the
  kernels and their contracts; what a contract is; a chaining value's bytes; the machine and what
  meeting a contract means.
- **Not shared:** the data structure's layout (`Stack.Holds`, `Levels.Holds`), the contracts of the
  functions on it, and (not written for the levels) the algorithm's proof: `../alg/Stack.lean`'s 293
  lines are about the stack.
- **Not known yet:** what the proofs cost. `ladd` has a loop that calls a kernel, as `merge` has; whether
  disjoint writes make its proof shorter is the next thing to measure.

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
