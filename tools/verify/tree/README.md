# Proofs of the tree walk

BLAKE3 hashes an input as a binary tree over its 1024-byte chunks. These
proofs show, in Lean, that the library's tree walk and the Hasher's stack,
both safe Rust, compute the tree of the C2SP specification
(`c2sp/BLAKE3/Blake3.lean`) for every input:

    AENEAS=/path/to/aeneas sh tools/verify/tree/check.sh

The walk is `src/tree_core.rs`, which the library runs and `rust/widecore`
includes as it is. It calls its kernels in batches: up to `degree()`
chunks per call, a layer of parents per call, and SME2's whole-subtree
kernel where it applies. Aeneas translates each crate to Lean
(`Widecore.lean`, `Hashercore.lean`; `check.sh` translates them again and
checks the committed files are the translations), and `check.sh` proves
the walk at every buffer size the library builds with
(MAX_SIMD_DEGREE_OR_2: 128, 16, 8, 4, 2). The walk's proofs are in
`WideProofs.lean`, `ChildrenProofs.lean`, and `HashProofs.lean`, on lemmas in
`Proofs.lean`:

- **`WideBridge.wide_is_tree`.** For every nonempty input whose chunk
  count fits in 64 bits, `wide` returns without panicking or overflowing.
  Under an abstraction `abs` of chaining values, the specification's tree
  over the values it returns is the specification's tree over the input's
  chunks. Kernels of any power-of-two degree up to 128 qualify.
- **`ChildrenProof.children_spec`.** `children` (the walk, then a layer of
  parents at a time until two values are left: the library's
  `condense_subtree`) returns the chaining values of two of the
  specification's nodes whose parent is the specification's tree node over
  the input's chunks; for a whole input, `goIdx_leafN_root` shows that node
  is `Blake3.tree`'s root. The proof follows the walk's values as nodes
  (`ChildrenProofs.lean`).
- **`HashProof.hash_spec`.** `hash` (`tree_core.rs`; the library's
  one-shot `hash`, `keyed_hash`, and `derive_key` call it) returns
  `Blake3.blake3 key mode input 32`, the specification's 32-byte output,
  for every input whose chunk count fits in 64 bits. Its hypotheses are the
  kernels' contracts, stated with the specification's own functions:
  `chunk_root` returns the output of the input's only chunk node,
  `parent_root` the output of the parent node of the two chaining values,
  and the SME2 `children` hook, where it answers, the root's children
  (`HashProofs.lean`).
- **`HasherCoreProof.hasher_spec`.** The Hasher's loop (`src/hasher_core.rs`:
  `fill`, `feed`, and `final_node`, over the stack of `src/stack_core.rs`;
  `hashercore` includes both): from a new Hasher, after any updates, the
  root's node is the specification's root over all the updates' bytes,
  whose 32-byte output is `Blake3.blake3 key mode` of them. Its hypotheses
  are the kernels' contracts (`Contracts`, `NodeContracts`), each stated
  through relations: a chunk state stands for its number and its bytes,
  a node for the specification's node. Between updates the stack
  holds the chaining values of `HasherProof.stackCvs` over the full chunks,
  merged while a chunk is partly filled, and else perhaps with one subtree
  on top not yet merged (`HInv`; `HasherCoreProofs.lean`). `update` there is
  the library's `update_pooled`: `fill`, then `feed` when input is left.
- **`ChunkProof.absorb_spec`, `node_eq`.** A chunk's state
  (`src/chunk_core.rs`, the library's `ChunkState`; `rust/hashercore`
  includes it too): after any bytes `B`, its fields are the specification's chunk node of
  `B` (`node_eq`): the chaining value after the blocks before the last, the
  last block (zero past its length) in `buf`, never empty once a byte has
  come (`CInv`; `new_spec`, `absorb_spec`). Its hypotheses are the
  compression kernels' contracts (`BlocksContracts`: `compress_in_place`
  and `compress_blocks`, stated with the specification's compression
  function; `ChunkProofs.lean`). As the Hasher's chunk (`inst_counter`,
  `inst_len`, `inst_update`, `inst_advance`), it meets the chunk contracts
  of `HasherCoreProof.Contracts`, read through the relation `Rel` (a state
  stands for its chunk's number and bytes).
- **`OutputProof.hasher_hash`.** The Hasher on the library's kernels
  (`Kernels` in `src/hasher_core.rs`; `Output`, a node's last compression,
  in `src/chunk_core.rs`): a new chunk state, any updates, the root's node,
  and its first 32 bytes are `Blake3.blake3 key mode` of the updates'
  bytes. `Kernels` meets the Hasher's contracts (`kernels_contracts`,
  `kernels_node_contracts`), given compression kernels that meet
  `BlocksContracts` and hooks (the pool and SME2 routes, the bit count, the
  subtree length) that meet `HookContracts`. On the way: a node's chaining
  value and root bytes are the specification's (`cv_spec`, `root_spec`), and
  so are the nodes of a chunk and of a parent (`chunk_output_spec`,
  `parent_output_spec`); the bytes of words are the specification's
  `bytesLE` (`le_bytes_spec`).

Each rests on Lean's three standard axioms (`propext`, `Classical.choice`,
`Quot.sound`), printed at the end of each file; `check.sh` fails on any
other.

**The kernels' contracts are the hypotheses.** `chunks` must return, in
order, the specification's chaining values of its chunks. `parents` must
return one layer of parents, with an odd last child passed through. The
assembly kernels' proofs (`tools/verify/prove_*.py`) establish exactly
these properties of the machine code, against the same specification's
compression function.

**The steps of the proof:**

1. `wide_spec` shows that `wide` returns the list `wideI`, a model of the
   walk over chunk indexes. The proof includes every buffer's size and the
   fact that the left half fills its buffer exactly: the slice
   `cvs[..ln + rn]` relies on it.
2. `wideI_spec` shows that the tree over `wideI`'s values is the tree over
   the chunks. Its key fact is `treeL_layerL`: the specification's tree over
   one layer of parents is its tree over the layer below.
3. `walk_eq_goIdx` and `walk_is_tree` connect a binary walk over bytes,
   a Lean function, to the specification's `tree` over its `ByteArray`
   chunks.

**The Hasher's stack** (`HasherProofs.lean`, the algorithm, and
`StackProofs.lean`, the code: `src/stack_core.rs`, included as it is by
`rust/hashercore`, whose `push` and `merge` are proved to compute the
algorithm's, never failing on a stack of at most 55 values). After
the first c chunks the stack holds one chaining value per 1-bit of c, the
tree over the aligned power-of-two block it stands for (`stackCvs`):

- `merge_push`: `push_cv` keeps this. After the block of 2^k chunks at
  chunk c (2^k dividing c) goes on top, `merge_cv_stack` merging to the
  1-bits of c + 2^k leaves the stack of c + 2^k.
- `final_output_whole`, `final_output_partial`: `final_output`'s fold of
  the stack onto its top (or onto a partial last chunk) is the
  specification's tree over all the chunks.

**Toolchain.** Aeneas `nightly-2026.10.07-aa66752`, Lean 4.31.0 (Aeneas's;
`Blake3.lean` builds unchanged under it), Rust `nightly-2026-09-17`.
