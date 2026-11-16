# Removing `hazmat`: what is left, and what each piece needs

A proposal (November 16, 2026), for Zooko to decide the names and the
order. `docs/tree-api.md` was layer 1 and is landed: `throughput::TreeHasher`,
`Cv`, `left_len`. This is the rest.

`blake3_servil_core::hazmat` is hidden (`#[doc(hidden)]`) and has one user,
the threads crate (`threads/`). It exists because that crate carries a
message's mode as a bare `(key, flags)` pair and names the kernels'
`Platform` itself. Nothing outside the two crates may use it, and the two
are released together, so it can change at will; the reason to remove it
is that a second implementation of a pool (Bao, iroh, anyone's) should be
able to do what ours does through the public API, and today cannot.

## What `threads/` takes from it

| From `hazmat` | Uses in `threads/src` | What it is for | Public replacement |
|---|---|---|---|
| `hash_all_at_once(..).chaining_value()` | 6 | a piece's subtree, off the root | `TreeHasher::subtree_cv` (landed) |
| `compress_subtree_to_parent_node` | 5 | a message's first piece, as its two halves | `TreeHasher::subtree_halves` (landed) |
| `compress_parents_parallel` | 2 | a layer of parents | `TreeHasher::parent_cvs` (landed) |
| `hasher::parent_output(..).root_hash()` | 3 | the root from two values | `TreeHasher::root_hash`, `root_output` (landed) |
| `tree::left_len` | 3 | where a message's left subtree ends | `throughput::left_len` (landed) |
| `hash_serial`, `hash_serial_on` | 8 | a whole message on one thread, the mode as `(key, flags)` | **new A** |
| `hash_many_serial`, `many::hash_many_on`, `many::slot_len`, `assert_slots` | 12 | a batch of messages on one thread | **new B** |
| `each::{hash_each_on, Item, MEMBERS, prepare_thread}` | about 8 | a collection of messages of any lengths, side by side | **new B** |
| `each::update_turn`, `incremental::Pool` | about 4 | many Hashers fed in one turn; a Hasher that hands large updates to a pool | **new C** |
| `platform::{Platform, Sme2Turn, MAX_SIMD_DEGREE}` | 18 and more | which kernels a thread runs, and the one SME2 unit's turn (Apple) | **new D** |
| `IV`, the flag constants, `CVWords`, `CVBytes`, `Output` | about 75 | the `(key, flags)` pair itself, and tests | gone with A |

## The four new pieces

**A. A mode, prepared once.** `TreeHasher` already holds what a mode comes
to (the key words and flags; for key derivation, the context's key, which
costs a hash to make). The threads crate would carry a `TreeHasher` where
it carries `(key, flags, platform)` today, and needs from it one more
call: the hash of a whole message.

    impl TreeHasher {
        pub fn hash(&self, input: &[u8]) -> Hash;      // name to decide
    }

It is useful outside the pool too: a program that hashes many messages
under one derive-key context pays for the context once. Question: is this
`TreeHasher`'s to have, or does it want a name of its own (a prepared
`Mode`)? `convenience::hash_with(mode, ..)` takes a `Mode` each call.

**B. Batches and collections on the calling thread.** The public
`throughput::hash_many` and `hash_each` exist; what the pool needs is the
same two for a part of a batch, in a prepared mode, with the output
slots it names. Probably two methods beside A's, taking the same
arguments the public functions take. `MEMBERS` (64, how many messages a
task holds) is the pool's own number and can live there.

**C. A Hasher that lends its large updates.** `incremental::Pool` is a
function pointer the multithreaded `update` passes down so that an update
of several megabytes is cut and hashed by the pool. The public form is the
hook Rüdiger asked about on #378: a `Hasher::update_with`-style call that
takes "hash these subtrees for me" from the caller. `each::update_turn`
(many Hashers, one piece each, side by side) needs the same hook.

**D. Which kernels, and the SME2 unit's turn.** On every machine but
Apple's SME2 ones, a thread runs the detected kernels and there is nothing
to choose. On those, one SME2 unit serves all cores: pool pieces run the
NEON kernels (`TreeHasher::on_this_core`, landed), and one thread at a time
takes the unit (`Sme2Turn`). The turn is the one item with no public shape
yet. Two ways: (1) keep it inside the core crate entirely, so that a call
"on the unit if it is free" is something `TreeHasher` decides and no
caller names; (2) publish the turn as a guard type. (1) is less surface
and I would try it first; it needs measurements on the Mac, which has
returned no verdict since November 14 (ops #14).

## Order I would take

1. The five landed replacements, in `threads/` (mechanical once A exists,
   since the call sites hold `(key, flags)`): no new surface beyond A.
2. A, then B: each removes a group of `hazmat` names and can be checked on
   the x86 machines and the Arm VM alone (the code Apple runs for them is
   the same NEON path).
3. C, with Rüdiger's use as the test of its shape.
4. D last, when the Mac measures again.

After 1 and 2, `hazmat` holds C's and D's names only.

## What I need decided

- A's name and home (a method on `TreeHasher`, or a prepared-mode type).
- Whether B's calls are methods beside A's.
- For D, whether to try keeping the turn wholly inside the core crate.
