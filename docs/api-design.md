# The servil API plan, and the benchmark that holds us to it

For Zooko and John Servil. A draft for Zooko's review (September 27,
2026). Once approved, it is encoded into bench-hashes and frozen (the last
section), and this file records why each choice was made. Decisions
already made carry their date; everything else is a proposal, and each
open question is marked **Q**.

**The strategy** (Zooko, September 27, 2026; AGENTS.md, "The streaming
APIs first"): the users most sensitive to performance, for time or for
energy, use the streaming APIs, so every trade-off goes to them, even at a
cost to the other APIs; choosing the efficient API is the caller's job.
The streaming APIs are **built for efficiency**; every other API is
**built for ease of use** (the API docs' labels, decided).

## Users and what they call

| user | use case | calls |
|---|---|---|
| one buffer in memory, other latencies around it | a file already read, a message received | `hash_multithreaded` (recommended), or `hash` |
| many messages of one length | a Merkle layer, an index of records | `hash_many_multithreaded` (recommended), or `hash_many` |
| one long input arriving in pieces, simply | a reader, a decompressor | `Hasher::update`, `update_reader` |
| one long input arriving in pieces, top speed | a file server, a backup tool | `Queue` in one-input form (below) |
| many separate inputs arriving, top speed | a content-addressed store, per-object digests over a network | `Queue` (below) |
| authenticated or derived | a MAC, a per-tenant key, a KDF | the keyed and derive-key form of each shape |
| saving energy, seriously | a laptop on battery, a fleet billed for power | the queue, efficient in energy |
| saving energy, casually | background work | the single-threaded forms, at background priority |

The one-shot forms and `Hasher` are built for ease of use; the queue is
built for efficiency. **Q1 (new)**: efficiency in time or in energy, both
supported; how the queue takes the choice (a boolean at construction, or
the thread choice itself: all cores for time, one E-core-friendly thread
for energy).

## Dimensions

**Threads** (settled for one-shot forms, September 27). Each one-shot
shape has a single-threaded form (`hash`, `hash_many`), a multithreaded
form the docs recommend (never slower; leaves the caller's thread from
768 KiB in all), and a form with a thread budget (`..._with_budget`,
counting the caller). The queue takes the same choice at construction.

**Energy against time.** Single-threaded spends the least energy per byte
(the M4 Max: multithreaded calls about 2.7x per byte; E-cores about an
eighth of P-cores' energy at a third to a quarter of the speed). The docs
of every multithreaded form say so beside the recommendation; the crate
docs keep the advice to hash single-threaded at background priority when
time allows. Users serious about energy use the queue in its
energy-efficient form (Q1); the `efficient` module idea in NEXT-STEPS
(SME2 on the caller, E-core helpers at background QoS) is how that form
might run.

**Modes.** Every shape serves plain hashing, keyed hashing, and key
derivation; they differ only in the key words and flags, so they cost the
same. Upstream names one-message modes by function (`keyed_hash`,
`derive_key`) and incremental ones by constructor (`Hasher::new_keyed`,
`Hasher::new_derive_key`). Across three modes, two shapes, and three
thread forms, a function per combination makes 18 one-shot functions.
Proposal: keep upstream's one-message functions, and give every other
shape the mode through its constructor or one argument:

```rust
pub enum Mode<'a> { Hash, Keyed(&'a [u8; 32]), DeriveKey(&'a str) }
pub fn hash_many_with(mode: Mode, input: &[u8], message_len: usize, out: &mut [[u8; 32]]);
pub fn hash_many_multithreaded_with(mode: Mode, input: &[u8], message_len: usize, out: &mut [[u8; 32]], max_threads: usize);
pub fn hash_multithreaded_with(mode: Mode, input: &[u8], max_threads: usize) -> Hash;
Queue::new(mode, threads)
```

`Mode` it is (Zooko, September 27, 2026): one concept with a default, so
a user who wants plain hashing never meets it. Proposal to go with it: the
thread choice as one argument too, `Threads::{One, All, Budget(n)}`, so
each shape has its two easy functions and one full one:
`hash`, `hash_multithreaded`, `hash_with(mode, threads, input)`;
`hash_many`, `hash_many_multithreaded`, `hash_many_with(mode, threads,
input, message_len, out)`; upstream's `keyed_hash` and `derive_key` stay
for drop-in use; the `..._with_budget` functions go.

**Signatures.** One style throughout: inputs as `&[u8]` (one-shot) or
owned buffers (queue); a one-message digest as `Hash` (its equality runs
in constant time); batch digests as `&mut [[u8; 32]]`, filled in order (a
batch usually feeds the next tree layer); counts and budgets as `usize`;
contract violations panic with a message naming the rule broken.

**Initialization** (settled, September 27). `initialize()` runs the
startup self-test (under 200 µs on an M4 Max);
`initialize_multithreaded()` also starts the pool (under 1 ms). The docs
of `hash` and `hash_multithreaded` say calling them early keeps those
costs off the first call. `initialize()` changing meaning is a minor
version bump with a changelog entry.

## The batch contract (settled, September 26)

Message i starts at byte i x s, s being `message_len` rounded up to a
multiple of 64 (64 for an empty message); the caller zeroes the bytes
between one message's end and the next one's start; any message length.

## The queue: streaming without copies

The core interface passes buffers by ownership, as Rust's io_uring
libraries do. The program keeps a fixed set of buffers and cycles them:
fill one (for a file or socket, the `read` itself), submit it, get it back
with its digest, fill it again. No copy, no allocation per input, one
handoff per buffer.

```rust
let mut queue = Queue::new(Mode::Hash, Threads::All);
queue.submit(buffer);                     // T: AsRef<[u8]> + Send + 'static; blocks while the budget is full
queue.try_submit(buffer)?;                // or returns the buffer at once when full
while let Some((buffer, hash)) = queue.ready() { /* in submission order */ }
for (buffer, hash) in queue.finish() { /* the rest */ }
```

- **Budget** (the back-pressure): bytes in flight, a few MiB by default.
- **The streaming shapes**: (a) one message of any length after another,
  each with its digest; (b) a long or endless series of fixed-length
  messages, batched; (c) one long message in pieces (a file), one digest
  for all of them; (d) a Merkle tree over a series of leaves. **Q3**
  (restated): one queue type whose constructor names the shape, or a type
  per shape? (a) and (b) differ only in what the queue may batch; (c)
  returns one digest; (d) returns a root and, if wanted, the layers.
- **Shared buffers**: an `Arc<[u8]>` submitted to us and to a writer at
  once serves both without a copy; it returns to its pool when the last
  user lets go.
- **Inside**: one hashing thread per queue, holding the pool while inputs
  wait (a `lanes::Hold`, as `Stream` does since 3d7102e); inputs waiting
  together batch through `hash_many`'s kernels; large ones split over the
  pool from 768 KiB. The handoff is a lock-free ring of descriptors, a
  futex wake only when a side sleeps.
- `Stream` is deleted for now (Zooko, September 27, 2026), so nothing
  distracts from the plan until the benchmark is frozen; a copying helper
  may come back after that.

**io_uring, as an optional Linux layer.** A read's completion hands its
buffer to the queue; the queue's completions post into the program's own
ring (`IORING_OP_MSG_RING`, Linux 5.18), so one `io_uring_wait` covers
disk, network, and hashing; digests written into a program's buffer go
out as a send. Elsewhere completions wake a condition variable (macOS: a
kqueue event on request).

**Chaining.** Any stage that passes buffers by ownership chains to the
queue: a compressor's output buffer becomes the hasher's input.

**A Merkle tree as a worked example.** Leaves go in as one queue's
inputs; their digests land back to back in a buffer, each pair of
children already one 64-byte message, which a second stage hashes with
`hash_many(…, 64)`. Each node layer is half the one below, so all node
layers together cost about one layer of 64-byte messages: two stages
(leaves, then every node layer), or node layers fused into the leaf stage
while the digests are in cache, chosen by measurement. The `merkle`
module idea (NEXT-STEPS) builds on this.

## How the benchmark measures each

Two scenarios for every shape (settled, September 27): **back to back**
(perf_regress holds at 3%: small kernel regressions) and **after idle**
(20%: the wake path and cold starts, which back to back cannot see; its
CHECKS compare within one clock state). No warm-start gap scenario. The
graph plots back to back only; after idle and everything else sit behind
a door.

| shape | use case in the benchmark | contenders |
|---|---|---|
| one-shot one message | one input at a time, 64 B-128 MiB | every hash; servil st and mt |
| one-shot batch | batches of 64-byte messages, 1-262144 | BLAKE3 official (`Platform::hash_many`, sixteen a call), SHA-256s one call each; servil st and mt |
| one input in pieces | the input arriving in 64 KiB pieces from a producer that copies them in (as a read would) | every hash's incremental API; servil through `Hasher` and the queue's one-input shape |
| many inputs | new: a producer handing over N inputs of one size in turn from a fixed set of buffers, digests collected as they come, timed end to end | every hash in a loop; servil through the queue |
| modes | keyed and derive-key spot checks at a few sizes in perf_regress (same cost as plain; a check that it stays so), no graph axis | servil |
| energy | a maintainers' probe (probe/energy), outside the benchmark: joules per byte by form | servil |

perf_regress's points gain the 4- and 12-message batches.

## Encoding it into the benchmark, and freezing it

Once Zooko approves this plan:

1. bench-hashes calls exactly the interfaces above in exactly these
   usage patterns. Interfaces not built yet get a first, simple, correct
   version in the fork (the queue as a loop over `hash` behind the
   planned signatures), so the benchmark measures the plan from day one
   and the work is making it fast.
2. **The freeze**: a manifest in bench-hashes (`FROZEN.md`) lists every
   use case, the servil call it makes, its usage pattern, its points, and
   its scenarios, each with the reason and the decision's date; a test
   derives the same list from the code and fails when they differ. A
   change to what the benchmark asks of servil therefore needs an edit of
   the manifest, which carries Zooko's decision and its reason. AGENTS.md
   says so: the benchmark is the contract; the fork's work is to be fast
   under it.
3. This file stays as the record of why.
