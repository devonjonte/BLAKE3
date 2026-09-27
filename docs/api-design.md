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
| many messages of one length | an index of records, a layer of a tree | `hash_many_multithreaded` (recommended), or `hash_many` |
| one long input arriving in pieces, simply | a reader, a decompressor | `Hasher::update`, `update_reader` |
| one long input arriving in pieces, top speed | a file server, a backup tool | `Queue::pieces` |
| many separate inputs arriving, top speed | a content-addressed store, per-object digests over a network | `Queue` (below) |
| authenticated or derived | a MAC, a per-tenant key, a KDF | the keyed and derive-key form of each shape |
| saving energy, seriously | a laptop on battery, a fleet billed for power | the queue, efficient in energy |
| saving energy, casually | background work | the single-threaded forms, at background priority |

The one-shot forms and `Hasher` are built for ease of use; the queue is
built for efficiency, in time or in energy, chosen per queue
(`Efficiency::Time` or `Efficiency::Energy`).

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
energy-efficient form (`Efficiency::Energy`); the `efficient` module idea in NEXT-STEPS
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

Decided with Zooko (September 27, 2026): Merkle trees are out for now;
the engine is one per process and a queue is a handle onto it; the queue
takes its shape; results arrive as calls to a handler the user
implements, from one delivery thread; no polling and no blocking.

- **The engine**: the process-wide singleton (one pool, its hashing
  threads, the SME2 unit's turn, and one delivery thread). It starts with
  the first queue, or earlier with `initialize_multithreaded()`; the user
  never makes or configures it. (The user keeps competing processes off
  the machine if that matters to him.)
- **A queue**: a cheap handle for one stream of work, made for one shape,
  holding its mode and key, its efficiency choice (`Efficiency::Time`:
  every core; `Efficiency::Energy`: one thread, the E-core-friendly way),
  its message in progress, and its handler. A program with streams of
  several shapes, or on several threads, makes a queue each; the engine
  serves the queues in turn.
- **Buffers pass by ownership**, as Rust's io_uring libraries do: the
  program cycles a fixed set of buffers (fill one, for a file or socket by
  the `read` itself; submit it; get it back in a handler call; fill it
  again). No copy, no allocation per input. `submit` returns at once.
- **Back-pressure is the program's own buffers**: every buffer comes back
  through the handler, so the buffers in flight never exceed the number
  the program made; a program out of buffers waits for its next handler
  call, as an io_uring program waits for its next completion.

The three shapes, each with its handler trait (one set of calls resolved
at compile time: `Queue<H>`):

```rust
pub trait MessageHandler: Send + 'static {        // messages of any length, one per buffer
    type Buffer: AsRef<[u8]> + Send + 'static;
    fn hashed(&mut self, buffer: Self::Buffer, hash: Hash);
}
pub trait PieceHandler: Send + 'static {          // one long message in pieces
    type Buffer: AsRef<[u8]> + Send + 'static;
    fn piece_done(&mut self, buffer: Self::Buffer);
    fn finished(&mut self, hash: Hash);
}
pub trait FixedHandler: Send + 'static {          // messages of one length, back to back
    type Buffer: AsRef<[u8]> + Send + 'static;
    type Digests: AsMut<[[u8; 32]]> + Send + 'static;
    fn hashed(&mut self, buffer: Self::Buffer, digests: Self::Digests);
}

let queue = Queue::messages(Mode::Hash, Efficiency::Time, handler);
queue.submit(buffer);
let queue = Queue::pieces(Mode::Hash, Efficiency::Time, handler);
queue.submit(piece);                    // in order; queue.finish() ends the message
let queue = Queue::fixed(64, Mode::Hash, Efficiency::Time, handler);
queue.submit(buffer, digests);          // the digests' space is the caller's too, returned with the buffer
```

The handler contract:

1. **Short, never blocking**: a slow handler delays the delivery of every
   queue's results; heavy work goes to the program's own threads.
2. **Order and exclusion**: a queue's handler is called in submission
   order, one call at a time (so `&mut self`, no locking).
3. **Calling back in**: `submit` from inside a handler is allowed (refill
   and resubmit is the natural cycle); it never waits on the engine.
4. **A panic in a handler aborts the process** (fail stop; a panic cannot
   unwind through the engine's threads safely).
5. **Dropping a queue cancels nothing**: buffers in flight are still
   hashed and returned through the handler, which the engine keeps alive
   until its last call; a handler never finished stays alive until the
   process ends. Buffers always come back; nothing drops them silently.

- **Delivery**: one delivery thread per engine takes results as the
  hashing threads finish them, in any order, and calls each queue's
  handler in submission order; hashing threads never run user code. It
  sleeps when there is nothing to deliver, so a wake (about 3 µs on the
  Mac) falls once per burst of results. Direct delivery from the hashing
  threads is worth measuring against it later.
- **Shared buffers**: an `Arc<[u8]>` submitted to us and to a writer at
  once serves both without a copy; it returns to its pool when the last
  user lets go.
- **Inside**: the engine's hashing threads keep the pool in the call while
  inputs wait; inputs waiting together batch through `hash_many`'s
  kernels; large ones split over the pool from 768 KiB. The handoffs are
  lock-free rings of descriptors, a futex wake only when a side sleeps.

**io_uring, as an optional Linux layer.** A read's completion hands its
buffer to the queue; a handler that posts into the program's own ring
(`IORING_OP_MSG_RING`, Linux 5.18) makes one `io_uring_wait` cover disk,
network, and hashing; digests written into a program's buffer go out as a
send.

**Chaining.** Any stage that passes buffers by ownership chains to the
queue: a compressor's output buffer becomes the hasher's input.

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
| one input in pieces | the input arriving in 64 KiB pieces from a producer that copies them in (as a read would) | every hash's incremental API; servil through `Hasher` and the queue |
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
