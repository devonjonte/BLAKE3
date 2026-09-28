# The servil API plan, and the benchmark that holds us to it

For Zooko and John Servil. A draft for Zooko's review (September 28,
2026). Once approved, it is encoded into bench-hashes and frozen (the last
section). Decisions carry their date; everything else is a proposal, and
each open question is marked **Q**.

## Four questions lead a user to one call

The crate docs open as a choose-your-own-adventure (Zooko, September 28,
2026), so a reader learns that the streaming and batch calls exist before
reaching for a loop over `hash`:

1. **Can your program use several threads?** A program that cannot gets
   the single-threaded calls, built to save time under intermittent use,
   and answers question 2 alone; the docs say that saving energy, and the
   best speed for a continuous load, take several threads.
2. **What shape is your data?**
   - *A message in one buffer*: all in memory.
   - *A message arriving in pieces*.
   - *A batch*: many messages of one length, all in memory.
3. **(Several threads only.) Do you want to save time or energy?**
4. **(Several threads only.) When you finish hashing a message, will
   there typically be another message already ready to be hashed?**
   - *No, the program goes off and does other things*: intermittent, a
     synchronous call; its one-time cost (latency) matters.
   - *Yes, one after another as fast as possible*: continuous, the queue;
     the repeated cost (throughput) matters.
   A user who cannot tell answers no; the synchronous call is never far
   wrong, and the queue pays only with enough work in flight. (To be
   revisited once both are implemented, benchmarked, and optimised.)

The answers lead to nine calls:

| shape | single-threaded (intermittent) | several threads, intermittent | several threads, continuous |
|---|---|---|---|
| message in one buffer | `hash` | `hash_multithreaded` | the queue, one message per buffer |
| message in pieces | `Hasher::update`, then `finalize` | `update_multithreaded`, then `finalize` | the queue, pieces |
| batch | `hash_many` | `hash_many_multithreaded` | the queue, messages of one length (`Queue::fixed`) |

The queue offers the same three shapes as question 2, so each answer
leads to one obvious call; how the engine shares work between them stays
inside.

**Time or energy.** Each queue takes the choice as an argument
(`Efficiency::Time` or `Efficiency::Energy`); the multithreaded
synchronous calls take it too. Single-threaded calls always save time
(Zooko, September 28, 2026).
- **Q**: what saving energy means for a multithreaded synchronous call. A
  call with the caller on SME2 and E-core NEON helpers at background QoS
  hashed 8 MiB 10-27% faster than `hash` for a third less energy
  (NEXT-STEPS, "the `efficient` module").

**No thread budget** (Zooko, September 28, 2026): the `..._with_budget`
functions and `Threads::Budget` go.

**`hash` keeps its name** (Zooko, September 28, 2026): a message in one
buffer, intermittent, is likely the most common case, and `hash` and
`hash_multithreaded` are its natural names. The crate docs lead with the
questions above, so a reader meets the other shapes first.

- **Q**: the multithreaded `Hasher` form's name (`update_multithreaded`
  is a placeholder).

## The synchronous calls

Each call returns its result; nothing keeps running for a call that may
come (AGENTS.md, "Serve real programs"), with one exception:

**A `Hasher` between `update` and `finalize` may linger** (Zooko,
September 28, 2026): a message in progress promises more updates, and
they usually come in swift succession, so the multithreaded form keeps
its workers ready between them.
- **Q**: a bound on lingering. A program that keeps a `Hasher` open for a
  long time (one per network connection, say) must not keep workers
  spinning; a proposal is to linger for a fixed, measured time after each
  update and then sleep.

**Initialization** (settled, September 27). `initialize()` runs the
startup self-test (under 200 µs on an M4 Max);
`initialize_multithreaded()` also starts the pool (under 1 ms). The docs
of `hash` and `hash_multithreaded` say calling them early keeps those
costs off the first call. `initialize()` changing meaning is a minor
version bump with a changelog entry.

**The batch contract** (settled, September 26). Message i starts at byte
i x s, s being `message_len` rounded up to a multiple of 64 (64 for an
empty message); the caller zeroes the bytes between one message's end and
the next one's start; any message length.

## The queue

The queue maximises throughput: bytes or messages hashed per second, or
per joule, by a program that keeps the engine fed. It spends latency to
buy throughput. What it owes is that handovers never slow the hashing
threads, so its throughput is the hashing's, for a program that keeps
enough in flight (Little's law: in flight = rate x round trip).

Its requirements (Zooko, September 27-28, 2026):
- **Event-based, through traits**: results arrive as calls to a handler
  the user implements; no polling and no blocking. `submit` returns at
  once.
- **Zero copying**: buffers pass by ownership, as Rust's io_uring
  libraries do. The program cycles a fixed set of buffers (fill one, for
  a file or socket by the `read` itself; submit it; get it back in a
  handler call; fill it again).
- **Zero dynamic allocation** after warm-up (`tests/queue_no_alloc.rs`
  holds it).
- **Always multithreaded**, efficient in time or in energy per queue.

The engine and its queues (decided September 27, 2026):
- **The engine** is one per process: the pool, its hashing threads, the
  SME2 unit's turn, and one delivery thread. It starts with the first
  queue, or earlier with `initialize_multithreaded()`; the user never
  makes or configures it.
- **A queue** is a cheap handle for one stream of work, made for one
  shape, holding its mode and key, its efficiency choice, its message in
  progress, and its handler. A program with streams of several shapes, or
  on several threads, makes a queue each; the engine serves them in turn.
- **`submit` takes `&self`**: a handler may hold its own queue (through an
  `Arc`) and submit from inside its call; a queue is `Send + Sync`.
- **Back-pressure is the program's own buffers**: every buffer comes back
  through the handler, so the buffers in flight never exceed the number
  the program made.

The shapes, each with its handler trait (resolved at compile time:
`Queue<H>`):

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
3. **Calling back in**: `submit` from inside a handler is allowed; it
   never waits on the engine.
4. **A panic in a handler aborts the process** (fail stop).
5. **Dropping a queue cancels nothing**: buffers in flight are still
   hashed and returned through the handler, which the engine keeps alive
   until its last call.

**Later, optional**: an io_uring layer on Linux (a read's completion
hands its buffer to the queue; a handler posts into the program's ring
with `IORING_OP_MSG_RING`), and chaining (a compressor's output buffer
becomes the hasher's input). Merkle trees are out for now.

## Everything else, in every call

**Modes** (settled, September 27). Every call serves plain hashing, keyed
hashing, and key derivation through one argument with a default, so a
user who wants plain hashing never meets it:

```rust
pub enum Mode<'a> { Hash, Keyed(&'a [u8; 32]), DeriveKey(&'a str) }
```

Upstream's `keyed_hash` and `derive_key` stay for drop-in use.

**Signatures.** Inputs as `&[u8]` (synchronous calls) or owned buffers
(the queue); a one-message digest as `Hash` (its equality runs in
constant time); batch digests as `&mut [[u8; 32]]`, filled in order;
counts as `usize`; contract violations panic with a message naming the
rule broken.

## How the benchmark measures each

The benchmark measures each call only as its contract says users call
it, so that it guides us to optimise each one for them and flags only
what users meet (Zooko, September 28, 2026). No synchronous call is
measured back to back: every one comes after the program has gone off
and done other things (the gap). Every cell records wall time and
cycles; the energy cells also record joules.

**The synchronous calls: each on its own** (six use cases: three
shapes, single-threaded and multithreaded). The calls can differ widely
in speed, and each deserves its own optimisation.

| use case | call pattern | points |
|---|---|---|
| message in one buffer | one call after the gap | one message, 64 B-128 MiB |
| batch | one call after the gap | message counts at 64 B (and **Q**: other lengths, e.g. 256 B leaves) |
| message in pieces | the first `update` after the gap, the rest in swift succession from a producer that copies each 64 KiB piece in (as a read would), then `finalize` | message length, 64 B-128 MiB |

**The queue: two use cases**, each with enough in flight to
keep the hashing threads busy (about 1 MiB or about 1024 buffers,
whichever is fewer), timed end to end over many inputs:

| use case | call pattern | points |
|---|---|---|
| messages | messages of one length, each read into a free buffer and submitted in pieces of up to 64 KiB (a message up to 64 KiB is one buffer); covers messages in one buffer and in pieces | message length, 64 B-128 MiB |
| batches | buffers of fixed-length messages through `Queue::fixed` | message length and messages per buffer |

The other contenders run the same producers through their own calls: a
one-shot call per message, their incremental API per piece, their batch
call where they have one (BLAKE3 official through `Platform::hash_many`,
sixteen a call).

- The gap: 1 ms, the program asleep (Zooko, September 28, 2026).
  Anything we keep ready, such as a `Hasher` lingering between updates,
  has gone to sleep well before the gap ends.
- perf_regress judges the cells above: the synchronous calls after the
  gap at 20%, the continuous cells at 3% solo and 10% shared.
- **Q**: the continuous cells under both `Efficiency` settings: time
  cells judged by wall time, energy cells by joules.
- **Q**: an energy counter in the timing helper, per process and
  repeatable, validated before any energy cell is frozen.
- **Modes**: keyed and derive-key spot checks at a few sizes in
  perf_regress (same cost as plain; a check that it stays so), no graph
  axis.

## Encoding it into the benchmark, and freezing it

Once Zooko approves this plan:

1. bench-hashes calls exactly the interfaces above in exactly these call
   patterns. An interface not built yet gets a first, simple, correct
   version in the fork, so the benchmark measures the plan from day one
   and the work is making it fast.
2. **The freeze**: bench-hashes' `FROZEN.md` lists every use case, the
   servil call it makes, its call pattern, its points, and its
   scenarios, each with the reason and the decision's date; the test
   `frozen_contract_matches_frozen_md` compares it with the code. A change
   to what the benchmark asks of servil is Zooko's decision, recorded
   there.
3. This file stays as the record of why.
