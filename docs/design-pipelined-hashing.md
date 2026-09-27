# Design: hashing a stream of inputs without pipeline bubbles

For Zooko and John Servil, before building (NEXT-STEPS item 2). A proposal
with its open questions; nothing here is built yet.

## The need

A program with many inputs to hash, one after another (files in a
directory, objects arriving over a network, records in a log, blobs for a
content-addressed store), today calls `hash` or `hash_multithreaded` once
per input and does its own work between calls: reading the next input,
storing the last digest. Each call waits for the hash; during the program's
own work our threads sit idle. Since 1046c10 the pool keeps nothing awake
between calls, so every multithreaded call also pays to wake its workers
(about 15-45 µs until the first arrives). The fix is an interface where the
program hands inputs over and moves on, and collects digests as they come.

`Stream` already does this for one long input: the caller fills our 1 MiB
buffers, a hashing thread hashes each full one while the caller fills the
next, and a full set of buffers makes the caller wait (the back-pressure).
The design below extends the same shape to many inputs, each with its own
digest.

## Proposal: `Queue`

```rust
let mut queue = blake3_servil::Queue::new();       // or Queue::new_multithreaded()
for item in items {
    let space = queue.buffer(item.len());          // our memory, item.len() bytes
    item.read_into(space);                         // the caller writes the input
    queue.submit();                                // hand it over; returns at once
    while let Some(hash) = queue.ready() {         // digests so far, in submission order
        store(hash);
    }
}
for hash in queue.finish() {                       // the rest, in order
    store(hash);
}
```

- **Familiar concepts only:** a queue with bounded room, digests returned
  in the order inputs went in. No tickets, no callbacks, no async runtime.
  Each input's digest is the `hash` of its bytes.
- **Zero copy:** as with `Stream`, the caller writes each input into our
  buffer, so nothing is copied after `submit`. A convenience
  `queue.push(&[u8])` copies for callers that hold their input already;
  its copy costs about what hashing costs at multithreaded speed on an M4,
  so the docs steer high-throughput callers to `buffer`.
- **Back-pressure:** `buffer` blocks while the queue's memory is full,
  exactly as `Stream::buffer` does. Room is a byte budget (a few MiB by
  default), so many small inputs and a few large ones both fit the same
  rule.
- **Built for top speed**, in the API docs' terms.

## How it runs

- One hashing thread per queue (as `Stream` has), kept asleep between
  queues. While submitted inputs wait, it holds the pool (a `lanes::Hold`,
  as `Stream` does since 3d7102e), so workers stay in the call across
  inputs and nobody pays a wake per input; when the queue runs empty it
  drops the hold and the workers sleep.
- **Small inputs batch themselves.** Inputs waiting together are grouped
  by length class and hashed through `hash_many`'s kernels (sixteen at a
  time on SME2, the NEON plans below that), so a stream of 64-byte to
  15 KiB inputs runs at batch speed instead of one call's. Inputs of
  different lengths go through the padded batch contract (each padded to
  a multiple of 64 in our buffer, which we zero), so no new kernel is
  needed.
- **Large inputs split over the pool** as `hash_multithreaded` splits
  them (from 768 KiB), with the SME2 turn as today.
- **Order:** digests return in submission order; a small input finished
  early waits behind a large one only in the output, never in the work.

## What it costs and what it wins (to measure)

- Win: the program's own work overlaps our hashing; small inputs reach
  batch speed (1024 x 64 B: about 5x a loop of `hash`); multithreaded
  inputs pay one wake per busy stretch instead of per input.
- Cost: a second thread and the buffers (the queue's byte budget, a few
  MiB); for a single input, a handoff (`Stream` measured 3-4 ns at 64 B
  against a `Hasher`), so the docs keep `hash` as the answer for one input.
- The benchmark needs a use case where the producer does real work per
  input (a copy from a source buffer, as a read would, plus storing each
  digest), timed end to end, with the synchronous contenders running the
  same producer. That use case also shows the bubble the current API
  leaves, for every contender.

## Open questions for Zooko

1. The name: `Queue` (a familiar word for "hand over, collect in order"),
   or an extension of `Stream` (one type, a mode per input)?
2. `ready()` as a polling call, or also a blocking `next()`? Polling keeps
   the caller in control; blocking suits a consumer thread.
3. Mixed lengths through padding cost the padding's bytes; is batching by
   length class worth its code before a user asks for it, or start with
   one input at a time through the hold and add batching second?
4. Keyed and derive-key modes: one mode per queue (simplest), or per input?
5. Should `Stream` and `Queue` share the hashing thread and buffers of the
   calling thread (one of each kept asleep), or keep them separate?
