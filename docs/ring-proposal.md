# A ring the hasher owns: a proposal, measured

NOTES' Future work describes the queue redesigned around "one ring of
input bytes the queue owns, read into in place", with "the calling thread
hashing what no worker has taken" and "workers woken by backlog". This page
describes a working experiment of that design and what it measured on x86
Linux (i7-12700K). The code is `examples/ring_probe.rs` on
`experiment/devon-ring`, about 300 lines on the public API.

## The calls

A program owns one `Ring` per stream of messages.

- `submit(len, fill, digest)` reserves `len` bytes at the ring's head,
  lets `fill` write the message there (a copy from the program's buffer,
  or a read: io_uring could read a socket into it), and publishes it.
- `collect(digest)` hands back every finished digest, in order, on the
  calling thread.
- `finish(digest)` publishes what is written, hashes on the calling thread
  any batch no thread has taken, and hands back every digest.

When the ring is full, `submit` hands back finished digests, and hashes a
batch itself when none are finished. A lone message therefore costs the
program about one `hash()`, with no wait on another thread.

## How it runs

- **Layout.** Each message sits in a slot of whole blocks, zero-padded:
  `hash_many`'s layout, so a run of equal-length messages is one
  `hash_many` call, read in place.
- **Publication.** A batch at a time: one plain store of a count per 64
  messages or 64 KiB, with no locked instruction per message. (In the
  queue, the locked instructions per message were most of `submit`'s cost
  on x86: issue #12.)
- **Hashing threads.** Each claims a batch with one compare-and-swap. A
  thread that finds no batch sleeps at once; the program wakes one when
  two batches wait.
- **Digests.** They come back in order on the program's thread, so there
  is no delivery thread.

## What it measured

| | the queue (Queue::messages, owned buffers) | the ring |
|---|---|---|
| a stream of 64-byte messages | 0.614 ns/B | **0.189** (12 ns a message: hash_many's own rate) |
| 1 KiB / 16 KiB / 64 KiB messages | 0.082 / 0.065 / 0.071 | 0.043 / 0.036 / 0.037 |
| CPU time per byte, 16 KiB | 0.43 CPU-ns | 0.27 |
| two programs at once, every length | | ×0.32–0.74 the queue's time |
| one message after a 1 ms pause, 64 B | 113–127 µs | **1.6 µs** (`hash()`: 0.5) |
| one message after a pause, 64 KiB | 96–109 µs | 20–21 µs (`hash()`: 15) |

Every length streams 1.4–3.3 times as fast as the queue, with less CPU
time. A lone message costs about what `hash()` costs, where the queue pays
about 60 µs of wakes beyond the 55 µs its handover pattern costs on its
own.

For files, the ring buys nothing on this machine. Reading files into
registered buffers with io_uring (`experiments/b3ring`) loses to mapping
for files in the page cache (one copy too many), and from storage both
run at the drive's speed. The ring's gain is in-memory streaming:
messages that already arrive in the program.

## What it gives up, and open questions

- **One producer per ring.** The queue takes many submitters. Several
  producers would each own a ring, or share one through a lock per batch.
- **A copy into the ring.** Data already in the program's buffers is
  copied once (the measurements above include it). NOTES calls for
  measuring exactly this before replacing the owned-buffer queue.
- **Latency of a partial batch.** A message waits in an unpublished batch
  until the program collects, finishes, or fills the ring. A program with
  latency targets calls `collect` or `finish` when it needs the digest.
- **A fixed size.** The ring's size is set per ring here; a message over
  half of it cannot enter.
- **Threads.** The experiment starts its own threads; in the crate the
  ring would use the pool.
