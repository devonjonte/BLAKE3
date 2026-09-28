# Changelog

## Unreleased

- `Hasher::update_multithreaded` is public: `Hasher::update` over several
  threads, with the same result. Past a message's first 128 KiB it keeps
  the worker threads ready for 50 µs after each update of 64 KiB or more,
  so a long message in 64 KiB pieces hashes about 2.4x as fast as with
  `update` on an Apple M4 Max, at several times the energy per byte.
- `Queue` is faster for a stream of inputs: on an Apple M4 Max about 2x for
  messages one after another and 2.5-4x for batches of 64-byte messages,
  with the program keeping enough in flight. Worker threads with nothing to
  take sleep after 50 µs, even while a queue has inputs in flight.

## 0.3.0

- `Queue`: a stream of inputs hashed behind your program. You hand it your
  buffers and move on; each comes back hashed through a handler you write.
  `Queue::messages` takes separate inputs, `Queue::pieces` one long input
  in pieces, `Queue::fixed` messages of one length many per buffer. With
  `Efficiency::Time` the inputs in flight are hashed on several threads at
  once; with `Efficiency::Energy` on one.
- `Mode` (plain, keyed, key derivation) and `Threads` (one, all, a
  budget): `hash_with(mode, threads, input)` and
  `hash_many_with(mode, threads, input, message_len, out)` take both.
  Batches now hash in every mode at the same speed.
- `initialize()` runs the startup self-test alone (under 200 µs on an
  Apple M4 Max); `initialize_multithreaded()` also starts the worker
  threads (under 1 ms). A program that called `initialize()` to start the
  workers calls `initialize_multithreaded()` instead.
- Removed: `hash_multithreaded_with_budget` and
  `hash_many_multithreaded_with_budget`; use `hash_with` and
  `hash_many_with` with `Threads::Budget(n)`.
- The worker threads sleep whenever no call has work for them, and a
  multithreaded call leaves the calling thread from 768 KiB. A program
  that makes multithreaded calls back to back with no work between them
  runs them slower than 0.2.0 did (which kept the workers spinning between
  calls); a program that pauses between calls runs them faster, and none
  keeps a CPU busy while it waits.
