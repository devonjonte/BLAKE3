# Changelog

What changed in each release that a user meets: what it gives, how to
come to it, and what breaks. `git log` holds every step on the way.

## 0.8.0 (unreleased)

**blake3-servil 0.8: BLAKE3, proved and faster.** The same digests as
official BLAKE3, faster on 64-bit Arm and on x86-64. Every Arm kernel is
proved correct for every input, everything else is tested, and the tests
are tested ([QUALITY.md](QUALITY.md)). Beyond official BLAKE3: a stream
for inputs one after another, collections and many messages at once,
verified streaming (outboards and a `Verifier`), a C API, and a faster
`b3sum`.

**Coming from official BLAKE3:**

1. Check your target: 64-bit Arm (Linux, macOS) or x86-64 (Linux, Windows
   with MSVC), with the latest stable Rust. 32-bit CPUs, big-endian CPUs,
   WebAssembly, Windows with MinGW and older compilers stay with official
   BLAKE3.
2. Call `blake3_servil::initialize()` once before any other call, or
   `initialize_multithreaded(None)` if the program makes multithreaded
   calls or uses a stream. A call before it panics, saying so.
3. Choose a mode with `Mode`: `keyed_hash(key, input)` becomes
   `hash_with(Mode::Keyed(key), input)`, `derive_key(context, material)`
   becomes `hash_with(Mode::DeriveKey(context), material)`, and
   `Hasher::new_keyed` / `new_derive_key` become `Hasher::new_with(mode)`.
   `hash(input)` and `Hasher::new()` are as they were.
4. Threads are this crate's, not Rayon's: `Hasher::update_rayon` becomes
   `update_multithreaded`, and `hash_multithreaded(input)` hashes one
   message over the threads. There is no `rayon` feature.
5. Gone, with what to use instead: the `mmap` feature and
   `Hasher::update_mmap` (map the file yourself and call `update`, or use
   `update_reader`); the `traits-preview` feature (the RustCrypto `digest`
   traits); the `guts` and `hazmat` modules (subtrees by hand: the
   verified-streaming calls below serve the tree, and
   `hash_derive_key_context` is at the crate root); the hidden `platform`
   module; the testing features `no_avx2`, `no_avx512`, `no_neon` and
   `no_sme2` (`pure` stays).
6. `b3sum`: `--num-threads N` means at most N threads in all (1: one
   thread); `--no-mmap` has no effect; every file is read to its end; a
   broken pipe ends it quietly, as GNU's tools do.

**New calls**, each documented with its speed in the crate docs ("Which
call to use"): `hash_many` / `hash_many_multithreaded` for messages of
one length in one buffer; `hash_each_with` / `hash_each_multithreaded_with`
for a collection of any lengths; `Hasher::update_each` for many messages
in progress at once; `stream()` for inputs one after another, hashed
behind the caller; `outboard_with`, `verify_range_with` and `Verifier`
for verified streaming in iroh-blobs' format; a C API in `capi/b3.h`
(`libb3_servil`, C11 and C++11).

**Behaviour a user may notice:**

- A panic on one of this crate's threads, or in a caller while its
  multithreaded call is in progress (a bug in this crate), ends the
  process with the panic's message, rather than leaving a call waiting
  forever.
- The startup self-test runs in every build, `no_std` included, and a
  build or CPU that computes wrong digests stops with a panic naming the
  code path. On x86-64 a binary built for CPUs with LZCNT or BMI1 stops
  on a CPU without them.
- The AVX2 and AVX-512 batch kernels no longer read past an input's end
  (official BLAKE3's did, reachable there only through its hidden
  `platform` module: BLAKE3-team/BLAKE3#598).
- Worker threads sleep as soon as they find nothing to take; nothing runs
  between calls. `initialize_multithreaded` returns once the first worker
  has started; the rest start behind it.
- A `Hasher` is about 18 KiB: it gathers updates shorter than 16 KiB to
  hash them side by side, so a message arriving in network-sized pieces
  hashes nearly as fast as one in whole buffers.
- Building needs a C compiler (GCC 12 or later, or Clang) and, for the
  Arm kernels, an assembler that knows armv8.2-a+sha3 (GNU as 2.30,
  LLVM 7); without one the build warns and leaves those kernels out, or
  build with the `pure` feature.

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
