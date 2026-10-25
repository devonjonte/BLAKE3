# blake3-servil 0.8, against official BLAKE3 1.8.7

The same digests. Faster than official BLAKE3 1.8.7 on 64-bit Arm and
x86-64. Every kernel is assembly, and every one is proved correct
within its stated contract. Everything else is tested, and the tests
are tested ([QUALITY.md](QUALITY.md)).

## Faster

Each figure is blake3-servil's speed over official BLAKE3 1.8.7's, both
measured in the same run by [bench-hashes](https://github.com/johnservil/bench-hashes)
(0.17.0, one run per machine, October 23–24; the release's own runs
replace these figures):

| | Intel i7-12700K | AMD EPYC 9255 | Apple M4 Max |
|---|---|---|---|
| One message of 64 B | 1.0× | 0.9× | 1.5× |
| One message of 1 KiB | 1.0× | 1.0× | 1.1× |
| One message of 1 MiB, one thread | 1.0× | 1.0× | 2.5× |
| One message of 128 MiB, every core | 1.0× | 1.0× | not yet measured |
| A stream of 64 KiB messages | 7.8× | 7.5× | not yet measured |
| A batch of 1024 messages, 64 B each | 1.1× | 1.2× | 1.9× |
| b3sum over 1000 files of mixed sizes | 2.9× | 5.7× | 4.4× |

On 64-bit Arm, new kernels make every size faster: SME2 on the M4 and
later, and kernels that run the integer and NEON units side by side.
On x86-64, a single message hashes with official's own assembly (each
proved below), so it runs at official's speed, and at 64 B on the EPYC
slower (0.9×). The gains there come from many messages at once: a
stream that hashes on other cores while the program reads the next
input, batches of short messages, and b3sum over many files. The
M4 Max's run measured official's single-threaded form only, so its
every-core rows wait for the release's run.

## Checked more

Beyond official's tests (published test vectors and a reference
implementation), this crate adds:

- **Formal proofs of every assembly kernel**, official's own x86-64
  assembly among them, at every shape this crate calls it: symbolic
  execution against a specification of BLAKE3, with memory accesses,
  the calling convention and secret-dependent branches checked too.
- **Mutation testing**: one small mistake planted at a time, and a test
  must fail for each; the few that survive are listed with their reason.
- **A model checker (Shuttle)** for the thread pool's waits, under
  thousands of thread schedules.
- **Guard pages**: tests put an inaccessible page beside every input,
  output, key and context of every public call, in Rust and in C, so
  a call that touches one byte past the caller's memory crashes the
  test.
- **A startup self-test** of the build and the CPU before the first
  hash.

These found eight bugs before release, among them the AVX2 and AVX-512
batch kernels reading past an input's end at shapes this crate's batch
calls use (fixed here; see below). [QUALITY.md](QUALITY.md) says what
each check covers and what remains unproved.

## Before you switch

1. Targets: 64-bit Arm on Linux and macOS, x86-64 on Linux and Windows
   with MSVC. Latest stable Rust and a C compiler, GCC 12 or Clang.
   Official BLAKE3 keeps 32-bit CPUs, big-endian CPUs, WebAssembly, MinGW
   and older compilers.
2. Call `blake3_servil::initialize()` once before any other call. A
   program that makes multithreaded calls or uses a stream calls
   `initialize_multithreaded(None)` instead. A call before it panics.
3. Two kinds of call, in two modules. `convenience`: one call per hash,
   every feature, any slice, the result returned: `hash(input)` is now
   `convenience::hash(input)`, `keyed_hash(key, input)` is
   `convenience::hash_with(Mode::Keyed(key), input)`, `derive_key(context,
   material)` is `convenience::hash_with(Mode::DeriveKey(context),
   material)`, and `convenience::hash_xof(mode, input)` gives extended
   output. `performance`, for power users, has every way to hash fast,
   the `Hasher` among them (`Hasher::new_with(mode)` replaces
   `Hasher::new_keyed` and `Hasher::new_derive_key`): the program takes
   on more of the work, with inputs as `Block`s (64 bytes on a 64-byte
   boundary: a message is blocks and a length, a batch messages of one
   length), digests into its places, and a `Mode` in every call.
4. Threads are the crate's own. `Hasher::update_rayon` is now
   `update_multithreaded`. `performance::hash_multithreaded(mode, input)`
   hashes one message over the threads. There is no `rayon` feature.
5. Removed: `Hasher::update_mmap` and the `mmap` feature (map the file
   yourself, or use `update_reader`), the `traits-preview` feature, the
   `guts`, `hazmat`, and `platform` modules, and the `no_avx2`,
   `no_avx512`, `no_neon`, and `no_sme2` features. `pure` stays, and means
   portable Rust alone: no assembly, and no SIMD on x86-64 (official
   BLAKE3's `pure` keeps its Rust SSE4.1 and AVX2 kernels).
6. b3sum installs from the package `b3sums` (`cargo install b3sums`);
   crates.io's `b3sum` is official BLAKE3's. The program is still `b3sum`.
   `--num-threads N` means at most N threads in all, and 1 means one
   thread. `--no-mmap` does nothing. Every file is read to its end. A
   broken pipe ends b3sum quietly.

## New

- `performance::hash_many` and `hash_many_multithreaded`: messages of
  one length in `Block`s (64 bytes on a 64-byte boundary), which a
  `Batch` builds with every byte past each message zero.
- `performance::hash_each` and `hash_each_multithreaded`: a collection of
  any lengths.
- `performance::update_each` and `finalize_each`: many messages in
  progress at once, each with its own `Hasher`.
- `performance::stream()`: inputs one after another, hashed behind the
  caller.
- A C API in `capi/b3.h`. The library is `libb3_servil`. C11 and C++11.
- `Mode::DeriveKeyMaterial` with `performance::hash_derive_key_context`: one context
  hashed once for many derivations.

## Different

- A startup self-test checks the build and the CPU. A wrong digest stops
  the process, uncatchably: with `std` it names the code path and aborts;
  without it, the CPU's trap instruction.
- A panic on one of the crate's threads, or in a caller during a
  multithreaded call, ends the process.
- A `Hasher` is about 18 KiB. It gathers short updates and hashes them
  side by side, so a message arriving in small pieces hashes as fast as
  one in a buffer.
- The AVX2 and AVX-512 batch kernels read nothing past an input's end.
- The crate leaves Arm's data-independent timing (DIT) as the calling
  thread has it. A program that wants Arm's promise turns DIT on in its
  own threads before it hashes (the quality manual, "Timing and secrets":
  [docs/quality-manual.md](docs/quality-manual.md)).
- Building the Arm kernels needs an assembler that knows armv8.2-a+sha3,
  GNU as 2.30 or LLVM 7. Without one, the build warns and leaves them out.
