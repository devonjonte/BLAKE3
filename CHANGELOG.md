# blake3-servil 0.8, against official BLAKE3 1.8.7

The same digests. Faster on 64-bit Arm and x86-64. Every Arm kernel is
proved correct for every input; everything else is tested, and the tests
are tested ([QUALITY.md](QUALITY.md)).

## Before you switch

1. Targets: 64-bit Arm (Linux, macOS) and x86-64 (Linux, Windows with
   MSVC), latest stable Rust, a C compiler (GCC 12 or Clang). Official
   BLAKE3 keeps 32-bit CPUs, big-endian CPUs, WebAssembly, MinGW and older
   compilers.
2. Call `blake3_servil::initialize()` once before any other call, or
   `initialize_multithreaded(None)` if the program makes multithreaded
   calls or uses a stream. A call before it panics.
3. `keyed_hash(key, input)` is `hash_with(Mode::Keyed(key), input)`;
   `derive_key(context, material)` is
   `hash_with(Mode::DeriveKey(context), material)`; `Hasher::new_keyed`
   and `new_derive_key` are `Hasher::new_with(mode)`. `hash` and
   `Hasher::new` are unchanged.
4. Threads are the crate's own. `Hasher::update_rayon` is
   `update_multithreaded`; `hash_multithreaded(input)` hashes one message
   over them. No `rayon` feature.
5. Gone: the `mmap` feature and `Hasher::update_mmap` (map the file
   yourself, or use `update_reader`); the `traits-preview` feature; the
   `guts`, `hazmat` and `platform` modules; the `no_avx2`, `no_avx512`,
   `no_neon` and `no_sme2` features (`pure` stays).
6. `b3sum --num-threads N` is at most N threads in all (1: one thread).
   `--no-mmap` does nothing. Every file is read to its end. A broken pipe
   ends it quietly.

## New

- `hash_many` and `hash_many_multithreaded`: messages of one length in
  one buffer.
- `hash_each_with` and `hash_each_multithreaded_with`: a collection of any
  lengths.
- `Hasher::update_each`: many messages in progress at once.
- `stream()`: inputs one after another, hashed behind the caller.
- `outboard_with`, `verify_range_with`, `Verifier`: verified streaming in
  iroh-blobs' format.
- A C API, `capi/b3.h` (`libb3_servil`; C11, C++11).
- `Mode::DeriveKeyMaterial` with `hash_derive_key_context`: a context
  hashed once for many derivations.

## Different

- A startup self-test checks the build and the CPU; a wrong digest stops
  the program with the code path named.
- A panic on one of the crate's threads, or in a caller during a
  multithreaded call, ends the process.
- A `Hasher` is about 18 KiB: it gathers short updates and hashes them side
  by side, so a message arriving in small pieces hashes as fast as one in
  a buffer.
- The AVX2 and AVX-512 batch kernels read nothing past an input's end
  (BLAKE3-team/BLAKE3#598; reachable in official BLAKE3 only through its
  hidden `platform` module).
- Building the Arm kernels needs an assembler that knows armv8.2-a+sha3
  (GNU as 2.30, LLVM 7); without one, the build warns and leaves them out.
