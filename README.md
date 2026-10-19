# BLAKE3, the servil fork

A faster [BLAKE3](https://blake3.io), computing the same digests as official BLAKE3. It
is fastest on 64-bit Arm, above all on Apple M4-class chips, and faster on x86-64 too.

**It is new.** An AI, John Servil, wrote it under Zooko's direction, and no person has
reviewed it line by line or audited it. Its checks are unusually thorough (below), but you
would be among its first users: use it at your own risk.

## What you get

- The same `hash`, `Hasher`, keyed hash and key derivation as official BLAKE3, with one
  change: call `initialize()` once first, and choose the keyed hash or key derivation with
  a `Mode`.
- Calls for the ways programs hash a lot: one large message over every core
  (`hash_multithreaded`); batches of equal-length messages (`hash_many`); a collection of
  messages of any lengths (`hash_each_with`); and a `stream` that hashes your messages on
  other threads while your program reads or makes the next ones.
- Verified streaming in the format [iroh-blobs](https://github.com/n0-computer/iroh-blobs)
  stores (`outboard_with`, `Verifier`).
- A C library, `libb3_servil`, and the command-line `b3sum`.

## Using it

From Rust, add

```toml
[dependencies]
blake3-servil = { git = "https://github.com/johnservil/BLAKE3", branch = "servil" }
```

and call it as you would official BLAKE3's `blake3` crate, under its own name:

```rust
use blake3_servil::Mode;

blake3_servil::initialize(); // once, before any other call (it runs the self-test)
let hash = blake3_servil::hash(b"foobarbaz");

let mut hasher = blake3_servil::Hasher::new();
hasher.update(b"foo");
hasher.update(b"barbaz");
assert_eq!(hasher.finalize(), hash);

let key = [42u8; 32];
let mac = blake3_servil::hash_with(Mode::Keyed(&key), b"message");
let subkey = blake3_servil::hash_with(Mode::DeriveKey("example.com 2026-10-19 session keys"), b"key material");
```

The [crate documentation](https://johnservil.github.io/BLAKE3/blake3_servil/) opens with a
table of which call fits your data.

From C, build the library in `capi/` (`cargo build --release` there gives `libb3_servil.a`
and `libb3_servil.so` or `libb3_servil.dylib`), include [`capi/b3.h`](capi/b3.h), and link
with `-lb3_servil`:

```c
#include "b3.h"

b3_mode plain = b3_plain();
b3_digest digest = b3_hash(&plain, "foobarbaz", 9);
```

`b3.h` documents each call.

The command-line `b3sum` prints the BLAKE3 hashes of files or of standard input:

```bash
cargo install --git https://github.com/johnservil/BLAKE3 b3sum
```

## How it is checked

- **Proved correct:** every assembly kernel on 64-bit Arm is proved, as the CPU runs it, to
  compute the BLAKE3 standard's compression for every possible input, to stay within the
  memory it is given, and to take the same path whatever the input's bytes. A solver checks
  the machine code against a specification of the standard written in Lean.
- **Its tests are tested:** mutation testing plants about 2,500 likely bugs in the Rust
  code, one at a time. Nearly two in three fail a test; each of the rest is listed with the
  reason it survives (most change only speed, or run only on another kind of machine).
- **Every digest is checked** against the official test vectors and an independent
  implementation, and every process checks its kernels against known answers before its
  first hash.
- **Memory safety is tested** under AddressSanitizer, ThreadSanitizer, Miri, and guard
  pages: tests that put each input beside memory the program may not touch, so a kernel
  reading one byte too far crashes the test. This is how the fork found a read past the end
  of an input in official BLAKE3's AVX2 and AVX-512 kernels, fixed here and reported there.

[`QUALITY.md`](QUALITY.md) explains these checks for a newcomer, and the
[quality manual](docs/quality-manual.md) states each claim precisely with the commands to
repeat it.

## Where it runs

64-bit Arm (Linux and macOS) and x86-64 (Linux, and Windows with MSVC), with the latest
stable Rust. Those are the targets its checks run on, and the only ones it claims. [Official
BLAKE3](https://github.com/BLAKE3-team/BLAKE3) serves the rest: 32-bit CPUs, big-endian
CPUs, WebAssembly, Intel Macs, Windows with MinGW, and older compilers.

## How fast

[bench-hashes](https://github.com/johnservil/bench-hashes) measures it against official
BLAKE3 and other hashes on your own machine, for the ways programs hash: one message, many
messages, after idling, with other work beside, and so on. Its published results are the
[map for an Apple M4 Max](https://johnservil.github.io/bench-hashes/benchmark-results/AppleM4Max.darwin25/bench-hashes.map.html);
[METHODOLOGY.md](https://github.com/johnservil/bench-hashes/blob/main/METHODOLOGY.md)
says how it measures.

## About BLAKE3

BLAKE3 was designed by Jack O'Connor, Samuel Neves, Jean-Philippe Aumasson and Zooko. It
is fast, secure, parallel (a Merkle tree inside), and one algorithm with no variants; it
serves as a hash, MAC, KDF and XOF. The [BLAKE3
paper](https://github.com/BLAKE3-team/BLAKE3-specs/blob/master/blake3.pdf) gives the design
and [C2SP](https://c2sp.org/BLAKE3) the specification. BLAKE3 is not a password hash; for
passwords, use [Argon2](https://github.com/P-H-C/phc-winner-argon2).

This repository also carries the [Rust reference
implementation](reference_impl/reference_impl.rs), the clearest place to see how BLAKE3
works, and the [test vectors](test_vectors/test_vectors.json).

## Contributing and licenses

[CONTRIBUTING.md](CONTRIBUTING.md) says how to work on the fork. This work is released into
the public domain with [CC0 1.0](./LICENSE_CC0), or alternatively under [Apache
2.0](./LICENSE_A2) or [Apache 2.0 with LLVM exceptions](./LICENSE_A2LLVM).
