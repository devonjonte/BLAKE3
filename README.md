# BLAKE3, the servil fork

A faster [BLAKE3](https://blake3.io) for 64-bit Arm and x86-64, computing the same digests
as official BLAKE3.

**It is new.** An AI, John Servil, wrote it under Zooko's direction, and no human has
reviewed it line by line or audited it. Its checks are unusually thorough (below), but you
would be among its first users: use it at your own risk.

## Using it

From Rust, add

```toml
[dependencies]
blake3-servil = { git = "https://github.com/johnservil/BLAKE3", branch = "servil" }
```

and hash as you would with official BLAKE3:

```rust
blake3_servil::initialize(); // once, before any other call
let hash = blake3_servil::hash(b"foobarbaz");
```

Programs that hash a lot have faster calls: one large message over many cores, batches,
collections, and a stream that hashes behind your program. The [crate
documentation](https://johnservil.github.io/BLAKE3/blake3_servil/) shows which fits your
data.

From C, build `capi/` (`cargo build --release` there), include [`capi/b3.h`](capi/b3.h),
and link with `-lb3_servil`.

The command-line `b3sum` prints BLAKE3 hashes of files or standard input. On Linux, build
it statically linked, which makes each run start faster (name your machine's target,
`aarch64-unknown-linux-gnu` on Arm):

```bash
RUSTFLAGS="-C target-feature=+crt-static" cargo install --git https://github.com/johnservil/BLAKE3 b3sum --target x86_64-unknown-linux-gnu
```

Elsewhere, `cargo install --git https://github.com/johnservil/BLAKE3 b3sum`.

## How it is checked

- **Proved correct:** the Arm assembly kernels are proved, as the CPU runs them, to
  compute the BLAKE3 standard's compression for all inputs, to stay within their memory,
  and to take the same path whatever the input's bytes. A solver checks the machine code
  against a specification of the standard written in Lean.
- **The tests are tested:** mutation testing plants about 2,500 likely bugs in the Rust
  code, one at a time, and requires a test to catch each one.
- **Digests are checked** against the official test vectors and an independent
  implementation, and each process checks its kernels against known answers before its
  first hash.
- **Memory is checked** under AddressSanitizer, ThreadSanitizer, Miri, and guard pages,
  which crash a test when a kernel reads one byte too far. That is how the fork found a
  read past an input's end in official BLAKE3's AVX2 and AVX-512 kernels, fixed here and
  reported there.

[`QUALITY.md`](QUALITY.md) says more about how the fork is checked and what remains open.

## Where it runs

64-bit Arm (Linux, macOS) and x86-64 (Linux, Windows with MSVC), with the latest stable
Rust. [Official BLAKE3](https://github.com/BLAKE3-team/BLAKE3) serves the rest: 32-bit
CPUs, big-endian CPUs, WebAssembly, Intel Macs, Windows with MinGW, and older compilers.

## How fast

[bench-hashes](https://github.com/johnservil/bench-hashes) measures it against official
BLAKE3 and other hashes on your own machine, for the ways programs hash. Published maps:
an [Intel i7-12700K](https://devonjonte.github.io/bench-hashes/) and an
[Apple M4 Max](https://johnservil.github.io/bench-hashes/benchmark-results/AppleM4Max.darwin25/bench-hashes.map.html).

## About BLAKE3

BLAKE3 was designed by Jack O'Connor, Samuel Neves, Jean-Philippe Aumasson and Zooko. It
is fast, secure, parallel, and one algorithm with no variants, serving as a hash, MAC, KDF
and XOF. The [paper](https://github.com/BLAKE3-team/BLAKE3-specs/blob/master/blake3.pdf)
gives the design and [C2SP](https://c2sp.org/BLAKE3) the specification. BLAKE3 is not a
password hash; for passwords, use [Argon2](https://github.com/P-H-C/phc-winner-argon2).

Other implementations: [official BLAKE3](https://github.com/BLAKE3-team/BLAKE3) (Rust and
C, the BLAKE3 team's), and this repository's [Rust reference
implementation](reference_impl/reference_impl.rs), the clearest place to see how BLAKE3
works, with the [test vectors](test_vectors/test_vectors.json).

## Contributing and licenses

[CONTRIBUTING.md](CONTRIBUTING.md) says how to work on the fork. This work is released into
the public domain with [CC0 1.0](./LICENSE_CC0), or alternatively under [Apache
2.0](./LICENSE_A2) or [Apache 2.0 with LLVM exceptions](./LICENSE_A2LLVM).
