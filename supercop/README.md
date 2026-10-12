# blake3-servil in eBASH

This directory holds a proposed eBASH submission: `crypto_hash/blake3/rust_servil`, an
implementation of SUPERCOP's `crypto_hash_blake3` that builds this fork's Rust crate at a
pinned commit and calls `blake3_servil::hash`, as the crate's users do. SUPERCOP builds
Rust implementations with cargo, as it does `crypto_hash/sha256/rust_sha2`.

The crate picks its kernels at run time for each length and CPU, so its timings at every
length are the ones its users get. On x86-64 it runs upstream's Rust code, with its
runtime choice of SSE4.1, AVX2 or AVX-512.

SUPERCOP 20261004 on Debian 12 in a VM on an Apple M4 Max, cycles per call:

| bytes | crypto_hash/blake3/neon | rust_servil |
|---|---|---|
| 1536 | 3800 | 3200 |
| 16192 | 23300 | 10400 |
| 64576 | 84000 | 35000 to 40000 |

SUPERCOP's checksums pass with gcc and clang, and it selects rust_servil on that machine.

It is a separate implementation, added beside the existing `crypto_hash/blake3`
implementations, which it leaves unchanged: they measure the BLAKE3 team's code, which
remains widely used, supported and distributed.

To try it: unpack SUPERCOP, copy `crypto_hash/blake3/rust_servil` into its
`crypto_hash/blake3/`, then run `./do-part init` and `./do-part crypto_hash blake3`
(cargo needs network access to fetch the pinned commit). `sh make-tarball.sh COMMIT`
writes the tarball for a pushed commit.
