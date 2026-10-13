# blake3-servil in eBASH

A proposed eBASH submission: one new implementation, `crypto_hash/blake3/rust_servil`,
beside the existing `crypto_hash/blake3` implementations, which it leaves unchanged.

It builds the blake3-servil crate at a pinned commit (`Cargo.lock`) and calls it as its
users do:

```rust
pub fn crypto_hash(out: &mut [u8; 32], m: &[u8]) {
  out.copy_from_slice(blake3_servil::hash(m).as_bytes())
}
```

SUPERCOP builds Rust implementations with cargo, as it does `crypto_hash/sha256/rust_sha2`.
The crate picks its kernels at run time for each length and CPU; on x86-64 that is
upstream's code, with its runtime choice of SSE4.1, AVX2 or AVX-512.

SUPERCOP 20261004 in a Linux VM on an Apple M4 Max, cycles per call (checksums pass, and
SUPERCOP selects rust_servil):

| bytes | crypto_hash/blake3/neon | rust_servil |
|---|---|---|
| 1536 | 3800 | 3200 |
| 16192 | 23300 | 10400 |
| 64576 | 84000 | 35000 to 40000 |

To try it, copy `crypto_hash/blake3/rust_servil` (or the tarball beside this file) into a
SUPERCOP tree and run `./do-part init` and `./do-part crypto_hash blake3`; cargo fetches the
pinned commit.
