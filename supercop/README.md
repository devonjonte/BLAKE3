# blake3-servil in eBASH

A proposed eBASH submission: one new implementation, `crypto_hash/blake3/rust_servil`,
beside the existing `crypto_hash/blake3` implementations, which it leaves unchanged.

It builds the blake3-servil crate at a pinned commit (`Cargo.lock`) and calls it as its
users do:

```rust
static INITIALIZE: std::sync::Once = std::sync::Once::new();

pub fn crypto_hash(out: &mut [u8; 32], m: &[u8]) {
  INITIALIZE.call_once(blake3_servil::initialize);
  out.copy_from_slice(blake3_servil::hash(m).as_bytes())
}
```

(`initialize()`, once per process, is the crate's contract; SUPERCOP's first call makes it, before anything is timed.)

SUPERCOP builds Rust implementations with cargo, as it does `crypto_hash/sha256/rust_sha2`.
The crate picks its kernels at run time for each length and CPU; on x86-64, upstream's
assembly for SSE4.1, AVX2 or AVX-512, with the fork's own passes of whole chunks and a
partial one.

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

## After each release

1. `sh supercop/make-tarball.sh vX.Y.Z+<commit>` pins `rust_servil` to the release and
   writes its tarball here, in place of the last one; commit both and push.
2. `sh supercop/check.sh` runs the pinned crate through a fresh SUPERCOP tree, as eBASH
   does, and reports its checksums and SUPERCOP's choice; both must pass, and its cycles
   count only from an idle machine.
3. Zooko sends this to the eBATS list (subscribe first: an empty message to
   ebats-subscribe@list.cr.yp.to), with the tarball's URL at that commit:

```
To: ebats@list.cr.yp.to
Subject: BLAKE3: new implementation crypto_hash/blake3/rust_servil

Dan,

Please include https://raw.githubusercontent.com/johnservil/BLAKE3/<commit>/supercop/<tarball>
in SUPERCOP. It adds one implementation, crypto_hash/blake3/rust_servil,
and leaves the existing ones unchanged: the blake3-servil Rust crate,
pinned by its Cargo.lock and called as its users call it. The crate
picks its kernels at run time for each message length, so its timings
at every length are the ones its users get.

License CC0-1.0 OR Apache-2.0; copyright and patent level 0.

Zooko
```

The email and the tarball are all Dan reads: the submission succeeds when he adds it with
one action, so it looks like the code already in SUPERCOP (its layout, file names and
conventions).
