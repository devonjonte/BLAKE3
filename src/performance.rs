//! The performance API, for power users: every way this crate makes
//! hashing fast (other cores, batches, collections, streams, a message fed
//! in pieces). The program takes on more of the work, so the calls can be
//! fast and simple:
//!
//! - **Inputs start at 64-byte boundaries**: every buffer, and each
//!   message and item in it, so that no 64-byte block straddles two cache
//!   lines. A batch is laid out in 64-byte slots ([`hash_many`]). The
//!   [`Hasher`] alone takes pieces of any length anywhere (it copies short
//!   ones into its own buffer); an aligned long piece runs fastest.
//! - **Digests go where the program says**: into its slices and places.
//! - **Every call takes a [`Mode`]**: `Mode::Hash` for the plain hash.
//!
//! For one call per hash, any slice, the result returned, see the
//! [`convenience`](crate::convenience) API.

#[cfg(feature = "std")]
pub use crate::each::{finalize_each, hash_each, hash_each_multithreaded, update_each, update_each_multithreaded};
pub use crate::incremental::Hasher;
#[cfg(feature = "std")]
pub use crate::stream::{Stream, stream};

use crate::{ContextKey, DERIVE_KEY_CONTEXT, Hash, IV, Mode, OUT_LEN};

/// [`convenience::hash`](crate::convenience::hash) in any [`Mode`]: the
/// plain hash, the keyed hash, or key derivation, at its speed.
///
/// ```
/// # blake3_servil::initialize();
/// use blake3_servil::{Mode, performance};
/// let key = [7u8; 32];
/// assert_eq!(performance::hash(Mode::Keyed(&key), b"foo"), performance::Hasher::new_with(Mode::Keyed(&key)).update(b"foo").finalize());
/// ```
// Inlined, so a constant mode folds to its constants (as
// convenience::hash is: no mode stored for the call to read).
#[inline]
pub fn hash(mode: Mode, input: &[u8]) -> Hash {
    let mut room = core::mem::MaybeUninit::uninit();
    let (key, flags) = mode.key(&mut room);
    crate::hash_serial(input, key, flags)
}

/// The hashes of many messages of one length, laid out in one buffer, in
/// `mode`, on the calling thread: `out[i]` becomes the [`hash`] of message
/// `i`.
///
/// Message `i` starts at byte `i * stride` of `input`, where `stride` is
/// `message_len` rounded up to a multiple of 64 (64 for empty messages), so
/// messages whose length is a multiple of 64 sit back to back. `input`
/// holds exactly `out.len()` strides, and the bytes between a message's end
/// and the next stride are zero (debug builds check; another byte there
/// changes that message's hash). This is the shape of a Merkle tree's
/// layer: leaves of one size, or nodes of two 32-byte children
/// (`message_len` 64).
///
/// ```
/// # blake3_servil::initialize();
/// use blake3_servil::Mode;
/// let leaves = vec![7u8; 1000 * 256];
/// let mut hashes = vec![[0u8; 32]; 1000];
/// blake3_servil::performance::hash_many(Mode::Hash, &leaves, 256, &mut hashes);
/// assert_eq!(hashes[3], *blake3_servil::convenience::hash(&leaves[3 * 256..4 * 256]).as_bytes());
///
/// // 100-byte messages sit 128 bytes apart, zero between them.
/// let mut records = vec![0u8; 10 * 128];
/// for (i, record) in records.chunks_mut(128).enumerate() {
///     record[..100].fill(i as u8 + 1);
/// }
/// let mut digests = vec![[0u8; 32]; 10];
/// blake3_servil::performance::hash_many(Mode::Hash, &records, 100, &mut digests);
/// assert_eq!(digests[9], *blake3_servil::convenience::hash(&[10u8; 100]).as_bytes());
/// ```
///
/// **Speed**: short messages hash several at a time, so a batch beats a
/// loop of [`hash`]: on an Apple M4 Max, 64-byte messages take about 10 to
/// 20 ns each in batches of 16 or more, against about 50 for one [`hash`]
/// each. Messages longer than 15 KiB cost what [`hash`] costs. For the
/// same hashes over several cores, see [`hash_many_multithreaded`].
// Inlined, so a constant mode folds to its constants (as
// convenience::hash is: no mode stored for the call to read).
#[inline]
pub fn hash_many(mode: Mode, input: &[u8], message_len: usize, out: &mut [[u8; OUT_LEN]]) {
    let mut room = core::mem::MaybeUninit::uninit();
    let (key, flags) = mode.key(&mut room);
    crate::hash_many_serial(input, message_len, key, flags, out);
}

/// [`hash_many`], using other CPU cores where that is faster: the same
/// hashes, never slower.
///
/// ```
/// # blake3_servil::initialize_multithreaded(None);
/// use blake3_servil::Mode;
/// let leaves = vec![7u8; 4096 * 256];
/// let mut hashes = vec![[0u8; 32]; 4096];
/// blake3_servil::performance::hash_many_multithreaded(Mode::Hash, &leaves, 256, &mut hashes);
/// assert!(hashes.iter().all(|h| h == blake3_servil::convenience::hash(&[7u8; 256]).as_bytes()));
/// ```
///
/// **Speed**: below 512 KiB in all it runs on the calling thread, at
/// [`hash_many`]'s speed; larger batches use the other cores too (on an
/// Apple M4 Max, 64-byte messages from about 10 down to 3 ns each). It
/// shares the cores with other callers as [`hash_multithreaded`] does.
#[cfg(feature = "std")]
// Inlined, so a constant mode folds to its constants (as
// convenience::hash is: no mode stored for the call to read).
#[inline]
pub fn hash_many_multithreaded(mode: Mode, input: &[u8], message_len: usize, out: &mut [[u8; OUT_LEN]]) {
    crate::lanes::require();
    let mut room = core::mem::MaybeUninit::uninit();
    let (key, flags) = mode.key(&mut room);
    crate::lanes::hash_many(input, message_len, key, flags, out);
}

/// The hash of `input` in `mode`, using other CPU cores where that is
/// faster: the same
/// [`Hash`](struct@Hash) as [`hash`](crate::convenience::hash), never slower.
///
/// ```
/// # blake3_servil::initialize_multithreaded(None);
/// let hash = blake3_servil::performance::hash_multithreaded(blake3_servil::Mode::Hash, &[0u8; 1 << 20]);
/// assert_eq!(hash, blake3_servil::convenience::hash(&[0u8; 1 << 20]));
/// ```
///
/// **Speed**, on an Apple M4 Max (16 cores): below 512 KiB it hashes on the
/// calling thread, at [`hash`](crate::convenience::hash)'s speed; from 512 KiB it uses the other cores
/// too: about 12 GB/s at 1 MiB, 20 GB/s at 4 MiB, and 25 GB/s from 16 MiB,
/// 4 to 6 times [`hash`](crate::convenience::hash). The extra threads wait asleep between calls and
/// use no CPU then.
///
/// **Several callers at once**: calls from several threads of one program
/// share the cores in turn, each getting a fair part; a call that finds the
/// cores all busy hashes on its own thread, at [`hash`](crate::convenience::hash)'s speed.
///
/// **CPUs with performance and efficiency cores** (Intel's since Alder
/// Lake): a multithreaded call or stream uses every core, and afterwards
/// the OS sometimes leaves the calling thread on an efficiency core for a
/// while, where single-threaded hashing runs at about half speed (AVX2's
/// 256-bit operations run as two halves there). Measured on an i7-12700K
/// under Linux 7.0: beside nonstop multithreaded streams, 7% of 16 KiB
/// single-threaded hashes ran partly on an efficiency core, 2.2 times
/// slower, about 6% on their average. A program that alternates the two
/// and needs its single-threaded speed steady can keep that thread on the
/// performance cores (`sched_setaffinity` on Linux).
///
/// The program calls [`initialize_multithreaded`](crate::initialize_multithreaded) first; a call before it
/// panics.
#[cfg(feature = "std")]
// Inlined, so a constant mode folds to its constants (as
// convenience::hash is: no mode stored for the call to read).
#[inline]
pub fn hash_multithreaded(mode: Mode, input: &[u8]) -> Hash {
    crate::lanes::require();
    let mut room = core::mem::MaybeUninit::uninit();
    let (key, flags) = mode.key(&mut room);
    crate::lanes::hash_with_key(input, key, flags)
}

/// Hash a key-derivation context string and return a [`ContextKey`].
///
/// This has the same security requirement as key derivation. **The context
/// string should be hardcoded, globally unique, and application-specific.**
///
/// Its one use is [`Mode::DeriveKeyMaterial`]: a program that derives many
/// keys from one context hashes the context once.
///
/// # Example
///
/// ```
/// # blake3_servil::initialize();
/// use blake3_servil::Mode;
///
/// let context_key = blake3_servil::performance::hash_derive_key_context("foo");
/// let derived = blake3_servil::performance::hash(Mode::DeriveKeyMaterial(&context_key), b"bar");
/// assert_eq!(derived, blake3_servil::performance::hash(Mode::DeriveKey("foo"), b"bar"));
/// ```
pub fn hash_derive_key_context(context: &str) -> ContextKey {
    crate::hash_serial(context.as_bytes(), IV, DERIVE_KEY_CONTEXT).0
}
