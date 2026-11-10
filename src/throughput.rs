//! The throughput API, for power users: every way this crate makes
//! hashing fast (batches, collections, many hashers fed in turns). The program takes on more of the work, so the calls can be
//! fast and simple:
//!
//! - **Inputs are [`Block`]s**: 64 bytes each on a 64-byte boundary, so
//!   every message starts a cache line and no block straddles two; the
//!   type holds it. A message is blocks and a length (`&[Block], len`),
//!   the bytes past its end ignored. A batch is a [`Batch`]: messages of
//!   one length, each in its own whole blocks, every byte past each one
//!   zero, which the batch kernels read in place, side by side; a `Batch`
//!   lets the program write only its messages' bytes, so those zeros
//!   cannot go wrong. Bytes already in place become blocks with no copy
//!   through [`Block::from_bytes`], and a batch through
//!   [`Batch::from_blocks`] where its messages fill their blocks.
//!   [`update_each`] alone takes pieces of any
//!   length anywhere, into a [`Hasher`](crate::convenience::Hasher) (which
//!   copies short ones into its own buffer); an aligned long piece runs
//!   fastest.
//! - **Digests go where the program says**: into its slices and places.
//! - **Every call takes a [`Mode`]**: `Mode::Plain` for the plain hash.
//!
//! For one call per hash, any slice, the result returned, see the
//! [`convenience`](crate::convenience) API.

#[cfg(feature = "std")]
pub use crate::block::Packed;
pub use crate::block::{Batch, Block, Prepared};
#[cfg(feature = "std")]
pub use crate::each::{finalize_each, hash_each, update_each};

use crate::{ContextKey, DERIVE_KEY_CONTEXT, Hash, IV, Mode, OUT_LEN};

/// The hash in `mode` of the message of `len` bytes that starts `input`:
/// a batch of one. The message starts a block, so on a cache line; the
/// bytes past its end, in its last block and any after, are ignored.
/// Tuned for call after call: for a hash now and then amid other work,
/// [`convenience::hash`](crate::convenience::hash) is the faster call.
///
/// ```
/// # blake3_servil_core::initialize();
/// # #[cfg(feature = "std")] {
/// use blake3_servil_core::{Mode, convenience, throughput::{self, Batch}};
/// let mut message = Batch::new(100, 1);
/// message.set(0, &[7u8; 100]);
/// assert_eq!(throughput::hash(Mode::Plain, message.blocks(), 100), convenience::hash(&[7u8; 100]));
/// # }
/// ```
// Inlined, so a constant mode folds to its constants (as
// convenience::hash is: no mode stored for the call to read).
#[inline]
pub fn hash(mode: Mode, input: &[Block], len: usize) -> Hash {
    let mut room = core::mem::MaybeUninit::uninit();
    let (key, flags) = mode.key(&mut room);
    crate::hash_serial(&Block::bytes(input)[..len], key, flags)
}

/// The hashes of a [`Batch`]'s messages, in `mode`, on the calling thread:
/// `out[i]` becomes the [`hash`] of message `i`, one digest a message. This
/// is the shape of a Merkle tree's layer: leaves of one size, or nodes of
/// two 32-byte children, which the layer below writes straight into the
/// next layer's batch ([`Batch::digests_mut`]).
///
/// ```
/// # blake3_servil_core::initialize();
/// # #[cfg(feature = "std")] {
/// use blake3_servil_core::{Mode, convenience, throughput::{self, Batch}};
/// let mut leaves = Batch::new(256, 1000);
/// for i in 0..1000 {
///     leaves.set(i, &[7u8; 256]);
/// }
/// let mut hashes = vec![[0u8; 32]; 1000];
/// throughput::hash_many(Mode::Plain, &leaves, &mut hashes);
/// assert_eq!(hashes[3], *convenience::hash(&[7u8; 256]).as_bytes());
/// # }
/// ```
///
/// **Speed**: short messages hash several at a time, so a batch beats a
/// loop of [`hash`]: on an Apple M4 Max, 64-byte messages take about 10 to
/// 20 ns each in batches of 16 or more, against about 50 for one [`hash`]
/// each. Messages longer than 15 KiB cost what [`hash`] costs. For the
/// same hashes over several cores, the crate `blake3-servil` has
/// `hash_many_multithreaded`.
///
/// A [`Packed`] of 16- or 32-byte messages is a batch too, as the program
/// holds them, with no copy into blocks:
///
/// ```
/// # blake3_servil_core::initialize();
/// # #[cfg(feature = "std")] {
/// use blake3_servil_core::{Mode, convenience, throughput::{self, Packed}};
/// let mut leaves = Packed::<32>::new(1000);
/// for (i, leaf) in leaves.iter_mut().enumerate() {
///     leaf[0] = i as u8;
/// }
/// let mut digests = Packed::<32>::new(1000); // the next layer's input
/// throughput::hash_many(Mode::Plain, &leaves, &mut digests);
/// assert_eq!(digests[3], *convenience::hash(&leaves[3]).as_bytes());
/// # }
/// ```
// Inlined, so a constant mode folds to its constants (as
// convenience::hash is: no mode stored for the call to read).
#[inline(always)]
pub fn hash_many<P: Prepared>(mode: Mode, batch: &P, out: &mut [[u8; OUT_LEN]]) {
    let mut room = core::mem::MaybeUninit::uninit();
    let (key, flags) = mode.key(&mut room);
    crate::hash_many_serial(batch.bytes(), batch.message_len(), batch.slot(), key, flags, out);
}

/// Hash a key-derivation context string and return a [`ContextKey`].
///
/// This has the same security requirement as key derivation. **The context
/// string should be hardcoded, globally unique, and application-specific.**
///
/// Its one use is [`Mode::DeriveKeyWith`]: a program that derives many
/// keys from one context hashes the context once.
///
/// # Example
///
/// ```
/// # blake3_servil_core::initialize();
/// use blake3_servil_core::Mode;
///
/// let context_key = blake3_servil_core::throughput::context_key("foo");
/// let derived = blake3_servil_core::convenience::hash_with(Mode::DeriveKeyWith(&context_key), b"bar");
/// assert_eq!(derived, blake3_servil_core::convenience::hash_with(Mode::DeriveKey("foo"), b"bar"));
/// ```
pub fn context_key(context: &str) -> ContextKey {
    crate::hash_serial(context.as_bytes(), IV, DERIVE_KEY_CONTEXT).0
}
