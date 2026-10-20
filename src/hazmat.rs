//! The tree's interior values, for the tests: a positioned subtree's
//! chaining value (`HasherExt`) and the merge of two subtrees
//! (`merge_subtrees_*`), upstream's `hazmat` API kept as an independent
//! computation the pool's tests check themselves against. Nothing public:
//! this fork's tree APIs are `outboard_with`, `verify_range_with` and
//! `Verifier`, in iroh-blobs' format.
use crate::platform::Platform;
use crate::{CHUNK_LEN, CVWords, ContextKey, Hasher, IV, KEY_LEN, OUT_LEN, hash_derive_key_context, max_subtree_len};

/// Extension methods for [`Hasher`]. This is the main entrypoint to the `hazmat` module.
pub(crate) trait HasherExt {
    /// Similar to [`Hasher::new_with`] with [`Mode::DeriveKeyMaterial`](crate::Mode::DeriveKeyMaterial) but using a pre-hashed [`ContextKey`] from
    /// [`hash_derive_key_context`].
    ///
    /// The [`hash_derive_key_context`] function is the _only_ valid source of the [`ContextKey`].
    /// Any other source ([`hash`](crate::hash), a keyed hash, arbitrary bytes
    /// from the caller) violates the security requirements.
    ///
    /// Calling [`derive_key`](crate::derive_key) or [`Hasher::new_with`] with [`Mode::DeriveKeyMaterial`](crate::Mode::DeriveKeyMaterial) in a loop will
    /// re-hash the context string every time. This constructor function is a performance
    /// optimization to avoid that repeated work. If you hardcode the [`ContextKey`], the
    /// derive-key mode becomes zero-overhead, like the keyed mode.
    ///
    /// # Example
    ///
    /// ```
    /// # blake3_servil::initialize();
    /// use blake3_servil::Hasher;
    /// use blake3_servil::hazmat::HasherExt;
    ///
    /// let context_key = blake3_servil::hazmat::hash_derive_key_context("foo");
    /// let mut hasher = Hasher::new_from_context_key(&context_key);
    /// hasher.update(b"bar");
    /// let derived_key = *hasher.finalize().as_bytes();
    ///
    /// assert_eq!(derived_key, *blake3_servil::hash_with(blake3_servil::Mode::DeriveKey("foo"), b"bar").as_bytes());
    /// ```
    fn new_from_context_key(context_key: &ContextKey) -> Self;

    /// Configure the `Hasher` to process a chunk or subtree starting at `offset` bytes into the
    /// whole input.
    ///
    /// You must call this function before processing any input with [`update`](Hasher::update) or
    /// similar. This step isn't required for the first chunk, or for a subtree that includes the
    /// first chunk (i.e. when the `offset` is zero), but it's required for all other chunks and
    /// subtrees.
    ///
    /// The starting input offset of a subtree implies a maximum possible length for that subtree.
    /// See [`max_subtree_len`] and section 2.1 of [the BLAKE3
    /// paper](https://github.com/BLAKE3-team/BLAKE3-specs/blob/master/blake3.pdf). Note that only
    /// subtrees along the right edge of the whole tree can have a length less than their maximum
    /// possible length.
    ///
    /// See the [module level examples](index.html#examples).
    ///
    /// # Panics
    ///
    /// This function panics if the `Hasher` has already accepted any input with
    /// [`update`](Hasher::update) or similar.
    ///
    /// This should always be paired with [`finalize_non_root`](HasherExt::finalize_non_root). It's
    /// never correct to use a non-zero input offset with [`finalize`](Hasher::finalize) or
    /// [`finalize_xof`](Hasher::finalize_xof). The `offset` must also be a multiple of
    /// `CHUNK_LEN`. Violating either of these rules will currently fail an assertion and panic,
    /// but this is not guaranteed.
    fn set_input_offset(&mut self, offset: u64) -> &mut Self;

    /// Finalize the non-root hash ("chaining value") of the current chunk or subtree.
    ///
    /// Afterwards you can merge subtree chaining values into parent nodes using
    /// [`merge_subtrees_non_root`] and ultimately into the root node with either
    /// [`merge_subtrees_root`] (similar to [`Hasher::finalize`]) or [`merge_subtrees_root_xof`]
    /// (similar to [`Hasher::finalize_xof`]).
    ///
    /// See the [module level examples](index.html#examples), particularly the discussion of valid
    /// tree structures.
    fn finalize_non_root(&self) -> ChainingValue;
}

impl HasherExt for Hasher {
    fn new_from_context_key(context_key: &[u8; KEY_LEN]) -> Hasher {
        let context_key_words = crate::platform::words_from_le_bytes_32(context_key);
        Hasher::from_core(crate::HasherCore::new_internal(&context_key_words, crate::DERIVE_KEY_MATERIAL))
    }

    fn set_input_offset(&mut self, offset: u64) -> &mut Hasher {
        assert_eq!(self.count(), 0, "hasher has already accepted input");
        self.core.set_input_offset(offset);
        self
    }

    fn finalize_non_root(&self) -> ChainingValue {
        assert_ne!(self.count(), 0, "empty subtrees are never valid");
        self.final_output().chaining_value()
    }
}

#[test]
fn test_max_subtree_len() {
    assert_eq!(max_subtree_len(0), None);
    // (chunk index, max chunks)
    let cases = [(1, 1), (2, 2), (3, 1), (4, 4), (5, 1), (6, 2), (7, 1), (8, 8)];
    for (chunk_index, max_chunks) in cases {
        let input_offset = chunk_index * CHUNK_LEN as u64;
        assert_eq!(max_subtree_len(input_offset), Some(max_chunks * CHUNK_LEN as u64),);
    }
}

/// Given the length in bytes of either a complete input or a subtree input, return the number of
/// bytes that belong to its left child subtree. The rest belong to its right child subtree.
///
/// Concretely, this function returns the largest power-of-two number of bytes that's strictly less
/// than `input_len`. This leads to a tree where all left subtrees are "complete" and at least as
/// large as their sibling right subtrees, as specified in section 2.1 of [the BLAKE3
/// paper](https://github.com/BLAKE3-team/BLAKE3-specs/blob/master/blake3.pdf). For example, if an
/// input is exactly two chunks, the left subtree gets the first chunk and the right subtree gets
/// the second chunk. But if an input is two chunks plus one more byte, then its left subtree gets
/// two chunks, and its right subtree only gets one byte.
///
/// This function isn't meaningful for one chunk of input, because chunks don't have children. It
/// currently panics in debug mode if `input_len <= CHUNK_LEN`.
///
/// # Example
///
/// Hash an input as two subtrees:
///
/// ```
/// # blake3_servil::initialize();
/// # #[cfg(feature = "std")] {
/// use blake3_servil::hazmat::{left_subtree_len, merge_subtrees_root, HasherExt, Mode};
/// use blake3_servil::{Hasher, CHUNK_LEN};
///
/// // To be split into two subtrees, the input must be longer than CHUNK_LEN.
/// let input_len = 5 * CHUNK_LEN + 100;
/// let input: Vec<u8> = (0..input_len).map(|i| (i % 251) as u8).collect();
///
/// // Compute the left and right subtree hashes and then the root hash. left_subtree_len() tells
/// // us exactly where to split the input. Any other split would either panic (if we're lucky) or
/// // lead to an incorrect root hash.
/// let left_len = left_subtree_len(input_len as u64) as usize;
/// let left_subtree_cv = Hasher::new()
///     .update(&input[..left_len])
///     .finalize_non_root();
/// let right_subtree_cv = Hasher::new()
///     .set_input_offset(left_len as u64)
///     .update(&input[left_len..])
///     .finalize_non_root();
/// let root_hash = merge_subtrees_root(&left_subtree_cv, &right_subtree_cv, Mode::Hash);
///
/// // Double check the answer.
/// assert_eq!(root_hash, blake3_servil::hash(&input));
/// # }
/// ```
#[inline(always)]
pub(crate) fn left_subtree_len(input_len: u64) -> u64 {
    debug_assert!(input_len > CHUNK_LEN as u64);
    // Note that .next_power_of_two() is greater than *or equal*.
    ((input_len + 1) / 2).next_power_of_two()
}

#[test]
fn test_left_subtree_len() {
    assert_eq!(left_subtree_len(1025), 1024);
    for boundary_case in [2, 4, 8, 16, 32, 64] {
        let input_len = boundary_case * CHUNK_LEN as u64;
        assert_eq!(left_subtree_len(input_len - 1), input_len / 2);
        assert_eq!(left_subtree_len(input_len), input_len / 2);
        assert_eq!(left_subtree_len(input_len + 1), input_len);
    }
}

/// The `mode` argument to [`merge_subtrees_root`] and friends
///
/// See the [module level examples](index.html#examples).
#[derive(Copy, Clone, Debug)]
pub(crate) enum Mode<'a> {
    /// The default [`hash`][crate::hash] mode. Subtrees must be hashed with [`Hasher::new`].
    Hash,

    /// The keyed hash mode. Subtrees must be hashed with
    /// [`Hasher::new_with`].
    KeyedHash(&'a [u8; KEY_LEN]),

    /// The key derivation mode. Subtrees must be hashed with either
    /// [`Hasher::new_with`] with [`Mode::DeriveKeyMaterial`](crate::Mode::DeriveKeyMaterial) or [`Hasher::new_from_context_key`]. The [`ContextKey`] comes
    /// from [`hash_derive_key_context`].
    DeriveKeyMaterial(&'a ContextKey),
}

impl<'a> Mode<'a> {
    pub(crate) fn key_words(&self) -> CVWords {
        match self {
            Mode::Hash => *IV,
            Mode::KeyedHash(key) => crate::platform::words_from_le_bytes_32(key),
            Mode::DeriveKeyMaterial(cx_key) => crate::platform::words_from_le_bytes_32(cx_key),
        }
    }

    pub(crate) fn flags_byte(&self) -> u8 {
        match self {
            Mode::Hash => 0,
            Mode::KeyedHash(_) => crate::KEYED_HASH,
            Mode::DeriveKeyMaterial(_) => crate::DERIVE_KEY_MATERIAL,
        }
    }
}

/// "Chaining value" is the academic term for a non-root or non-final hash.
///
/// Besides just sounding fancy, it turns out there are [security
/// reasons](https://jacko.io/tree_hashing.html) to be careful about the difference between
/// (root/final) hashes and (non-root/non-final) chaining values.
pub(crate) type ChainingValue = [u8; OUT_LEN];

fn merge_subtrees_inner(left_child: &ChainingValue, right_child: &ChainingValue, mode: Mode) -> crate::Output {
    crate::hasher::parent_output(&left_child, &right_child, &mode.key_words(), mode.flags_byte(), Platform::detect())
}

/// Compute a non-root parent node chaining value from two child chaining values.
///
/// See the [module level examples](index.html#examples), particularly the discussion of valid tree
/// structures. The left and right child chaining values can come from either
/// [`Hasher::finalize_non_root`](HasherExt::finalize_non_root) or other calls to
/// `merge_subtrees_non_root`. "Chaining value" is the academic term for a non-root or non-final
/// hash.
pub(crate) fn merge_subtrees_non_root(left_child: &ChainingValue, right_child: &ChainingValue, mode: Mode) -> ChainingValue {
    merge_subtrees_inner(left_child, right_child, mode).chaining_value()
}

/// Compute a root hash from two child chaining values.
///
/// See the [module level examples](index.html#examples), particularly the discussion of valid tree
/// structures. The left and right child chaining values can come from either
/// [`Hasher::finalize_non_root`](HasherExt::finalize_non_root) or [`merge_subtrees_non_root`].
/// "Chaining value" is the academic term for a non-root or non-final hash.
///
/// Note that inputs of [`CHUNK_LEN`] or less don't produce any parent nodes and can't be hashed
/// using this function. In that case you must get the root hash from [`Hasher::finalize`] (or just
/// [`blake3_servil::hash`](crate::hash)).
pub(crate) fn merge_subtrees_root(left_child: &ChainingValue, right_child: &ChainingValue, mode: Mode) -> crate::Hash {
    merge_subtrees_inner(left_child, right_child, mode).root_hash()
}

/// Build a root [`OutputReader`](crate::OutputReader) from two child chaining values.
///
/// See also the [module level examples](index.html#examples), particularly the discussion of valid
/// tree structures. The left and right child chaining values can come from either
/// [`Hasher::finalize_non_root`](HasherExt::finalize_non_root) or [`merge_subtrees_non_root`].
/// "Chaining value" is the academic term for a non-root or non-final hash.
///
/// Note that inputs of [`CHUNK_LEN`] or less don't produce any parent nodes and can't be hashed
/// using this function. In that case you must get the `OutputReader` from
/// [`Hasher::finalize_xof`].
///
/// # Example
///
/// ```
/// # blake3_servil::initialize();
/// use blake3_servil::hazmat::{merge_subtrees_root_xof, HasherExt, Mode};
/// use blake3_servil::{Hasher, CHUNK_LEN};
///
/// // Hash a 2-chunk subtree in steps. Note that only
/// // the final chunk can be shorter than CHUNK_LEN.
/// let chunk0 = &[42; CHUNK_LEN];
/// let chunk1 = b"hello world";
/// let chunk0_cv = Hasher::new()
///     .update(chunk0)
///     .finalize_non_root();
/// let chunk1_cv = Hasher::new()
///     .set_input_offset(CHUNK_LEN as u64)
///     .update(chunk1)
///     .finalize_non_root();
///
/// // Obtain a blake3_servil::OutputReader at the root and extract 1000 bytes.
/// let mut output_reader = merge_subtrees_root_xof(&chunk0_cv, &chunk1_cv, Mode::Hash);
/// let mut output_bytes = [0; 1_000];
/// output_reader.fill(&mut output_bytes);
///
/// // Double check the answer.
/// let mut hasher = Hasher::new();
/// hasher.update(chunk0);
/// hasher.update(chunk1);
/// let mut expected = [0; 1_000];
/// hasher.finalize_xof().fill(&mut expected);
/// assert_eq!(output_bytes, expected);
/// ```
pub(crate) fn merge_subtrees_root_xof(left_child: &ChainingValue, right_child: &ChainingValue, mode: Mode) -> crate::OutputReader {
    crate::OutputReader::new(merge_subtrees_inner(left_child, right_child, mode))
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    #[should_panic]
    fn test_empty_subtree_should_panic() {
        Hasher::new().finalize_non_root();
    }

    #[test]
    #[should_panic]
    fn test_unaligned_offset_should_panic() {
        Hasher::new().set_input_offset(1);
    }

    #[test]
    #[should_panic]
    fn test_hasher_already_accepted_input_should_panic() {
        Hasher::new().update(b"x").set_input_offset(0);
    }

    #[test]
    #[should_panic]
    fn test_too_much_input_should_panic() {
        Hasher::new().set_input_offset(CHUNK_LEN as u64).update(&[0; CHUNK_LEN + 1]);
    }

    #[test]
    #[should_panic]
    fn test_set_input_offset_cant_finalize() {
        Hasher::new().set_input_offset(CHUNK_LEN as u64).finalize();
    }

    #[test]
    #[should_panic]
    fn test_set_input_offset_cant_finalize_xof() {
        Hasher::new().set_input_offset(CHUNK_LEN as u64).finalize_xof();
    }

    #[test]
    fn test_grouped_hash() {
        const MAX_CHUNKS: usize = (crate::test::TEST_CASES_MAX + 1) / CHUNK_LEN;
        let mut input_buf = [0; crate::test::TEST_CASES_MAX];
        crate::test::paint_test_input(&mut input_buf);
        for subtree_chunks in [1, 2, 4, 8, 16, 32] {
            #[cfg(feature = "std")]
            dbg!(subtree_chunks);
            let subtree_len = subtree_chunks * CHUNK_LEN;
            for &case in crate::test::TEST_CASES {
                if case <= subtree_len {
                    continue;
                }
                #[cfg(feature = "std")]
                dbg!(case);
                let input = &input_buf[..case];
                let expected_hash = crate::hash(input);

                // Collect all the group chaining values.
                let mut chaining_values = arrayvec::ArrayVec::<ChainingValue, MAX_CHUNKS>::new();
                let mut subtree_offset = 0;
                while subtree_offset < input.len() {
                    let take = core::cmp::min(subtree_len, input.len() - subtree_offset);
                    let subtree_input = &input[subtree_offset..][..take];
                    let subtree_cv = Hasher::new().set_input_offset(subtree_offset as u64).update(subtree_input).finalize_non_root();
                    chaining_values.push(subtree_cv);
                    subtree_offset += take;
                }

                // Compress all the chaining_values together, layer by layer.
                assert!(chaining_values.len() >= 2);
                while chaining_values.len() > 2 {
                    let n = chaining_values.len();
                    // Merge each side-by-side pair in place, overwriting the front half of the
                    // array with the merged results. This moves us "up one level" in the tree.
                    for i in 0..(n / 2) {
                        chaining_values[i] = merge_subtrees_non_root(&chaining_values[2 * i], &chaining_values[2 * i + 1], Mode::Hash);
                    }
                    // If there's an odd CV out, it moves up.
                    if n % 2 == 1 {
                        chaining_values[n / 2] = chaining_values[n - 1];
                    }
                    chaining_values.truncate(n / 2 + n % 2);
                }
                assert_eq!(chaining_values.len(), 2);
                let root_hash = merge_subtrees_root(&chaining_values[0], &chaining_values[1], Mode::Hash);
                assert_eq!(expected_hash, root_hash);
            }
        }
    }

    #[test]
    fn test_keyed_hash_xof() {
        let group0 = &[42; 4096];
        let group1 = &[43; 4095];
        let mut input = [0; 8191];
        input[..4096].copy_from_slice(group0);
        input[4096..].copy_from_slice(group1);
        let key = &[44; 32];

        let mut expected_output = [0; 100];
        Hasher::new_with(crate::Mode::Keyed(&key)).update(&input).finalize_xof().fill(&mut expected_output);

        let mut hazmat_output = [0; 100];
        let left = Hasher::new_with(crate::Mode::Keyed(key)).update(group0).finalize_non_root();
        let right = Hasher::new_with(crate::Mode::Keyed(key)).set_input_offset(group0.len() as u64).update(group1).finalize_non_root();
        merge_subtrees_root_xof(&left, &right, Mode::KeyedHash(&key)).fill(&mut hazmat_output);
        assert_eq!(expected_output, hazmat_output);
    }

    #[test]
    fn test_derive_key() {
        let context = "foo";
        let mut input = [0; 1025];
        crate::test::paint_test_input(&mut input);
        let expected = *crate::hash_with(crate::Mode::DeriveKey(context), &input).as_bytes();

        let cx_key = hash_derive_key_context(context);
        let left = Hasher::new_from_context_key(&cx_key).update(&input[..1024]).finalize_non_root();
        let right = Hasher::new_from_context_key(&cx_key).set_input_offset(1024).update(&input[1024..]).finalize_non_root();
        let derived_key = merge_subtrees_root(&left, &right, Mode::DeriveKeyMaterial(&cx_key)).0;
        assert_eq!(expected, derived_key);
    }
}
