//! The batch calls' input: [`Block`]s, 64 bytes each on a 64-byte boundary,
//! and [`Batch`], which holds messages of one length in them with every
//! byte past each message zero (BLAKE3 #146, John Servil's proposal; the
//! owning builder, Zooko's choice of October 24).

use crate::BLOCK_LEN;

/// 64 bytes on a 64-byte boundary: the unit the batch calls read. A batch
/// is `&[Block]`, each message starting a block and taking whole blocks
/// (one for an empty message), so every message starts on a cache line.
///
/// The bytes past each message's end, to its last block's end, are zero:
/// the caller's to write, checked in debug builds (another byte there
/// changes that message's hash). [`Batch`] keeps them zero by
/// construction.
#[repr(C, align(64))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Block(pub [u8; BLOCK_LEN]);

impl Block {
    /// A block of zeros.
    pub const ZERO: Block = Block([0; BLOCK_LEN]);

    /// The blocks' bytes, in order.
    pub fn bytes(blocks: &[Block]) -> &[u8] {
        // Sound: a Block is 64 bytes with no padding, and u8 needs no alignment.
        unsafe { core::slice::from_raw_parts(blocks.as_ptr().cast(), blocks.len() * BLOCK_LEN) }
    }

    /// The blocks' bytes, in order, for writing.
    pub fn bytes_mut(blocks: &mut [Block]) -> &mut [u8] {
        // Sound: as in bytes, and the borrow is exclusive.
        unsafe { core::slice::from_raw_parts_mut(blocks.as_mut_ptr().cast(), blocks.len() * BLOCK_LEN) }
    }

    /// The blocks as 32-byte digests, two a block: a Merkle layer's digests
    /// written straight into the next layer's input (its 64-byte messages,
    /// two children each). A layer of an odd count leaves a slot to spare:
    /// slice it, `&mut Block::digests_mut(blocks)[..count]`.
    pub fn digests_mut(blocks: &mut [Block]) -> &mut [[u8; 32]] {
        // Sound: a [u8; 32] is 32 bytes with alignment 1; two fill a Block.
        unsafe { core::slice::from_raw_parts_mut(blocks.as_mut_ptr().cast(), blocks.len() * 2) }
    }

    /// `bytes` as blocks, without a copy, when they start on a 64-byte
    /// boundary and are whole blocks (bytes already in place, such as a
    /// mapped file's records), or are empty: `None` otherwise.
    pub fn from_bytes(bytes: &[u8]) -> Option<&[Block]> {
        // An empty slice's pointer says nothing of placement.
        if bytes.is_empty() {
            return Some(&[]);
        }
        if bytes.as_ptr().align_offset(BLOCK_LEN) != 0 || bytes.len() % BLOCK_LEN != 0 {
            return None;
        }
        // Sound: aligned and whole blocks, just checked; Block has no padding.
        Some(unsafe { core::slice::from_raw_parts(bytes.as_ptr().cast(), bytes.len() / BLOCK_LEN) })
    }
}

impl core::fmt::Debug for Block {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "Block({:02x?})", &self.0[..])
    }
}

/// Messages of one length in [`Block`]s, ready for the batch calls: each
/// message starts a block, and every byte past each message's end stays
/// zero, since the only bytes a `Batch` lets the program write are the
/// messages' own. The zeros are written once, when it is made, so refilling
/// a `Batch` with new messages costs only their bytes.
///
/// ```
/// # blake3_servil::initialize();
/// use blake3_servil::{Mode, convenience, performance::{self, Batch}};
/// let mut batch = Batch::new(100, 3);
/// for i in 0..3 {
///     batch.set(i, &[i as u8; 100]);
/// }
/// let mut out = [[0u8; 32]; 3];
/// performance::hash_many(Mode::Plain, batch.blocks(), 100, &mut out);
/// assert_eq!(out[2], *convenience::hash(&[2u8; 100]).as_bytes());
///
/// // Read straight into a message's own bytes.
/// batch.message_mut(1).copy_from_slice(&[9u8; 100]);
/// performance::hash_many(Mode::Plain, batch.blocks(), 100, &mut out);
/// assert_eq!(out[1], *convenience::hash(&[9u8; 100]).as_bytes());
/// ```
#[cfg(feature = "std")]
#[derive(Clone)]
pub struct Batch {
    blocks: std::vec::Vec<Block>,
    message_len: usize,
    count: usize,
}

#[cfg(feature = "std")]
impl Batch {
    /// `count` messages of `message_len` bytes, every byte zero. The zeros
    /// are written now, so all of a `Batch`'s memory is resident from its
    /// making, not as its pages are first touched: make one and refill it.
    pub fn new(message_len: usize, count: usize) -> Self {
        let per = Self::blocks_per(message_len);
        Batch { blocks: std::vec![Block::ZERO; per * count], message_len, count }
    }

    /// The blocks each message of `message_len` bytes takes: its bytes in
    /// whole blocks, one for an empty message.
    fn blocks_per(message_len: usize) -> usize {
        message_len.div_ceil(BLOCK_LEN).max(1)
    }

    /// The messages' length.
    pub fn message_len(&self) -> usize {
        self.message_len
    }

    /// How many messages it holds.
    pub fn len(&self) -> usize {
        self.count
    }

    /// Whether it holds no messages.
    pub fn is_empty(&self) -> bool {
        self.count == 0
    }

    /// Message `i`'s bytes, for writing: `message_len` of them, no more.
    pub fn message_mut(&mut self, i: usize) -> &mut [u8] {
        assert!(i < self.count, "message {i} of a batch of {}", self.count);
        let per = Self::blocks_per(self.message_len);
        &mut Block::bytes_mut(&mut self.blocks[i * per..][..per])[..self.message_len]
    }

    /// Message `i` becomes `message`, `message_len` bytes.
    pub fn set(&mut self, i: usize, message: &[u8]) {
        self.message_mut(i).copy_from_slice(message);
    }

    /// The batch as the batch calls take it.
    pub fn blocks(&self) -> &[Block] {
        &self.blocks
    }

    /// Every byte for writing, where no message has bytes past its end to
    /// keep zero: `message_len` a multiple of 64 (a Merkle layer's parents,
    /// 64 bytes each, whose digests [`Block::digests_mut`] writes in place).
    pub fn blocks_mut(&mut self) -> &mut [Block] {
        assert!(self.message_len % BLOCK_LEN == 0 && self.message_len > 0, "a batch whose messages leave no bytes past their ends ({} B)", self.message_len);
        &mut self.blocks
    }
}

#[cfg(all(test, feature = "std"))]
mod test {
    use super::*;
    use crate::Mode;
    use crate::performance::hash_many;

    /// Every byte a Batch lets the program write, written nonzero: every
    /// byte past each message's end stays zero, and each digest is the
    /// message's own (convenience::hash, an independent path).
    #[test]
    fn test_a_batch_keeps_the_bytes_past_its_messages_zero() {
        crate::initialize();
        for len in [0, 1, 63, 64, 65, 100, 1000, 1024, 1025] {
            let mut batch = Batch::new(len, 5);
            for round in 1..=2u8 {
                for i in 0..batch.len() {
                    batch.message_mut(i).fill(round * 16 + i as u8);
                }
                let per = len.div_ceil(BLOCK_LEN).max(1) * BLOCK_LEN;
                for (i, slot) in Block::bytes(batch.blocks()).chunks(per).enumerate() {
                    assert!(slot[len..].iter().all(|&b| b == 0), "{len} B, message {i}: its padding");
                }
                let mut out = [[0u8; 32]; 5];
                hash_many(Mode::Plain, batch.blocks(), len, &mut out);
                for (i, d) in out.iter().enumerate() {
                    assert_eq!(*d, *crate::convenience::hash(&std::vec![round * 16 + i as u8; len]).as_bytes(), "{len} B, message {i}, round {round}");
                }
            }
        }
    }

    #[test]
    fn test_from_bytes_takes_aligned_whole_blocks_only() {
        let blocks = [Block::ZERO; 3];
        let bytes = Block::bytes(&blocks);
        assert_eq!(Block::from_bytes(bytes).map(<[Block]>::len), Some(3));
        assert_eq!(Block::from_bytes(&bytes[..128]).map(<[Block]>::len), Some(2));
        assert!(Block::from_bytes(&bytes[16..80]).is_none(), "16 bytes into a line");
        assert!(Block::from_bytes(&bytes[..100]).is_none(), "a partial block");
        assert_eq!(Block::from_bytes(&[]).map(<[Block]>::len), Some(0));
    }

    #[test]
    #[should_panic(expected = "leave no bytes past their ends")]
    fn test_blocks_mut_refuses_messages_with_padding() {
        Batch::new(100, 2).blocks_mut();
    }

    /// A Merkle layer: leaves' digests written by hash_many straight into
    /// the parents' batch, two a block, then the parents hashed: the root
    /// of four leaves is a parent of parents, keyed alike (as a tree's
    /// caller keys its nodes).
    #[test]
    fn test_a_merkle_layer_lands_in_the_next_layers_blocks() {
        crate::initialize();
        let key = [5u8; 32];
        let mut leaves = Batch::new(256, 4);
        (0..4).for_each(|i| leaves.set(i, &[i as u8; 256]));
        let mut parents = Batch::new(64, 2);
        hash_many(Mode::Keyed(&key), leaves.blocks(), 256, Block::digests_mut(parents.blocks_mut()));
        let mut root = [[0u8; 32]; 2];
        hash_many(Mode::Keyed(&key), parents.blocks(), 64, &mut root);
        let leaf = |i: u8| *crate::convenience::hash_with(Mode::Keyed(&key), &[i; 256]).as_bytes();
        let parent = |a: [u8; 32], b: [u8; 32]| *crate::convenience::hash_with(Mode::Keyed(&key), &[a, b].concat()).as_bytes();
        assert_eq!(root[0], parent(leaf(0), leaf(1)));
        assert_eq!(root[1], parent(leaf(2), leaf(3)));
    }

    /// What a Batch says of itself: its message length and count, empty at
    /// zero messages; two digests a block from digests_mut, each landing on
    /// its own 32 bytes; a Block's Debug form names its bytes.
    #[test]
    fn test_a_batch_describes_itself() {
        let batch = Batch::new(100, 3);
        assert_eq!((batch.message_len(), batch.len(), batch.is_empty()), (100, 3, false));
        assert_eq!(batch.blocks().len(), 6, "two blocks a 100-byte message");
        let none = Batch::new(100, 0);
        assert_eq!((none.len(), none.is_empty()), (0, true));
        let mut blocks = [Block::ZERO; 3];
        let digests = Block::digests_mut(&mut blocks);
        assert_eq!(digests.len(), 6);
        digests[5] = [7; 32];
        assert_eq!(&blocks[2].0[32..], &[7u8; 32][..], "the sixth digest is block 2's second half");
        assert_eq!(&blocks[2].0[..32], &[0u8; 32][..]);
        assert!(std::format!("{:?}", Block::ZERO).starts_with("Block([00, 00"));
    }
}
