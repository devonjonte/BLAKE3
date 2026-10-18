//! Experiment (B3_PREAD=1): a large file hashed without mapping it. The
//! file is cut into LEAF-sized subtrees (aligned powers of two, so each is a
//! subtree of BLAKE3's tree); threads take leaves in turn, read each with
//! pread into a buffer of their own, and hash it at its offset (hazmat);
//! the leaves' chaining values merge up the tree.

use blake3::hazmat::{self, ChainingValue, HasherExt};
use std::os::unix::fs::FileExt;
use std::sync::atomic::{AtomicUsize, Ordering};

/// A leaf: a power of two, and a multiple of the read piece.
const LEAF: u64 = pilot("B3_LEAF", 4 << 20);
/// The read piece: a buffer that stays in a core's cache.
const PIECE: usize = 256 << 10;

const fn pilot(_name: &str, default: u64) -> u64 {
    default
}

/// The output of hashing all `len` bytes of `file` (plain mode), on
/// `threads` threads.
pub(crate) fn hash(file: &std::fs::File, len: u64, threads: usize) -> std::io::Result<blake3::OutputReader> {
    let leaves = len.div_ceil(LEAF).max(1) as usize;
    let cvs: Vec<std::sync::Mutex<ChainingValue>> = (0..leaves).map(|_| std::sync::Mutex::new([0; 32])).collect();
    let next = AtomicUsize::new(0);
    let failed = std::sync::Mutex::new(None);
    std::thread::scope(|scope| {
        let work = || {
            let mut buffer = vec![0u8; PIECE];
            loop {
                let leaf = next.fetch_add(1, Ordering::Relaxed);
                if leaf >= leaves {
                    return;
                }
                let start = leaf as u64 * LEAF;
                let end = (start + LEAF).min(len);
                let mut hasher = blake3::Hasher::new();
                hasher.set_input_offset(start);
                let mut at = start;
                while at < end {
                    let n = ((end - at) as usize).min(PIECE);
                    if let Err(e) = file.read_exact_at(&mut buffer[..n], at) {
                        *failed.lock().unwrap() = Some(e);
                        return;
                    }
                    hasher.update(&buffer[..n]);
                    at += n as u64;
                }
                *cvs[leaf].lock().unwrap() = hasher.finalize_non_root();
            }
        };
        for _ in 1..threads.min(leaves) {
            scope.spawn(work);
        }
        work();
    });
    if let Some(e) = failed.into_inner().unwrap() {
        return Err(e);
    }
    let cvs: Vec<ChainingValue> = cvs.into_iter().map(|m| m.into_inner().unwrap()).collect();
    // The root: leaves [0, leaves) cover [0, len); split as BLAKE3 does.
    let left_leaves = |n_bytes: u64| hazmat::left_subtree_len(n_bytes) / LEAF;
    fn subtree(cvs: &[ChainingValue], first: usize, bytes: u64, left_leaves: &dyn Fn(u64) -> u64) -> ChainingValue {
        if bytes <= LEAF {
            return cvs[first];
        }
        let left_bytes = hazmat::left_subtree_len(bytes);
        let l = subtree(cvs, first, left_bytes, left_leaves);
        let r = subtree(cvs, first + (left_bytes / LEAF) as usize, bytes - left_bytes, left_leaves);
        hazmat::merge_subtrees_non_root(&l, &r, hazmat::Mode::Hash)
    }
    let left_bytes = hazmat::left_subtree_len(len);
    let l = subtree(&cvs, 0, left_bytes, &left_leaves);
    let r = subtree(&cvs, (left_bytes / LEAF) as usize, len - left_bytes, &left_leaves);
    Ok(hazmat::merge_subtrees_root_xof(&l, &r, hazmat::Mode::Hash))
}
