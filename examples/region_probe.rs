//! Probe (b3sum, large files from storage): a mapped file split in halves,
//! as official BLAKE3's rayon join does, down to `threads` contiguous
//! regions; each thread hashes its own region front to back on one core
//! (hazmat subtrees), then the subtrees merge. Prints the hash, as b3sum.
//!     region_probe THREADS FILE
use blake3_servil::hazmat::{left_subtree_len, merge_subtrees_non_root, merge_subtrees_root, ChainingValue, HasherExt, Mode};
use blake3_servil::Hasher;

fn cv(input: &[u8], offset: u64, threads: usize) -> ChainingValue {
    if threads <= 1 || input.len() <= 1 << 20 {
        return Hasher::new().set_input_offset(offset).update(input).finalize_non_root();
    }
    let left = left_subtree_len(input.len() as u64) as usize;
    let (l, r) = input.split_at(left);
    let (a, b) = std::thread::scope(|s| {
        let a = s.spawn(|| cv(l, offset, threads / 2));
        let b = cv(r, offset + left as u64, threads - threads / 2);
        (a.join().unwrap(), b)
    });
    merge_subtrees_non_root(&a, &b, Mode::Hash)
}

fn main() {
    blake3_servil::initialize();
    let args: Vec<String> = std::env::args().collect();
    let threads: usize = args[1].parse().unwrap();
    let file = std::fs::File::open(&args[2]).unwrap();
    // Sound: a probe's own file, held open and unchanged while it runs.
    let map = unsafe { memmap2::Mmap::map(&file) }.unwrap();
    let left = left_subtree_len(map.len() as u64) as usize;
    let (l, r) = map.split_at(left);
    let (a, b) = std::thread::scope(|s| {
        let a = s.spawn(|| cv(l, 0, threads / 2));
        let b = cv(r, left as u64, threads - threads / 2);
        (a.join().unwrap(), b)
    });
    let hash = merge_subtrees_root(&a, &b, Mode::Hash);
    println!("{}  {}", hash, args[2]);
}
