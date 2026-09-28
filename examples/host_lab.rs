//! Probe (probe/hasher-small): a short message through Hasher (new, one
//! update, finalize) against hash(), after a 1 ms gap and back to back;
//! and each step of the Hasher timed. Wall time (clocks).
use std::hint::black_box;

fn after_gaps(label: &str, f: &dyn Fn()) {
    let b = clocks::measure_after_gaps(400, 1_000_000, || f());
    println!("{label:<40} after the gap {}", b.show());
}
fn back_to_back(label: &str, f: &dyn Fn()) {
    let b = clocks::measure(5, 2_000_000, || f());
    println!("{label:<40} back to back  {}", b[2].show());
}

fn main() {
    blake3_servil::initialize_multithreaded();
    let data = vec![7u8; 4096];
    for len in [64usize, 128, 1024, 4096] {
        let m = &data[..len];
        let hash = || { black_box(blake3_servil::hash(black_box(m))); };
        let hasher = || { let mut h = blake3_servil::Hasher::new(); h.update(black_box(m)); black_box(h.finalize()); };
        let hasher_mt = || { let mut h = blake3_servil::Hasher::new(); h.update_multithreaded(black_box(m)); black_box(h.finalize()); };
        let new_only = || { black_box(blake3_servil::Hasher::new()); };
        after_gaps(&format!("{len} B hash"), &hash);
        after_gaps(&format!("{len} B Hasher"), &hasher);
        after_gaps(&format!("{len} B Hasher, update_multithreaded"), &hasher_mt);
        back_to_back(&format!("{len} B hash"), &hash);
        back_to_back(&format!("{len} B Hasher"), &hasher);
        back_to_back("Hasher::new alone", &new_only);
    }
}
