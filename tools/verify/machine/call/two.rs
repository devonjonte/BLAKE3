#![no_std]
/// Each word replaced by the fold up to and including it; the fold of all of them.
#[no_mangle]
#[inline(never)]
pub extern "C" fn scan(words: &mut [u32], seed: u32) -> u32 {
    let mut a = seed;
    for w in words.iter_mut() {
        a = a.rotate_left(5) ^ *w;
        *w = a;
    }
    a
}

/// Two slices scanned one after the other, the second seeded by the first's fold.
#[no_mangle]
pub extern "C" fn scan2(first: &mut [u32], second: &mut [u32], seed: u32) -> u32 {
    let mid = scan(first, seed);
    scan(second, mid)
}
