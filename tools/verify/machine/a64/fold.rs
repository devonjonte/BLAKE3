#![no_std]
/// Every word of `words` folded into `seed`, first to last: rotate left by five, xor the word.
#[no_mangle]
pub extern "C" fn fold(words: &[u32], seed: u32) -> u32 {
    let mut a = seed;
    for &w in words {
        a = a.rotate_left(5) ^ w;
    }
    a
}

/// The same fold, each word replaced by the fold up to and including it.
#[no_mangle]
pub extern "C" fn scan(words: &mut [u32], seed: u32) -> u32 {
    let mut a = seed;
    for w in words.iter_mut() {
        a = a.rotate_left(5) ^ *w;
        *w = a;
    }
    a
}
