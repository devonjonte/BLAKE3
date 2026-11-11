#![allow(unused_parens)]
#[no_mangle]
pub fn rotxor(words: &mut [u32], seed: u32) -> u32 {
    let mut a = seed;
    for word in words.iter_mut() {
        let w = *word;
        a = (a.rotate_left(5) ^ w);
        *word = a;
    }
    a
}
#[no_mangle]
pub fn addrot(words: &mut [u32], seed: u32) -> u32 {
    let mut a = seed;
    for word in words.iter_mut() {
        let w = *word;
        a = (a.wrapping_add(w).rotate_left(7) ^ a);
        *word = a;
    }
    a
}
#[no_mangle]
pub fn mix(words: &mut [u32], seed: u32) -> u32 {
    let mut a = seed;
    for word in words.iter_mut() {
        let w = *word;
        a = ((a & 252645135u32) | ((!w) & 4042322160u32)).wrapping_add((w >> 3));
        *word = a;
    }
    a
}
#[no_mangle]
pub fn sum(words: &mut [u32], seed: u32) -> u32 {
    let mut a = seed;
    for word in words.iter_mut() {
        let w = *word;
        a = a.wrapping_add(w);
        *word = a;
    }
    a
}
#[no_mangle]
pub fn quarter(words: &mut [u32], seed: u32) -> u32 {
    let mut a = seed;
    for word in words.iter_mut() {
        let w = *word;
        a = (a.wrapping_add(w).wrapping_add(2654435769u32).rotate_left(16) ^ w);
        *word = a;
    }
    a
}
#[no_mangle]
pub fn blend(words: &mut [u32], seed: u32) -> u32 {
    let mut a = seed;
    for word in words.iter_mut() {
        let w = *word;
        a = ((a & w) | w.rotate_left(13));
        *word = a;
    }
    a
}
#[no_mangle]
pub fn invert(words: &mut [u32], seed: u32) -> u32 {
    let mut a = seed;
    for word in words.iter_mut() {
        let w = *word;
        a = (!a.wrapping_add(w.rotate_left(1)));
        *word = a;
    }
    a
}
#[no_mangle]
pub fn shift(words: &mut [u32], seed: u32) -> u32 {
    let mut a = seed;
    for word in words.iter_mut() {
        let w = *word;
        a = ((a >> 3) ^ w.wrapping_add(a));
        *word = a;
    }
    a
}
