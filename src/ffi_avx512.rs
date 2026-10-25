use crate::{BLOCK_LEN, CVWords, IncrementCounter, OUT_LEN};

// Unsafe because this may only be called on platforms supporting AVX-512.
pub unsafe fn compress_in_place(cv: &mut CVWords, block: &[u8; BLOCK_LEN], block_len: u8, counter: u64, flags: u8) {
    unsafe { ffi::blake3_servil_compress_in_place_avx512(cv.as_mut_ptr(), block.as_ptr(), block_len, counter, flags) }
}

// Unsafe because this may only be called on platforms supporting AVX-512.
pub unsafe fn compress_xof(cv: &CVWords, block: &[u8; BLOCK_LEN], block_len: u8, counter: u64, flags: u8) -> [u8; 64] {
    unsafe {
        let mut out = [0u8; 64];
        ffi::blake3_servil_compress_xof_avx512(cv.as_ptr(), block.as_ptr(), block_len, counter, flags, out.as_mut_ptr());
        out
    }
}

// Unsafe because this may only be called on platforms supporting AVX-512.
pub unsafe fn hash_many<const N: usize>(
    inputs: &[&[u8; N]],
    key: &CVWords,
    counter: u64,
    increment_counter: IncrementCounter,
    flags: u8,
    flags_start: u8,
    flags_end: u8,
    out: &mut [u8],
) {
    unsafe {
        // The Rust hash_many implementations do bounds checking on the `out`
        // array, but the C implementations don't. Even though this is an unsafe
        // function, assert the bounds here.
        assert!(out.len() >= inputs.len() * OUT_LEN);
        ffi::blake3_servil_hash_many_avx512(
            inputs.as_ptr() as *const *const u8,
            inputs.len(),
            N / BLOCK_LEN,
            key.as_ptr(),
            counter,
            increment_counter.yes(),
            flags,
            flags_start,
            flags_end,
            out.as_mut_ptr(),
        )
    }
}

/// The most blocks one call of the AVX-512 extended-output kernel makes:
/// its proof covers 1 to 32 (tools/verify/prove_x86.py, xof_many), so a
/// longer output takes one call per 32 blocks and every call stays within
/// what is proved (#163). The kernel is in the Unix assembly alone, as
/// `xof_many` below.
#[cfg(unix)]
pub const XOF_PROVED_BLOCKS: usize = 32;

// Unsafe because this may only be called on platforms supporting AVX-512.
#[cfg(unix)]
pub unsafe fn xof_many(cv: &CVWords, block: &[u8; BLOCK_LEN], block_len: u8, counter: u64, flags: u8, out: &mut [u8]) {
    debug_assert_eq!(0, out.len() % BLOCK_LEN, "whole blocks only");
    for (i, part) in out.chunks_mut(XOF_PROVED_BLOCKS * BLOCK_LEN).enumerate() {
        let blocks = part.len() / BLOCK_LEN;
        debug_assert!((1..=XOF_PROVED_BLOCKS).contains(&blocks), "a call within the proof's 1 to 32 blocks");
        let at = counter + (i * XOF_PROVED_BLOCKS) as u64;
        unsafe { ffi::blake3_servil_xof_many_avx512(cv.as_ptr(), block.as_ptr(), block_len, at, flags, part.as_mut_ptr(), blocks) };
    }
}

pub mod ffi {
    unsafe extern "C" {
        pub fn blake3_servil_compress_in_place_avx512(cv: *mut u32, block: *const u8, block_len: u8, counter: u64, flags: u8);
        pub fn blake3_servil_compress_xof_avx512(cv: *const u32, block: *const u8, block_len: u8, counter: u64, flags: u8, out: *mut u8);
        pub fn blake3_servil_hash_many_avx512(
            inputs: *const *const u8,
            num_inputs: usize,
            blocks: usize,
            key: *const u32,
            counter: u64,
            increment_counter: bool,
            flags: u8,
            flags_start: u8,
            flags_end: u8,
            out: *mut u8,
        );
        #[cfg(unix)]
        pub fn blake3_servil_xof_many_avx512(cv: *const u32, block: *const u8, block_len: u8, counter: u64, flags: u8, out: *mut u8, outblocks: usize);
    }
}

#[cfg(all(test, unix))]
mod test {
    use super::*;

    #[test]
    fn test_xof_many() {
        if !crate::platform::avx512_detected() {
            return;
        }
        crate::test::test_xof_many_fn(xof_many);
    }
}
