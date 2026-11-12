//! Trial: `push` of the chaining-value stack, AArch64. The bytes linked are the instruction words named in
//! the theorem `push_arm_meets`, which this crate's build checked before it assembled them (build.rs).

#[cfg(target_arch = "aarch64")]
extern "C" {
    /// Puts the 32 bytes at `cv` on the stack at `st` (count in its first 8 bytes, values from byte 32).
    /// The contract is `Push.byteContract`: the stack holds fewer than 55 values, and the two are apart.
    pub fn b3l_push(st: *mut u8, cv: *const u8);
}

#[cfg(all(test, target_arch = "aarch64"))]
mod tests {
    #[test]
    fn test_push_puts_the_value_on_the_stack() {
        let mut stack = [0u64; 1792 / 8];
        let st = stack.as_mut_ptr() as *mut u8;
        for k in 0..3u8 {
            let cv: [u8; 32] = core::array::from_fn(|i| k.wrapping_mul(37).wrapping_add(i as u8));
            unsafe { super::b3l_push(st, cv.as_ptr()) };
            let bytes = unsafe { core::slice::from_raw_parts(st, 1792) };
            assert_eq!(u64::from_le_bytes(bytes[..8].try_into().unwrap()), k as u64 + 1);
            let at = 32 + 32 * k as usize;
            assert_eq!(&bytes[at..at + 32], &cv);
            assert!(bytes[at + 32..].iter().all(|&b| b == 0));
        }
    }
}
