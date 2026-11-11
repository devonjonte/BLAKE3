//! What `impl PartialEq for Hash` compiles to: blake3-servil-core's `Hash` is `[u8; 32]`, and its
//! `eq` is `constant_time_eq::constant_time_eq_32(&self.0, &other.0)`.
#[no_mangle]
pub fn hash_eq(a: &[u8; 32], b: &[u8; 32]) -> bool {
    constant_time_eq::constant_time_eq_32(a, b)
}
