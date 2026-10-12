pub fn crypto_hash(out: &mut [u8; 32], m: &[u8]) {
  out.copy_from_slice(blake3_servil::hash(m).as_bytes())
}
