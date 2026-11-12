use std::hint::black_box;
use std::time::Instant;

extern "C" {
    #[cfg_attr(target_arch = "aarch64", link_name = "b3l_hex_neon")]
    #[cfg_attr(target_arch = "x86_64", link_name = "b3l_hex")]
    fn hex_kernel(out: *mut u8, hash: *const u8);
}

fn main() {
    // agreement first: a million hashes, every byte value among them
    let mut s: u64 = 88172645463325252;
    let mut differ = 0u64;
    let mut hashes = Vec::new();
    for n in 0..1_000_000u32 {
        let mut h = [0u8; 32];
        for b in h.iter_mut() {
            s ^= s << 13; s ^= s >> 7; s ^= s << 17;
            *b = (s >> 24) as u8;
        }
        if n < 256 { h = [n as u8; 32]; }
        let hash = blake3::Hash::from_bytes(h);
        let mut out = [0u8; 64];
        unsafe { hex_kernel(out.as_mut_ptr(), h.as_ptr()) };
        if hash.to_hex().as_bytes() != &out[..] { differ += 1; }
        if n < 4096 { hashes.push(h); }
    }
    println!("1000000 hashes: {differ} differ from the crate's to_hex");
    let rounds = 20_000usize;
    for pass in 0..3 {
        let t = Instant::now();
        let mut acc = 0u64;
        for _ in 0..rounds {
            for h in &hashes {
                let hash = blake3::Hash::from_bytes(*black_box(h));
                let x = hash.to_hex();
                acc = acc.wrapping_add(black_box(&x).as_bytes()[7] as u64);
            }
        }
        let crate_ns = t.elapsed().as_nanos() as f64 / (rounds * hashes.len()) as f64;
        let t = Instant::now();
        for _ in 0..rounds {
            for h in &hashes {
                let mut out = [0u8; 64];
                unsafe { hex_kernel(out.as_mut_ptr(), black_box(h).as_ptr()) };
                acc = acc.wrapping_add(black_box(&out)[7] as u64);
            }
        }
        let kernel_ns = t.elapsed().as_nanos() as f64 / (rounds * hashes.len()) as f64;
        println!("pass {pass}: the crate's to_hex {crate_ns:.2} ns, the kernel {kernel_ns:.2} ns ({acc})");
    }
}
