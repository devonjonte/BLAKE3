//! Probe (probe/after-gap): what a call costs after the program's thread
//! slept 1 ms (the benchmark's gap), against the same call back to back,
//! for hash() at sizes on each side of the kernels' boundaries, and for
//! SHA-256 (sha2) as the control. Variants after the gap: a few
//! microseconds of integer work first (does the clock's ramp explain
//! it?), and one 64-byte hash first (does the first vector work pay?).
//! Wall time and cycles per core kind (clocks).
use sha2::Digest;
use std::hint::black_box;

const GAP: u64 = 1_000_000;

fn spin(iterations: u64) -> u64 {
    let mut x = 1u64;
    for i in 0..iterations {
        x = black_box(x.wrapping_mul(6364136223846793005).wrapping_add(i));
    }
    x
}

fn show(label: &str, b: clocks::Batch) {
    println!("  {label:<28} {}", b.show());
}

fn main() {
    blake3_servil::initialize_multithreaded();
    let input = vec![7u8; 1 << 20];
    for len in [64usize, 1024, 2048, 4096, 8192, 16384, 65536] {
        let m = &input[..len];
        println!("{len} B");
        let bb = clocks::measure(5, 2_000_000, || { black_box(blake3_servil::hash(black_box(m))); });
        show("servil back to back", bb[2]);
        let calls = 300;
        show("servil after gap", clocks::measure_after_gaps(calls, GAP, || { black_box(blake3_servil::hash(black_box(m))); }));
        show("servil after gap+spin 20us", {
            let mut b = clocks::Batch { calls, wall_ns: 0, counts: None };
            for _ in 0..calls {
                std::thread::sleep(std::time::Duration::from_nanos(GAP));
                black_box(spin(80_000));
                let t = clocks::now();
                black_box(blake3_servil::hash(black_box(m)));
                b.wall_ns += clocks::since_ns(t);
            }
            b
        });
        show("servil after gap+hash(64)", {
            let mut b = clocks::Batch { calls, wall_ns: 0, counts: None };
            for _ in 0..calls {
                std::thread::sleep(std::time::Duration::from_nanos(GAP));
                black_box(blake3_servil::hash(black_box(&input[..64])));
                let t = clocks::now();
                black_box(blake3_servil::hash(black_box(m)));
                b.wall_ns += clocks::since_ns(t);
            }
            b
        });
        show("servil after gap, 2nd call", {
            let mut b = clocks::Batch { calls, wall_ns: 0, counts: None };
            for _ in 0..calls {
                std::thread::sleep(std::time::Duration::from_nanos(GAP));
                black_box(blake3_servil::hash(black_box(m)));
                let t = clocks::now();
                black_box(blake3_servil::hash(black_box(m)));
                b.wall_ns += clocks::since_ns(t);
            }
            b
        });
        let bb = clocks::measure(5, 2_000_000, || { black_box(sha2::Sha256::digest(black_box(m))); });
        show("sha256 back to back", bb[2]);
        show("sha256 after gap", clocks::measure_after_gaps(calls, GAP, || { black_box(sha2::Sha256::digest(black_box(m))); }));
        show("spin(1000) after gap", clocks::measure_after_gaps(calls, GAP, || { black_box(spin(1000)); }));
        let bb = clocks::measure(5, 2_000_000, || { black_box(spin(1000)); });
        show("spin(1000) back to back", bb[2]);
    }
}
