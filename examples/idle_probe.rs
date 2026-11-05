//! Per visit: which idle state CPU 2 entered during the 1 ms pause (its
//! cpuidle usage counters, read before and after the sleep, outside the
//! timed call), beside the call's time. Run pinned to CPU 2.
//! performance::hash_many, 16 messages of 64 B (bench-hashes IdleManyMessages).
use blake3_servil::performance::{hash_many, Batch, Block};
use blake3_servil::Mode;
use std::time::{Duration, Instant};

fn usage() -> Vec<u64> {
    (0..5)
        .map(|s| {
            std::fs::read_to_string(format!("/sys/devices/system/cpu/cpu2/cpuidle/state{s}/usage"))
                .unwrap()
                .trim()
                .parse()
                .unwrap()
        })
        .collect()
}

fn main() {
    blake3_servil::initialize();
    let visits: usize = std::env::args().nth(1).map_or(2000, |a| a.parse().unwrap());
    let mut blocks = vec![Block([0u8; 64]); 16];
    let mut out = vec![[0u8; 32]; 16];
    let start = Instant::now();
    for v in 0..visits {
        let before = usage();
        std::thread::sleep(Duration::from_millis(1));
        let after = usage();
        for (i, b) in blocks.iter_mut().enumerate() {
            b.0.fill((v + i) as u8);
        }
        let t = Instant::now();
        hash_many(Mode::Plain, &Batch::from_blocks(&blocks, 64), &mut out);
        let e = t.elapsed().as_nanos() as u64;
        std::hint::black_box(&out);
        let d: Vec<u64> = before.iter().zip(&after).map(|(b, a)| a - b).collect();
        println!("{}\t{}\t{}", start.elapsed().as_micros(), e, d.iter().map(u64::to_string).collect::<Vec<_>>().join(","));
    }
}
