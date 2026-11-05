//! Within one process: does a fresh allocation of the input move
//! `performance::hash_many` after a 1 ms pause between two speeds?
//! (bench-hashes's IdleManyMessages, 16 messages of 64 B.) For each of
//! ALLOCS allocations (each new pages, kept alive so the next cannot reuse
//! them), VISITS visits: sleep 1 ms, write the messages, time the call.
//! Prints each allocation's median ns per message and its buffer's address.
use blake3_servil::performance::{hash_many, Batch, Block};
use blake3_servil::Mode;
use std::time::{Duration, Instant};

fn main() {
    blake3_servil::initialize();
    let allocs: usize = std::env::args().nth(1).map_or(40, |a| a.parse().unwrap());
    let visits = 24;
    let mut kept: Vec<Vec<Block>> = Vec::new();
    for a in 0..allocs {
        // 64 KiB of blocks a time, the messages at its start: new pages each time.
        let mut blocks = vec![Block([0u8; 64]); 1024];
        let mut out = vec![[0u8; 32]; 16];
        let mut ns = Vec::with_capacity(visits);
        for v in 0..=visits {
            std::thread::sleep(Duration::from_millis(1));
            for (i, b) in blocks[..16].iter_mut().enumerate() {
                b.0.fill((a + v + i) as u8);
            }
            let t = Instant::now();
            hash_many(Mode::Plain, &Batch::from_blocks(&blocks[..16], 64), &mut out);
            let e = t.elapsed().as_nanos() as u64;
            std::hint::black_box(&out);
            if v > 0 {
                ns.push(e);
            }
        }
        ns.sort_unstable();
        println!("{a}\t{:.1}\t{:p}", ns[ns.len() / 2] as f64 / 16.0, blocks.as_ptr());
        kept.push(blocks);
    }
}
