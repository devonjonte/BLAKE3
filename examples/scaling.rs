//! Threads of one process hashing at once: n threads, each hashing its own
//! input back to back with `hash` (1 MiB) and `hash_many` (4096 one-block
//! messages); per-thread time, median and slowest thread, with the clock
//! each ran at where the platform counts cycles. The case where threads
//! would share an SME unit; compare with `--features no_sme2`.
//!
//!     cargo run --release --example scaling
use std::sync::{Arc, Barrier};

/// (picoseconds per unit, the thread's counts) for one thread.
fn one_thread(len: usize, batch: bool, k: usize, barrier: &Barrier) -> (u64, Option<clocks::Counts>) {
    let input: Vec<u8> = (0..len).map(|i| (i * 31 + k) as u8).collect();
    let mut digests = vec![[0u8; 32]; len / 64];
    let mut hash = || {
        if batch {
            blake3_servil::hash_many(std::hint::black_box(&input), 64, &mut digests);
        } else {
            std::hint::black_box(blake3_servil::hash(std::hint::black_box(&input)));
        }
    };
    for _ in 0..3 {
        hash();
    }
    barrier.wait();
    let before = clocks::Counts::read();
    let started = clocks::now();
    let mut count = 0u64;
    while clocks::since_ns(started) < 150_000_000 {
        hash();
        count += 1;
    }
    let wall_ns = clocks::since_ns(started);
    let counts = before.zip(clocks::Counts::read()).map(|(b, a)| a.since(b));
    let units = count * if batch { len / 64 } else { len } as u64;
    ((wall_ns * 1000 + units / 2) / units, counts)
}

/// (median, slowest) thread of n: picoseconds per unit and the clock it ran at.
fn per_thread(n: usize, len: usize, batch: bool) -> [(u64, String); 2] {
    let barrier = Arc::new(Barrier::new(n));
    let threads: Vec<_> = (0..n)
        .map(|k| {
            let barrier = barrier.clone();
            std::thread::spawn(move || one_thread(len, batch, k, &barrier))
        })
        .collect();
    let mut results: Vec<(u64, Option<clocks::Counts>)> = threads.into_iter().map(|t| t.join().unwrap()).collect();
    results.sort_by_key(|r| r.0);
    let show = |(ps, counts): (u64, Option<clocks::Counts>)| (ps, counts.map_or("-".to_owned(), |c| format!("{}MHz", c.mhz())));
    [show(results[results.len() / 2]), show(results[results.len() - 1])]
}

fn main() {
    let cpus = std::thread::available_parallelism().map(|n| n.get()).unwrap_or(1);
    let counts: Vec<usize> = [1, 2, 4, 8, 12, 16].into_iter().filter(|&n| n <= cpus).collect();
    println!("platform {}; per thread, median/slowest in ns per unit (the clock each ran at, - without cycle counts)", blake3_servil::kernel_report().platform);
    let ns = |ps: u64| format!("{}.{:03}", ps / 1000, ps % 1000);
    for (label, len, batch) in [("hash 1 MiB, ns/B", 1 << 20, false), ("hash_many 4096 x 64 B, ns/msg", 4096 * 64, true)] {
        let mut line = format!("{label:30}");
        for &n in &counts {
            let [(m, mc), (s, sc)] = per_thread(n, len, batch);
            line += &format!("  n={n:<2} {} ({mc})/{} ({sc})", ns(m), ns(s));
        }
        println!("{line}");
    }
}
