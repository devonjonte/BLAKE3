//! #196: how the pool's work spreads over its workers. One caller hashes
//! `LEN`-byte messages (one-shot hash_multithreaded) for SECS seconds; then
//! each thread's user CPU time from /proc/self/task/*/stat. Prints the
//! caller's, each worker's share, and the total. `worker_share SECS LEN`.
use blake3_servil::performance::{hash_multithreaded, Block};
use blake3_servil::Mode;
use std::time::{Duration, Instant};

fn thread_times() -> Vec<(String, u64)> {
    let mut v = Vec::new();
    for e in std::fs::read_dir("/proc/self/task").unwrap() {
        let p = e.unwrap().path();
        let stat = std::fs::read_to_string(p.join("stat")).unwrap();
        let name = stat.split('(').nth(1).unwrap().split(')').next().unwrap().to_owned();
        let after = stat.rsplit(')').next().unwrap();
        let f: Vec<&str> = after.split_whitespace().collect();
        let ticks: u64 = f[11].parse::<u64>().unwrap() + f[12].parse::<u64>().unwrap();
        v.push((name, ticks));
    }
    v
}

fn main() {
    blake3_servil::initialize_multithreaded(None);
    let secs: u64 = std::env::args().nth(1).map_or(3, |a| a.parse().unwrap());
    let len: usize = std::env::args().nth(2).map_or(64 << 20, |a| a.parse().unwrap());
    let blocks: Vec<Block> = (0..len / 64).map(|i| Block([i as u8; 64])).collect();
    std::hint::black_box(hash_multithreaded(Mode::Plain, &blocks, len));
    let before = thread_times();
    let end = Instant::now() + Duration::from_secs(secs);
    let t = Instant::now();
    let mut n = 0u64;
    while Instant::now() < end {
        std::hint::black_box(hash_multithreaded(Mode::Plain, &blocks, len));
        n += 1;
    }
    let dt = t.elapsed().as_secs_f64();
    let after = thread_times();
    let mut shares: Vec<(String, u64)> = after
        .iter()
        .map(|(name, a)| (name.clone(), a - before.iter().find(|(n, _)| n == name).map_or(0, |(_, b)| *b)))
        .collect();
    shares.sort_by(|a, b| b.1.cmp(&a.1));
    let total: u64 = shares.iter().map(|s| s.1).sum();
    let ticks_per_s = 100.0;
    println!("{:.2} GB/s; CPU {:.1} of {} threads busy on average", n as f64 * len as f64 / dt / 1e9, total as f64 / ticks_per_s / dt, shares.len());
    let w: Vec<String> = shares.iter().map(|(name, t)| format!("{}:{:.0}%", name, 100.0 * *t as f64 / total.max(1) as f64)).collect();
    println!("{}", w.join(" "));
}
