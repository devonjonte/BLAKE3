//! probe/devon-job-trace: for one-shot multithreaded calls back to back (the
//! lent cells' pattern), how many threads took pieces of each call, when the
//! first worker began, and how long the call took.
//!
//!     cargo run --release --features job-trace --example job_trace -- message 1048576 4000
//!     cargo run --release --features job-trace --example job_trace -- batch 16384 2000
//!
//! `message N`: hash_multithreaded on N bytes; `batch N`: hash_many_multithreaded
//! on N messages of 64 B. Prints the distribution over calls (p10, p50, p90).

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let kind = args.first().map_or("message", String::as_str).to_owned();
    let n: usize = args.get(1).map_or(1 << 20, |a| a.parse().expect("a size"));
    let calls: usize = args.get(2).map_or(2000, |a| a.parse().expect("a count"));
    blake3_servil::initialize_multithreaded();
    let input = vec![0x5au8; if kind == "batch" { n * 64 } else { n }];
    let mut out = vec![[0u8; 32]; if kind == "batch" { n } else { 0 }];
    let mut call = || {
        if kind == "batch" {
            blake3_servil::hash_many_multithreaded(&input, 64, &mut out);
            std::hint::black_box(&out);
        } else {
            std::hint::black_box(blake3_servil::hash_multithreaded(&input));
        }
    };
    for _ in 0..200 {
        call();
    }
    blake3_servil::job_trace::take();
    for _ in 0..calls {
        call();
    }
    let events = blake3_servil::job_trace::take();
    use blake3_servil::job_trace::{CALLER_PIECE, END, WORKER_PIECE};
    // Per job: its end, its first worker piece, its threads, its pieces by kind.
    let mut jobs: std::collections::BTreeMap<u32, (u32, u32, std::collections::BTreeSet<u32>, usize, usize)> = Default::default();
    for &(job, kind, thread, ns) in &events {
        let j = jobs.entry(job).or_insert((0, u32::MAX, Default::default(), 0, 0));
        match kind {
            END => j.0 = ns,
            WORKER_PIECE => {
                j.1 = j.1.min(ns);
                j.2.insert(thread);
                j.3 += 1;
            }
            CALLER_PIECE => j.4 += 1,
            _ => {}
        }
    }
    let jobs: Vec<_> = jobs.into_values().filter(|j| j.0 > 0).collect();
    let pct = |mut v: Vec<u64>| {
        v.sort_unstable();
        let at = |q: usize| v[(v.len() - 1) * q / 100];
        format!("p10 {} p50 {} p90 {}", at(10), at(50), at(90))
    };
    println!("{kind} {n}: {} calls traced", jobs.len());
    println!("call ns:              {}", pct(jobs.iter().map(|j| u64::from(j.0)).collect()));
    println!("first worker ns:      {}", pct(jobs.iter().map(|j| if j.1 == u32::MAX { u64::from(j.0) } else { u64::from(j.1) }).collect()));
    println!("workers a call:       {}", pct(jobs.iter().map(|j| j.2.len() as u64).collect()));
    println!("pieces by workers:    {}", pct(jobs.iter().map(|j| j.3 as u64).collect()));
    println!("pieces by the caller: {}", pct(jobs.iter().map(|j| j.4 as u64).collect()));
    let none = jobs.iter().filter(|j| j.2.is_empty()).count();
    println!("calls no worker joined: {none} of {}", jobs.len());
}
