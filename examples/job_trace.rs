//! probe/devon-job-trace: for one-shot multithreaded calls back to back (the
//! lent cells' pattern), how many threads took pieces of each call, when the
//! first worker began, and how long the call took.
//!
//!     cargo run --release --features job-trace --example job_trace -- message 1048576 4000
//!     cargo run --release --features job-trace --example job_trace -- batch 16384 2000
//!
//! `message N`: hash_multithreaded on N bytes; `batch N`: hash_many_multithreaded
//! on N messages of 64 B. Prints the distribution over calls (p10, p50, p90).
//! A fourth argument `after-stream` streams 64 messages of 16 KiB before each
//! call (the stream cells' pattern before a lent cell's).

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let kind = args.first().map_or("message", String::as_str).to_owned();
    let n: usize = args.get(1).map_or(1 << 20, |a| a.parse().expect("a size"));
    let calls: usize = args.get(2).map_or(2000, |a| a.parse().expect("a count"));
    let after_stream = args.get(3).is_some_and(|a| a == "after-stream");
    // `after-sleep`: 1 ms asleep before each call, so it meets parked workers.
    let after_sleep = args.get(3).is_some_and(|a| a == "after-sleep");
    let stream_first = args.get(3).is_some_and(|a| a == "stream-first");
    // The streams' messages: 64 of 16 KiB, or with BIG_STREAM=1 256 of
    // 64 KiB (16 MiB, about a bench sample of continuous 64 KiB messages).
    let big = std::env::var_os("BIG_STREAM").is_some();
    let messages: Vec<Vec<u8>> = (0..if big { 256u32 } else { 64 }).map(|i| i.to_le_bytes().repeat(if big { 16384 } else { 4096 })).collect();
    let mut places = vec![blake3_servil::Hash::from_bytes([0; 32]); messages.len()];
    let mut stream_once = || {
        if after_sleep {
            std::thread::sleep(std::time::Duration::from_millis(1));
        }
        if after_stream {
            blake3_servil::stream(blake3_servil::Mode::Hash, |_: &mut [blake3_servil::Hash]| {}, |s| {
                for (m, place) in messages.iter().zip(places.iter_mut()) {
                    s.submit(m, place);
                }
                s.finish();
            });
        }
    };
    blake3_servil::initialize_multithreaded();
    let copy = args.get(4).is_some_and(|a| a == "copy" || a == "cell");
    // `cell`: also each digest copied into a ring of 1024 slots afterwards,
    // as bench-hashes' use_digest does (the lent cell's whole sample).
    let cell = args.get(4).is_some_and(|a| a == "cell");
    let mut slots = vec![[0u8; 32]; 1024];
    let mut next = 0usize;
    let source = vec![0x5au8; if kind == "batch" { n * 64 } else { n }];
    let mut out = vec![[0u8; 32]; if kind == "batch" { n } else { 0 }];
    // The lent cell's pattern with `copy`: each call's input read into a
    // kept buffer first (allocated at the first call, after any first stream).
    let mut kept: Vec<u8> = Vec::new();
    let mut call = || {
        if kept.is_empty() {
            kept = vec![0u8; source.len()];
        }
        if copy {
            kept.copy_from_slice(std::hint::black_box(&source));
        } else if kept[0] == 0 {
            kept.copy_from_slice(&source);
        }
        let input = &kept;
        if kind == "batch" {
            blake3_servil::hash_many_multithreaded(input, 64, &mut out);
            if cell {
                for digest in &out {
                    slots[next % 1024] = *std::hint::black_box(digest);
                    next += 1;
                }
                std::hint::black_box(&slots);
            }
            std::hint::black_box(&out);
        } else {
            std::hint::black_box(blake3_servil::hash_multithreaded(&input));
        }
    };
    if stream_first {
        // One stream, once, then only calls (does a stream leave lasting
        // state?).
        let mut first_places = vec![blake3_servil::Hash::from_bytes([0; 32]); messages.len()];
        blake3_servil::stream(blake3_servil::Mode::Hash, |_: &mut [blake3_servil::Hash]| {}, |s| {
            for (m, place) in messages.iter().zip(first_places.iter_mut()) {
                s.submit(m, place);
            }
            s.finish();
        });
    }
    for _ in 0..200 {
        stream_once();
        call();
    }
    blake3_servil::job_trace::take();
    // `every10`: a stream of 64 x 16 KiB before each block of 10 calls, the
    // calls alone timed: the bench's pattern (a sample of about 10 calls,
    // other cells' streams between samples).
    let every10 = args.get(3).is_some_and(|a| a == "every10");
    let mut timed_ns = 0u128;
    if every10 {
        // DUO=1: the block's stream on two other threads at once, as the
        // bench's shared samples run (its duo-copy threads).
        let duo = std::env::var_os("DUO").is_some();
        let messages = &messages;
        let one_stream = move || {
            let mut places = vec![blake3_servil::Hash::from_bytes([0; 32]); messages.len()];
            blake3_servil::stream(blake3_servil::Mode::Hash, |_: &mut [blake3_servil::Hash]| {}, |s| {
                for (m, place) in messages.iter().zip(places.iter_mut()) {
                    s.submit(m, place);
                }
                s.finish();
            });
        };
        let mut stream_ten = || {
            if duo {
                std::thread::scope(|scope| {
                    scope.spawn(one_stream);
                    scope.spawn(one_stream);
                });
            } else {
                one_stream();
            }
        };
        let _ = &mut stream_ten;
        for _ in 0..calls / 10 {
            stream_ten();
            let began = std::time::Instant::now();
            for _ in 0..10 {
                call();
            }
            timed_ns += began.elapsed().as_nanos();
        }
    } else {
        let began = std::time::Instant::now();
        for _ in 0..calls {
            stream_once();
            call();
        }
        timed_ns = began.elapsed().as_nanos();
    }
    let per_call_ns = timed_ns / calls as u128;
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
    println!("{kind} {n}: {} calls traced, {per_call_ns} ns a loop iteration in all", jobs.len());
    println!("call ns:              {}", pct(jobs.iter().map(|j| u64::from(j.0)).collect()));
    println!("first worker ns:      {}", pct(jobs.iter().map(|j| if j.1 == u32::MAX { u64::from(j.0) } else { u64::from(j.1) }).collect()));
    println!("workers a call:       {}", pct(jobs.iter().map(|j| j.2.len() as u64).collect()));
    println!("pieces by workers:    {}", pct(jobs.iter().map(|j| j.3 as u64).collect()));
    println!("pieces by the caller: {}", pct(jobs.iter().map(|j| j.4 as u64).collect()));
    // Which thread took each call's first worker piece (probe thread numbers).
    let mut first: std::collections::BTreeMap<u32, usize> = Default::default();
    {
        let mut seen: std::collections::BTreeMap<u32, (u32, u32)> = Default::default();
        for &(job, kind, thread, ns) in &events {
            if kind == WORKER_PIECE {
                let e = seen.entry(job).or_insert((u32::MAX, 0));
                if ns < e.0 { *e = (ns, thread); }
            }
        }
        for (_, (_, thread)) in seen { *first.entry(thread).or_default() += 1; }
    }
    let mut top: Vec<_> = first.into_iter().collect();
    top.sort_by(|a, b| b.1.cmp(&a.1));
    println!("first worker, by thread (calls): {:?}", &top[..top.len().min(5)]);
    let none = jobs.iter().filter(|j| j.2.is_empty()).count();
    println!("calls no worker joined: {none} of {}", jobs.len());
}
