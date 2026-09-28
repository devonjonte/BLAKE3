//! Probe (probe/busy-gap): calls after a busy gap run at two speeds; is it
//! the counts' system call before each call, or the vector unit gone cold
//! through integer-only work?
use std::hint::black_box;

fn call_ns(input: &[u8]) -> u64 {
    let t = clocks::now();
    black_box(blake3_servil::hash(black_box(input)));
    clocks::since_ns(t)
}

fn neon_work(ns: u64) {
    // Busy work that keeps the vector unit in use: a float multiply-add chain on 4 lanes.
    let started = clocks::now();
    let mut v = [1.0f32; 16];
    while clocks::since_ns(started) < ns {
        for _ in 0..64 {
            for x in v.iter_mut() {
                *x = *x * 1.000001 + 0.5;
            }
        }
        v = black_box(v);
    }
}

fn report(name: &str, samples: &mut Vec<u128>) {
    samples.sort_unstable();
    let s = clocks::speeds::speeds(samples);
    let total = samples.len();
    let text: Vec<String> = s.iter().map(|sp| format!("{} ns ({}%)", sp.median >> 64, sp.count * 100 / total)).collect();
    println!("{name}: {}", text.join(" | "));
}

fn main() {
    blake3_servil::initialize();
    for len in [512usize, 4096] {
        let input = vec![7u8; len];
        for round in 0..2 {
            let mut plain = Vec::new();
            let mut with_counts = Vec::new();
            let mut neon_gap = Vec::new();
            let mut sleep_gap = Vec::new();
            for _ in 0..200 {
                clocks::busy_work(1_000_000);
                plain.push(clocks::speeds::per_unit(call_ns(&input), 1));
                clocks::busy_work(1_000_000);
                let before = clocks::Counts::read();
                let ns = call_ns(&input);
                black_box((before, clocks::Counts::read()));
                with_counts.push(clocks::speeds::per_unit(ns, 1));
                neon_work(1_000_000);
                neon_gap.push(clocks::speeds::per_unit(call_ns(&input), 1));
                std::thread::sleep(std::time::Duration::from_millis(1));
                sleep_gap.push(clocks::speeds::per_unit(call_ns(&input), 1));
            }
            println!("-- {len} B, round {round}");
            report("integer gap, no counts read", &mut plain);
            report("integer gap, counts read around the call", &mut with_counts);
            report("vector gap, no counts read", &mut neon_gap);
            report("sleep gap", &mut sleep_gap);
        }
    }
}
