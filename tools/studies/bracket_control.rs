//! How much the reads around a timed interval add to it, on this machine.
//!
//! bench-hashes' samplers bracket a call as: counts read, wall read, the
//! call, wall read, counts read. The counted interval therefore holds two
//! wall reads and the tails of two counts reads beside the call. This
//! program brackets a known amount of work that way, 20,000 times each,
//! and reports the distribution of every clock's reading: wall ns, the
//! thread's P-core time, cycles, and instructions from the counts, and
//! the E-core time (expected 0 on a P-core). The work is 0, about 1 us,
//! and about 10 us of register arithmetic, touching no memory, so a
//! reading above the work's own cost is the reads' share. A second
//! bracket order (wall read outside the counts read) measures the same
//! work with the roles swapped. The output is integers: min, median,
//! mean, 95th percentile, max, and the per-sample cost of each read
//! alone.
use clocks::Counts;

fn spin(rounds: u64) -> u64 {
    let mut x = 1u64;
    for _ in 0..rounds {
        x = x.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
    }
    std::hint::black_box(x)
}

fn stats(name: &str, mut v: Vec<u64>) {
    v.sort_unstable();
    let n = v.len() as u64;
    let sum: u64 = v.iter().sum();
    println!("  {name:<14} min {:>8} p50 {:>8} mean {:>8} p95 {:>8} max {:>10}", v[0], v[v.len() / 2], (sum + n / 2) / n, v[v.len() * 95 / 100], v[v.len() - 1]);
}

fn bracket(rounds: u64, counts_outside: bool) -> (Vec<u64>, Vec<u64>, Vec<u64>, Vec<u64>, Vec<u64>) {
    const SAMPLES: usize = 20_000;
    let (mut wall, mut p_time, mut cycles, mut instructions, mut e_time) = (Vec::with_capacity(SAMPLES), Vec::with_capacity(SAMPLES), Vec::with_capacity(SAMPLES), Vec::with_capacity(SAMPLES), Vec::with_capacity(SAMPLES));
    for _ in 0..SAMPLES {
        let (w, c) = if counts_outside {
            let before = Counts::read().expect("this Mac counts");
            let t = clocks::now();
            spin(rounds);
            let w = clocks::since_ns(t);
            (w, Counts::read().unwrap().since(before))
        } else {
            let t = clocks::now();
            let before = Counts::read().expect("this Mac counts");
            spin(rounds);
            let c = Counts::read().unwrap().since(before);
            (clocks::since_ns(t), c)
        };
        wall.push(w);
        p_time.push(c.p.time_ns);
        cycles.push(c.p.cycles);
        instructions.push(c.p.instructions);
        e_time.push(c.e.time_ns);
    }
    (wall, p_time, cycles, instructions, e_time)
}

fn main() {
    clocks::set_qos(clocks::USER_INTERACTIVE);
    println!("wall clock: {}", clocks::WALL_CLOCK);
    // Each read alone, averaged over a batch long enough that a tick is a small share.
    let reads = 200_000u64;
    let t = clocks::now();
    for _ in 0..reads {
        std::hint::black_box(clocks::now());
    }
    println!("one wall read: {} ns (mean of {reads})", (clocks::since_ns(t) + reads / 2) / reads);
    let before = Counts::read().unwrap();
    let t = clocks::now();
    for _ in 0..reads {
        std::hint::black_box(Counts::read());
    }
    let w = clocks::since_ns(t);
    let c = Counts::read().unwrap().since(before);
    println!(
        "one counts read: {} ns wall, {} ns P-time, {} P-cycles, {} P-instructions (means of {reads})",
        (w + reads / 2) / reads,
        (c.p.time_ns + reads / 2) / reads,
        (c.p.cycles + reads / 2) / reads,
        (c.p.instructions + reads / 2) / reads
    );
    // Calibrate the spin: rounds for about 1 us and 10 us of wall.
    let t = clocks::now();
    spin(1_000_000);
    let ns_per_round_e6 = clocks::since_ns(t);
    let per_us = 1_000_000_000 / ns_per_round_e6.max(1);
    println!("spin: {} ns per 1e6 rounds; {per_us} rounds per us", ns_per_round_e6);
    for (label, rounds) in [("no work", 0u64), ("~1 us", per_us), ("~10 us", 10 * per_us)] {
        for counts_outside in [true, false] {
            let order = if counts_outside { "counts outside wall (the samplers' order)" } else { "wall outside counts" };
            println!("{label}, {order}, 20000 samples:");
            let (wall, p_time, cycles, instructions, e_time) = bracket(rounds, counts_outside);
            stats("wall ns", wall);
            stats("P time ns", p_time);
            stats("P cycles", cycles);
            stats("P instructions", instructions);
            stats("E time ns", e_time);
        }
    }
}
