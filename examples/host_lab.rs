//! Probe (probe/energy-repeat): how repeatable the process's energy counter
//! is (clocks::process_energy_nj, macOS RUSAGE_INFO_V6 ri_energy_nj), for
//! stage 3's energy cells: ten repeats each of a 100 ms integer spin on a
//! P-core (user-interactive QoS), hash() over 64 MiB, and
//! hash_multithreaded() over 64 MiB, each after 50 ms asleep; energy per
//! repeat (and per byte), and the spread (max/min) of each set.
use std::hint::black_box;

fn spin_ms(ms: u64) {
    let t = clocks::now();
    let mut x = 1u64;
    while clocks::since_ns(t) < ms * 1_000_000 {
        for i in 0..1000 { x = black_box(x.wrapping_mul(6364136223846793005).wrapping_add(i)); }
    }
    black_box(x);
}

fn repeat(label: &str, bytes: u64, f: &dyn Fn()) {
    let mut e = Vec::new();
    for _ in 0..10 {
        std::thread::sleep(std::time::Duration::from_millis(50));
        let (e0, t) = (clocks::process_energy_nj().unwrap_or(0), clocks::now());
        f();
        let wall = clocks::since_ns(t);
        e.push((clocks::process_energy_nj().unwrap_or(0) - e0, wall));
    }
    let mut en: Vec<u64> = e.iter().map(|x| x.0).collect();
    en.sort();
    let per = |nj: u64| if bytes > 0 { format!("{} pJ/B", nj * 1000 / bytes) } else { format!("{} mW", nj * 1000 / 100_000_000) };
    println!("{label:<34} energy min {} median {} max {} (spread {}.{:02}x); wall {:?} ms", per(en[0]), per(en[5]), per(en[9]), en[9] / en[0].max(1), (en[9] * 100 / en[0].max(1)) % 100, e.iter().map(|x| x.1 / 1_000_000).collect::<Vec<_>>());
}

/// The energy of `f`, read at once and again after 1, 10, and 100 ms
/// asleep: whether the counter's energy arrives late.
fn lag(label: &str, bytes: u64, f: &dyn Fn()) {
    for delay in [1u64, 10, 100] {
        let mut rows = Vec::new();
        for _ in 0..8 {
            std::thread::sleep(std::time::Duration::from_millis(50));
            let e0 = clocks::process_energy_nj().unwrap_or(0);
            f();
            let now = clocks::process_energy_nj().unwrap_or(0) - e0;
            std::thread::sleep(std::time::Duration::from_millis(delay));
            let later = clocks::process_energy_nj().unwrap_or(0) - e0;
            rows.push((now * 1000 / bytes, later * 1000 / bytes));
        }
        rows.sort();
        println!("{label:<24} read at once / after {delay:>3} ms asleep, pJ/B: {:?}", rows);
    }
}

fn main() {
    blake3_servil::initialize_multithreaded();
    clocks::set_qos(clocks::USER_INTERACTIVE);
    let big = vec![5u8; 64 << 20];
    lag("hash 64 MiB", 64 << 20, &|| { black_box(blake3_servil::hash(&big)); });
    for _ in 0..0 {
        repeat("spin 100 ms (P)", 0, &|| spin_ms(100));
        repeat("hash 64 MiB", 64 << 20, &|| { black_box(blake3_servil::hash(&big)); });
        repeat("hash_multithreaded 64 MiB", 64 << 20, &|| { black_box(blake3_servil::hash_multithreaded(&big)); });
    }
}
