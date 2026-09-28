//! Probe (probe/first-call): what the first call after a 1 ms sleep costs
//! beyond a second call right after it, for hash() and SHA-256 (sha2) at 64
//! B and 1 KiB: a cost of the first call's cold state (cache lines, pages,
//! predictors) or of the core's. 400 gaps each; the first and the second
//! call timed alone, summed. Wall time and the clock (clocks).
use sha2::Digest;
use std::hint::black_box;

fn pair(label: &str, f: &dyn Fn()) {
    let calls = 400u64;
    let (mut first, mut second) = (0u64, 0u64);
    let before = clocks::Counts::read();
    for _ in 0..calls {
        std::thread::sleep(std::time::Duration::from_millis(1));
        let t = clocks::now();
        f();
        first += clocks::since_ns(t);
        let t = clocks::now();
        f();
        second += clocks::since_ns(t);
    }
    let mhz = before.zip(clocks::Counts::read()).map(|(b, a)| a.since(b).mhz()).unwrap_or(0);
    println!("{label:<22} first {:>5} ns, second {:>5} ns, first - second {:>5} ns ({mhz} MHz over both)", first / calls, second / calls, (first - second) / calls);
}

fn main() {
    blake3_servil::initialize_multithreaded();
    let data = vec![7u8; 1024];
    for _ in 0..2 {
        pair("servil hash 64 B", &|| { black_box(blake3_servil::hash(black_box(&data[..64]))); });
        pair("sha256 64 B", &|| { black_box(sha2::Sha256::digest(black_box(&data[..64]))); });
        pair("servil hash 1 KiB", &|| { black_box(blake3_servil::hash(black_box(&data[..]))); });
        pair("sha256 1 KiB", &|| { black_box(sha2::Sha256::digest(black_box(&data[..]))); });
    }
}
