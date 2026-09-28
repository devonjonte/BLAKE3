//! Probe (probe/energy-new, probe/energy-old): energy and CPU time beside
//! wall time for the queue's short messages, for a long message in 64 KiB
//! pieces through Hasher::update and update_multithreaded (what lingering
//! costs), and for hash_multithreaded after 1 ms gaps, on the fork commit
//! it is built on. The process's energy from proc_pid_rusage V6
//! (ri_energy_nj; kernel's estimate), its CPU time from the clocks crate.
//! Each case three times; the middle by energy.
use blake3_servil::{Efficiency, Hash, MessageHandler, Mode, Queue};
use std::hint::black_box;
use std::sync::mpsc;

#[cfg(target_vendor = "apple")]
fn energy_nj() -> u64 {
    unsafe extern "C" {
        fn proc_pid_rusage(pid: i32, flavor: i32, buffer: *mut u64) -> i32;
        fn getpid() -> i32;
    }
    let mut words = [0u64; 128];
    assert_eq!(unsafe { proc_pid_rusage(getpid(), 6, words.as_mut_ptr()) }, 0);
    words[42]
}
#[cfg(not(target_vendor = "apple"))]
fn energy_nj() -> u64 { 0 }

struct Back(mpsc::Sender<Vec<u8>>);
impl MessageHandler for Back { type Buffer = Vec<u8>; fn hashed(&mut self, b: Vec<u8>, h: Hash) { black_box(h); self.0.send(b).unwrap(); } }

fn case(label: &str, units: u64, unit: &str, f: &dyn Fn()) {
    let mut runs: Vec<(u64, u64, u64)> = (0..3).map(|_| {
        std::thread::sleep(std::time::Duration::from_millis(20));
        let (e, c, t) = (energy_nj(), clocks::process_cpu_ns(), clocks::now());
        f();
        // The energy of what the work left running, too: 5 ms more.
        let wall = clocks::since_ns(t);
        std::thread::sleep(std::time::Duration::from_millis(5));
        (energy_nj() - e, clocks::process_cpu_ns() - c, wall)
    }).collect();
    runs.sort();
    let (e, c, w) = runs[1];
    println!("{label:<52} {:>7} pJ/{unit}, CPU {:>6} ps/{unit}, wall {:>6} ps/{unit}", e * 1000 / units, c * 1000 / units, w * 1000 / units);
}

fn queue(len: usize, n: usize) {
    let (tx, rx) = mpsc::channel();
    let mut free: Vec<Vec<u8>> = (0..1024.min((1 << 20) / len).max(2)).map(|_| vec![0u8; len]).collect();
    let count = free.len();
    let input = vec![7u8; len];
    let q = Queue::messages(Mode::Hash, Efficiency::Time, Back(tx));
    for _ in 0..n {
        let mut b = match free.pop() { Some(b) => b, None => rx.recv().unwrap() };
        b.copy_from_slice(&input);
        q.submit(b);
    }
    for _ in free.len()..count { rx.recv().unwrap(); }
}

fn main() {
    blake3_servil::initialize_multithreaded();
    let big = vec![3u8; 32 << 20];
    for _ in 0..2 {
        case("queue, 64 B messages x 500000", 500_000, "msg", &|| queue(64, 500_000));
        case("queue, 1 KiB messages x 200000", 200_000 * 1024, "B", &|| queue(1024, 200_000));
        case("Hasher::update, 32 MiB in 64 KiB pieces", 32 << 20, "B", &|| {
            let mut buf = vec![0u8; 65536];
            let mut h = blake3_servil::Hasher::new();
            for p in big.chunks(65536) { buf.copy_from_slice(p); h.update(black_box(&buf)); }
            black_box(h.finalize());
        });
        case("Hasher::update_multithreaded, 32 MiB in 64 KiB pieces", 32 << 20, "B", &|| {
            let mut buf = vec![0u8; 65536];
            let mut h = blake3_servil::Hasher::new();
            for p in big.chunks(65536) { buf.copy_from_slice(p); h.update_multithreaded(black_box(&buf)); }
            black_box(h.finalize());
        });
        case("hash, 8 MiB, x20 after 1 ms gaps", 20 * (8 << 20), "B", &|| {
            for _ in 0..20 { std::thread::sleep(std::time::Duration::from_millis(1)); black_box(blake3_servil::hash(&big[..8 << 20])); }
        });
        case("hash_multithreaded, 8 MiB, x20 after 1 ms gaps", 20 * (8 << 20), "B", &|| {
            for _ in 0..20 { std::thread::sleep(std::time::Duration::from_millis(1)); black_box(blake3_servil::hash_multithreaded(&big[..8 << 20])); }
        });
    }
}
