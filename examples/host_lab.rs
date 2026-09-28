//! Probe (probe/aftereffect): does work on other threads (the queue, an
//! SME2 burst, a NEON burst) leave the next single-threaded work slower?
//! SHA-256 of 1 KiB messages (sha2) in a loop on the main thread for 1 ms,
//! cycles per byte and clock, right after each kind of burst and after
//! 5 ms asleep. Median of 15 of each, interleaved.
use blake3_servil::{Efficiency, Hash, MessageHandler, Mode, Queue};
use sha2::Digest;
use std::hint::black_box;
use std::sync::mpsc;

struct Back(mpsc::Sender<Vec<u8>>);
impl MessageHandler for Back { type Buffer = Vec<u8>; fn hashed(&mut self, b: Vec<u8>, h: Hash) { black_box(h); self.0.send(b).unwrap(); } }

fn sha_loop(buf: &[u8]) -> clocks::Batch {
    let mut b = clocks::measure(1, 1_000_000, || { black_box(sha2::Sha256::digest(black_box(buf))); });
    b.remove(0)
}

fn on_thread(f: impl FnOnce() + Send + 'static) { std::thread::spawn(f).join().unwrap(); }

fn main() {
    blake3_servil::initialize_multithreaded();
    let buf = vec![5u8; 1024];
    let kinds = ["asleep 5 ms", "queue 2048 x 1 KiB", "SME2 burst (hash 1 MiB x 3, other thread)", "NEON burst (hash 8 KiB x 400, other thread)", "hash_multithreaded 8 MiB"];
    let mut results: Vec<Vec<(u64, u64, u64)>> = vec![Vec::new(); kinds.len()];
    for _ in 0..15 {
        for (k, _) in kinds.iter().enumerate() {
            std::thread::sleep(std::time::Duration::from_millis(5));
            match k {
                0 => {}
                1 => {
                    let (tx, rx) = mpsc::channel();
                    let q = Queue::messages(Mode::Hash, Efficiency::Time, Back(tx));
                    for _ in 0..2048 { q.submit(vec![1u8; 1024]); }
                    for _ in 0..2048 { rx.recv().unwrap(); }
                }
                2 => on_thread(|| { let d = vec![1u8; 1 << 20]; for _ in 0..3 { black_box(blake3_servil::hash(&d)); } }),
                3 => on_thread(|| { let d = vec![1u8; 8192]; for _ in 0..400 { black_box(blake3_servil::hash(&d)); } }),
                _ => { let d = vec![1u8; 8 << 20]; black_box(blake3_servil::hash_multithreaded(&d)); }
            }
            let b = sha_loop(&buf);
            let c = b.counts.map(|c| c.p.cycles + c.e.cycles).unwrap_or(0);
            let t = b.counts.map(|c| c.p.time_ns + c.e.time_ns).unwrap_or(0);
            results[k].push((b.wall_ns * 1000 / (b.calls * 1024), c * 1000 / (b.calls * 1024), if t > 0 { c * 1000 / t } else { 0 }));
        }
    }
    for (k, name) in kinds.iter().enumerate() {
        let mut r = results[k].clone();
        r.sort_by_key(|x| x.1);
        let m = r[r.len() / 2];
        println!("after {name:<44}: SHA-256 1 KiB {}.{:03} ns/B, {}.{:03} cycles/B, {} MHz (median of {})", m.0 / 1000, m.0 % 1000, m.1 / 1000, m.1 % 1000, m.2, r.len());
    }
}
