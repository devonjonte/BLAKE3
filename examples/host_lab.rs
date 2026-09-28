//! Probe (probe/submit-16k): the program thread's time in Queue::submit
//! for 16 KiB messages (a task each) and 4 KiB ones (gathered 64 to a
//! task), 64 or 256 in flight as the benchmark keeps (about 1 MiB), one
//! program alone and two at once (each its own queue, on its own thread).
use blake3_servil::{Efficiency, Hash, MessageHandler, Mode, Queue};
use std::hint::black_box;
use std::sync::mpsc;

struct Back(mpsc::Sender<Vec<u8>>);
impl MessageHandler for Back { type Buffer = Vec<u8>; fn hashed(&mut self, b: Vec<u8>, h: Hash) { black_box(h); self.0.send(b).unwrap(); } }

/// (ns per message, ns in submit per message, ns waiting for a buffer per message)
fn run(len: usize, n: usize) -> (u64, u64, u64) {
    let flight = ((1usize << 20) / len).clamp(2, 1024);
    let (tx, rx) = mpsc::channel();
    let mut free: Vec<Vec<u8>> = (0..flight).map(|_| vec![0u8; len]).collect();
    let input = vec![7u8; len];
    let (mut submit, mut wait) = (0u64, 0u64);
    let start = clocks::now();
    let q = Queue::messages(Mode::Hash, Efficiency::Time, Back(tx));
    for _ in 0..n {
        let t = clocks::now();
        let mut b = match free.pop() { Some(b) => b, None => rx.recv().unwrap() };
        wait += clocks::since_ns(t);
        b.copy_from_slice(&input);
        let t = clocks::now();
        q.submit(b);
        submit += clocks::since_ns(t);
    }
    for _ in free.len()..flight { rx.recv().unwrap(); }
    let n = n as u64;
    (clocks::since_ns(start) / n, submit / n, wait / n)
}

fn main() {
    blake3_servil::initialize_multithreaded();
    for len in [4096usize, 16384] {
        let n = (256 << 20) / len;
        for copies in [1usize, 2] {
            let mut results: Vec<Vec<(u64, u64, u64)>> = Vec::new();
            for _ in 0..3 {
                let r: Vec<(u64, u64, u64)> = std::thread::scope(|s| {
                    let hs: Vec<_> = (0..copies).map(|_| s.spawn(|| run(len, n))).collect();
                    hs.into_iter().map(|h| h.join().unwrap()).collect()
                });
                results.push(r);
            }
            let r = &results[1];
            for (c, (per, sub, wait)) in r.iter().enumerate() {
                println!("{len} B, {copies} program(s), copy {c}: {per} ns/msg, submit {sub} ns, waiting for a buffer {wait} ns");
            }
        }
    }
}
