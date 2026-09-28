//! Probe (probe/task-times): where a queued message's round trip goes, for
//! 64 KiB and 16 KiB messages with 1 MiB in flight (the benchmark's):
//! time waiting in the task list and hashing, by thread kind (SME2 thread
//! or NEON worker), and submit -> delivery per message.
use blake3_servil::{Efficiency, Hash, MessageHandler, Mode, Queue};
use std::sync::mpsc;
struct M(mpsc::Sender<Vec<u8>>);
impl MessageHandler for M { type Buffer = Vec<u8>; fn hashed(&mut self, b: Vec<u8>, h: Hash) { std::hint::black_box(h); self.0.send(b).unwrap(); } }

fn main() {
    blake3_servil::initialize_multithreaded();
    for len in [65536usize, 16384] {
        let flight = (1 << 20) / len;
        let n = (512usize << 20) / len;
        let input = vec![3u8; len];
        let (tx, rx) = mpsc::channel();
        let q = Queue::messages(Mode::Hash, Efficiency::Time, M(tx));
        let mut free: Vec<Vec<u8>> = (0..flight).map(|_| vec![0u8; len]).collect();
        let _ = blake3_servil::probe_take(); let _ = blake3_servil::probe_trip();
        let t = clocks::now();
        for _ in 0..n { let mut b = match free.pop() { Some(b) => b, None => rx.recv().unwrap() }; b.copy_from_slice(&input); q.submit(b); }
        for _ in free.len()..flight { rx.recv().unwrap(); }
        let wall = clocks::since_ns(t);
        let p = blake3_servil::probe_take(); let (trip, trips) = blake3_servil::probe_trip();
        println!("{len} B, {flight} in flight: {} ns/msg, {} ps/B", wall / n as u64, wall * 1000 / (n * len) as u64);
        for (k, name) in [(0usize, "NEON workers"), (1, "SME2 thread")] {
            let c = p[k][2].max(1);
            println!("  {name}: {} tasks, waiting {} ns on average (most {}), hashing {} ns", p[k][2], p[k][0] / c, p[k][3], p[k][1] / c);
        }
        println!("  submit -> delivered: {} ns on average over {trips}", trip / trips.max(1));
    }
}
