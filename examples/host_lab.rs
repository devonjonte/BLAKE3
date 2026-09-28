use blake3_servil::lanes::probe::*;
use blake3_servil::{Efficiency, Hash, Mode, PieceHandler, Queue};
use std::sync::{atomic::Ordering::Relaxed, mpsc};
enum B { P(Vec<u8>), D(Hash) }
struct P(mpsc::Sender<B>);
impl PieceHandler for P {
    type Buffer = Vec<u8>;
    fn piece_done(&mut self, b: Vec<u8>) { self.0.send(B::P(b)).unwrap(); }
    fn finished(&mut self, h: Hash) { self.0.send(B::D(h)).unwrap(); }
}
fn main() {
    blake3_servil::initialize_multithreaded();
    let input = vec![5u8; 32 << 20];
    let (tx, rx) = mpsc::channel();
    let mut free: Vec<Vec<u8>> = (0..4).map(|_| Vec::with_capacity(65536)).collect();
    let (mut copy_ns, mut wait_ns) = (0u64, 0u64);
    let t = std::time::Instant::now();
    for _ in 0..10 {
        let q = Queue::pieces(Mode::Hash, Efficiency::Time, P(tx.clone()));
        for piece in input.chunks(65536) {
            let w = std::time::Instant::now();
            let mut b = match free.pop() { Some(b) => b, None => loop { if let B::P(b) = rx.recv().unwrap() { break b } } };
            wait_ns += w.elapsed().as_nanos() as u64;
            let c = std::time::Instant::now();
            b.clear(); b.extend_from_slice(piece);
            copy_ns += c.elapsed().as_nanos() as u64;
            q.submit(b);
        }
        q.finish();
        loop { match rx.recv().unwrap() { B::P(b) => free.push(b), B::D(_) => break } }
    }
    let pieces = 10 * 512;
    println!("ns/B {:.3}", t.elapsed().as_nanos() as f64 / (10.0 * input.len() as f64));
    println!("producer per piece: wait {} ns, copy {} ns, submit {} ns", wait_ns / pieces, copy_ns / pieces, SUBMIT_NS.load(Relaxed) / SUBMITS.load(Relaxed));
    let runs = [RUNS[0].load(Relaxed), RUNS[1].load(Relaxed)];
    println!("tasks: sme2 thread {} (avg {} ns), workers {} (avg {} ns), push->pop avg {} ns, last done->delivered avg {} ns", runs[0], RUN_NS[0].load(Relaxed) / runs[0].max(1), runs[1], RUN_NS[1].load(Relaxed) / runs[1].max(1), POP_WAIT.load(Relaxed) / (runs[0] + runs[1]), DONE_TO_DELIVERED.load(Relaxed) / DELIVERS.load(Relaxed).max(1));
}
