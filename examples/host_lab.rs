//! Probe (probe/queue-submit): where a program's thread spends its time
//! per message through Queue::messages with 1024 buffers in flight (the
//! benchmark's continuous use case): the wait for a returned buffer, the
//! copy, and submit, each timed; against a loop of hash() over the same
//! copies. Wall time (clocks).
use blake3_servil::{Efficiency, Hash, MessageHandler, Mode, Queue};
use std::hint::black_box;
use std::sync::mpsc;

struct Back(mpsc::Sender<Vec<u8>>);
impl MessageHandler for Back {
    type Buffer = Vec<u8>;
    fn hashed(&mut self, buffer: Vec<u8>, hash: Hash) {
        black_box(hash);
        self.0.send(buffer).unwrap();
    }
}

fn run(len: usize, n: usize, flight: usize, timed: bool) -> (u64, u64, u64, u64) {
    let input = vec![7u8; len];
    let (tx, rx) = mpsc::channel();
    let mut free: Vec<Vec<u8>> = (0..flight).map(|_| vec![0u8; len]).collect();
    let (mut recv_ns, mut submit_ns, mut waits) = (0, 0, 0);
    let start = clocks::now();
    let queue = Queue::messages(Mode::Hash, Efficiency::Time, Back(tx));
    for _ in 0..n {
        let t = if timed { Some(clocks::now()) } else { None };
        let mut b = match free.pop() {
            Some(b) => b,
            None => match rx.try_recv() {
                Ok(b) => b,
                Err(_) => {
                    waits += 1;
                    rx.recv().unwrap()
                }
            },
        };
        if let Some(t) = t { recv_ns += clocks::since_ns(t); }
        b.copy_from_slice(&input);
        let t = if timed { Some(clocks::now()) } else { None };
        queue.submit(b);
        if let Some(t) = t { submit_ns += clocks::since_ns(t); }
    }
    let mut back = 0;
    while free.len() + back < flight {
        rx.recv().unwrap();
        back += 1;
    }
    (clocks::since_ns(start), recv_ns, submit_ns, waits)
}

fn main() {
    blake3_servil::initialize_multithreaded();
    for len in [64usize, 256, 1024] {
        let n = 200_000;
        let input = vec![7u8; len];
        let mut buffer = vec![0u8; len];
        let start = clocks::now();
        for _ in 0..n {
            buffer.copy_from_slice(&input);
            black_box(blake3_servil::hash(black_box(&buffer)));
        }
        let hash_ns = clocks::since_ns(start) / n as u64;
        for timed in [false, true] {
            let mut runs: Vec<_> = (0..7).map(|_| run(len, n, 1024, timed)).collect();
            runs.sort();
            let (total, recv, submit, waits) = runs[3];
            let n = n as u64;
            println!("{len} B, timed {timed}: {} ns/msg (hash() loop {hash_ns}); take a buffer {} ns, submit {} ns; waits {waits}", total / n, recv / n, submit / n);
        }
    }
}
