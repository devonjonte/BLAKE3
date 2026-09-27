//! Probe (probe/queue-timeline): where a stream of four 64 KiB pieces
//! through Queue::pieces spends its time, under the engine's two help
//! rules (the front's tasks only; any task). The program cycles four
//! buffers and waits on its channel, as bench-hashes' streamed use case
//! does. Per piece position in the stream: medians of publish -> claim,
//! claim -> done, done -> delivery (wall ns), and who claimed it. Wall
//! time only: the workers' cycles per core kind are not readable from here.
use blake3_servil::lanes::probe;
use blake3_servil::{Efficiency, Hash, Mode, PieceHandler, Queue};
use std::sync::atomic::Ordering;
use std::sync::mpsc;

enum Back {
    Piece(Vec<u8>),
    Done(Hash),
}
struct Handler(mpsc::Sender<Back>);
impl PieceHandler for Handler {
    type Buffer = Vec<u8>;
    fn piece_done(&mut self, buffer: Vec<u8>) {
        self.0.send(Back::Piece(buffer)).unwrap();
    }
    fn finished(&mut self, hash: Hash) {
        self.0.send(Back::Done(hash)).unwrap();
    }
}

fn median(mut v: Vec<u64>) -> u64 {
    v.sort_unstable();
    v[v.len() / 2]
}

fn main() {
    blake3_servil::initialize_multithreaded();
    const PIECE: usize = 64 * 1024;
    for total in [256 * 1024, 4 << 20] {
        let input = vec![7u8; total];
        let pieces = total / PIECE;
        for help_any in [false, true, false, true] {
            probe::HELP_ANY.store(help_any, Ordering::Relaxed);
            let (tx, rx) = mpsc::channel();
            let queue = Queue::pieces(Mode::Hash, Efficiency::Time, Handler(tx));
            let mut free: Vec<Vec<u8>> = (0..4).map(|_| Vec::with_capacity(PIECE)).collect();
            let streams = (probe::N / pieces).min(4000) - 1;
            let mut stream_ns = Vec::new();
            for _ in 0..streams {
                let start = clocks::now();
                for piece in input.chunks(PIECE) {
                    let mut buffer = match free.pop() {
                        Some(buffer) => buffer,
                        None => loop {
                            if let Back::Piece(buffer) = rx.recv().unwrap() {
                                break buffer;
                            }
                        },
                    };
                    buffer.clear();
                    buffer.extend_from_slice(piece);
                    queue.submit(buffer);
                }
                queue.finish();
                loop {
                    match rx.recv().unwrap() {
                        Back::Piece(buffer) => free.push(buffer),
                        Back::Done(hash) => {
                            std::hint::black_box(hash);
                            break;
                        }
                    }
                }
                stream_ns.push(clocks::since_ns(start));
            }
            // Task index = stream * pieces + position (one task per aligned 64 KiB piece).
            let skip = 50;
            println!("{} KiB streams, help {}: {} streams, median {} ns ({} ns/KiB)", total / 1024, if help_any { "any" } else { "front" }, streams, median(stream_ns.clone()), median(stream_ns) * 1024 / total as u64);
            for position in (0..pieces.min(4)).chain(if pieces > 8 { vec![pieces / 2, pieces / 2 + 1] } else { vec![] }) {
                let tasks: Vec<usize> = (skip..streams).map(|s| s * pieces + position).collect();
                let wait: Vec<u64> = tasks.iter().map(|&i| probe::get(&probe::CLAIMED, i) - probe::get(&probe::PUBLISHED, i)).collect();
                let hash: Vec<u64> = tasks.iter().map(|&i| probe::get(&probe::DONE, i) - probe::get(&probe::CLAIMED, i)).collect();
                let deliver: Vec<u64> = tasks.iter().map(|&i| probe::get(&probe::DELIVERED, i).saturating_sub(probe::get(&probe::DONE, i))).collect();
                let by_engine = tasks.iter().filter(|&&i| probe::get(&probe::CLAIMER, i) == 0).count();
                let engine_hash: Vec<u64> = tasks.iter().filter(|&&i| probe::get(&probe::CLAIMER, i) == 0).map(|&i| probe::get(&probe::DONE, i) - probe::get(&probe::CLAIMED, i)).collect();
                let worker_hash: Vec<u64> = tasks.iter().filter(|&&i| probe::get(&probe::CLAIMER, i) != 0).map(|&i| probe::get(&probe::DONE, i) - probe::get(&probe::CLAIMED, i)).collect();
                println!(
                    "  piece {position}: publish->claim {} ns, claim->done {} ns (engine {} ns, workers {} ns), done->delivered {} ns; the engine took {}%",
                    median(wait),
                    median(hash),
                    if engine_hash.is_empty() { 0 } else { median(engine_hash) },
                    if worker_hash.is_empty() { 0 } else { median(worker_hash) },
                    median(deliver),
                    by_engine * 100 / tasks.len()
                );
            }
        }
    }
}
