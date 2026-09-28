//! Probe (probe/queue-check): the queue's digests on this machine against
//! the one-shot calls (tests/api_plan.rs checks them against independent
//! sources; the Mac runner runs no integration tests): Queue::messages at
//! many lengths (members, subtree tasks, pieces), with 1024 in flight;
//! Queue::fixed batches; Queue::pieces; one queue shared by four threads;
//! Hasher::update_multithreaded streams. Prints "all equal" or panics.
use blake3_servil::{Efficiency, FixedHandler, Hash, MessageHandler, Mode, PieceHandler, Queue};
use std::sync::mpsc;

struct M(mpsc::Sender<(Vec<u8>, Hash)>);
impl MessageHandler for M { type Buffer = Vec<u8>; fn hashed(&mut self, b: Vec<u8>, h: Hash) { self.0.send((b, h)).unwrap(); } }
struct F(mpsc::Sender<(Vec<u8>, Vec<[u8; 32]>)>);
impl FixedHandler for F { type Buffer = Vec<u8>; type Digests = Vec<[u8; 32]>; fn hashed(&mut self, b: Vec<u8>, d: Vec<[u8; 32]>) { self.0.send((b, d)).unwrap(); } }
enum PE { Done(Vec<u8>), Fin(Hash) }
struct P(mpsc::Sender<PE>);
impl PieceHandler for P { type Buffer = Vec<u8>; fn piece_done(&mut self, b: Vec<u8>) { self.0.send(PE::Done(b)).unwrap(); } fn finished(&mut self, h: Hash) { self.0.send(PE::Fin(h)).unwrap(); } }

fn data(len: usize, seed: u8) -> Vec<u8> { (0..len).map(|i| (i as u8).wrapping_mul(31).wrapping_add(seed)).collect() }

fn main() {
    blake3_servil::initialize_multithreaded();
    let mut checked = 0usize;
    // Messages: many lengths, many in flight.
    for &len in &[0usize, 1, 63, 64, 65, 200, 1024, 1025, 4096, 8191, 16383, 16384, 16385, 65536, 100_000, 1 << 20] {
        let (tx, rx) = mpsc::channel();
        let q = Queue::messages(Mode::Hash, Efficiency::Time, M(tx));
        let n = (4 << 20) / len.max(64);
        let n = n.clamp(4, 3000);
        for i in 0..n { q.submit(data(len, i as u8)); }
        for i in 0..n {
            let (b, h) = rx.recv().unwrap();
            assert_eq!(b, data(len, i as u8), "messages {len} B: order");
            assert_eq!(h, blake3_servil::hash(&b), "messages {len} B, {i}");
            checked += 1;
        }
    }
    // Fixed batches.
    for &(mlen, count) in &[(64usize, 1usize), (64, 16), (64, 64), (64, 1000), (64, 20000), (100, 7), (1024, 9)] {
        let (tx, rx) = mpsc::channel();
        let q = Queue::fixed(mlen, Mode::Hash, Efficiency::Time, F(tx));
        let slot = mlen.next_multiple_of(64);
        let make = |seed: u8| { let mut b = vec![0u8; slot * count]; for k in 0..count { b[k * slot..k * slot + mlen].copy_from_slice(&data(mlen, seed.wrapping_add(k as u8))); } b };
        for s in 0..50u8 { q.submit(make(s), vec![[0u8; 32]; count]); }
        for s in 0..50u8 {
            let (b, d) = rx.recv().unwrap();
            assert_eq!(b, make(s), "fixed order");
            for k in 0..count { assert_eq!(d[k], *blake3_servil::hash(&b[k * slot..k * slot + mlen]).as_bytes(), "fixed {count} x {mlen}"); checked += 1; }
        }
    }
    // Pieces.
    for &(total, piece) in &[(3usize << 20, 65536usize), ((5 << 20) + 17, 100_000), (70_000, 1000)] {
        let (tx, rx) = mpsc::channel();
        let q = Queue::pieces(Mode::Hash, Efficiency::Time, P(tx));
        let d = data(total, 9);
        for _ in 0..3 { for p in d.chunks(piece) { q.submit(p.to_vec()); } q.finish(); }
        let mut fins = 0;
        while fins < 3 { if let PE::Fin(h) = rx.recv().unwrap() { assert_eq!(h, blake3_servil::hash(&d), "pieces {total}"); fins += 1; checked += 1; } }
    }
    // One queue, four submitting threads.
    let (tx, rx) = mpsc::channel();
    let q = Queue::messages(Mode::Hash, Efficiency::Time, M(tx));
    std::thread::scope(|s| { for t in 0..4u8 { let q = &q; s.spawn(move || { for i in 0..5000usize { let mut b = data([64, 1000, 20000][i % 3], t); b[0] = t; b[1..9].copy_from_slice(&(i as u64).to_le_bytes()); q.submit(b); } }); } });
    let mut next = [0u64; 4];
    for _ in 0..20000 { let (b, h) = rx.recv().unwrap(); let t = b[0] as usize; let i = u64::from_le_bytes(b[1..9].try_into().unwrap()); assert_eq!(i, next[t]); next[t] += 1; assert_eq!(h, blake3_servil::hash(&b)); checked += 1; }
    // Streams through update_multithreaded (lingering).
    for &(total, piece) in &[(32usize << 20, 65536usize), ((3 << 20) + 5, 65536), (2 << 20, 1000)] {
        let d = data(total, 5);
        for _ in 0..3 { let mut h = blake3_servil::Hasher::new(); for p in d.chunks(piece) { h.update_multithreaded(p); } assert_eq!(h.finalize(), blake3_servil::hash(&d), "stream {total}"); checked += 1; }
    }
    println!("queue-check: all equal ({checked} digests)");
}
