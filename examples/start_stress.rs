//! A fresh process's first calls, while the pool's threads are still
//! starting (initialize_multithreaded returns before they do): a queue of
//! messages of every shape it gathers, a multithreaded hash past the split,
//! and a Verifier's large piece, each checked against hash(). Exits 0 when
//! every digest matches; a mismatch panics. Run many times (a fresh process
//! each) to meet the threads at every stage of their start.
use blake3_servil::{Hash, MessageHandler, Mode, Queue};
use std::sync::mpsc;

/// A message and its place in the submission order.
struct Message(usize, Vec<u8>);
impl AsRef<[u8]> for Message {
    fn as_ref(&self) -> &[u8] {
        &self.1
    }
}

struct Back(mpsc::Sender<(usize, Hash)>);
impl MessageHandler for Back {
    type Buffer = Message;
    fn hashed(&mut self, buffer: Message, hash: Hash) {
        self.0.send((buffer.0, hash)).unwrap();
    }
}

fn main() {
    blake3_servil::initialize_multithreaded();
    let seed: usize = std::env::args().nth(1).map_or(0, |s| s.parse().unwrap());
    let data: Vec<u8> = (0..(2 << 20) + 4096).map(|i| ((i * 31 + seed) % 251) as u8).collect();
    // The queue first: messages of 64 B to 1 KiB (gathered members), and longer.
    let (tx, rx) = mpsc::channel();
    let queue = Queue::messages(Mode::Hash, Back(tx));
    let lens = [64usize, 64, 128, 256, 512, 1024, 64, 1000, 4096, 70_000, 64, 64];
    let count = 200 + seed % 300;
    for i in 0..count {
        let len = lens[(i + seed) % lens.len()];
        queue.submit(Message(i, data[i..i + len].to_vec()));
    }
    let mut got = vec![None; count];
    for _ in 0..count {
        let (i, h) = rx.recv().unwrap();
        got[i] = Some(h);
    }
    for i in 0..count {
        let len = lens[(i + seed) % lens.len()];
        assert_eq!(got[i], Some(blake3_servil::hash(&data[i..i + len])), "queue message {i}, {len} bytes, seed {seed}");
    }
    // A multithreaded hash past the split, and a Verifier's large piece.
    let big = &data[seed % 4096..][..(1 << 20) + 777];
    assert_eq!(blake3_servil::hash_multithreaded(big), blake3_servil::hash(big), "hash_multithreaded, seed {seed}");
    let (hash, encoding) = (blake3_servil::hash(big), blake3_servil::test_encoding(Mode::Hash, big));
    let mut v = blake3_servil::Verifier::new(Mode::Hash, &hash, big.len() as u64);
    let mut out = Vec::new();
    assert!(v.update_multithreaded(&encoding, |b| out.extend_from_slice(b)), "verifier, seed {seed}");
    assert_eq!(out, big, "verified bytes, seed {seed}");
}
