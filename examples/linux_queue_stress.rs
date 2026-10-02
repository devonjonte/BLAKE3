//! Correctness/liveness stress, not a performance measurement. Expected
//! digests come from the independent reference, anchored to published64 B
//! vectors before threads start. Inputs and scheduling are separate.
use blake3_servil::{Efficiency, FixedHandler, Hash, MessageHandler, Mode, Queue};
use std::sync::{Arc, mpsc};

const LENGTHS: &[usize] = &[0, 64, 128, 256, 512, 1024, 2048, 4096];
const KEY: &[u8; 32] = b"whats the Elvish word for friend";
const CONTEXT: &str = "BLAKE3 2019-12-27 16:29:52 test vectors context";
const IN_FLIGHT: usize = 16;
const SEEDS: usize = 16;
const BATCH: usize = 16;
type Expected = Vec<Vec<Vec<[u8; 32]>>>;

fn bytes(len: usize, seed: usize) -> Vec<u8> {
    (0..len).map(|i| ((i + seed * 17) % 251) as u8).collect()
}

fn expectations() -> Arc<Expected> {
    let mut all = Vec::new();
    for mode in 0..3 {
        let mut lengths = Vec::new();
        for &len in LENGTHS {
            let mut seeds = Vec::new();
            for seed in 0..SEEDS {
                let mut h = match mode {
                    0 => reference_impl::Hasher::new(),
                    1 => reference_impl::Hasher::new_keyed(KEY),
                    _ => reference_impl::Hasher::new_derive_key(CONTEXT),
                };
                h.update(&bytes(len, seed));
                let mut digest = [0; 32];
                h.finalize(&mut digest);
                seeds.push(digest);
            }
            lengths.push(seeds);
        }
        all.push(lengths);
    }
    // Published test_vectors/test_vectors.json, input_len64, i %251.
    for (mode, anchor) in [
        "4eed7141ea4a5cd4b788606bd23f46e212af9cacebacdc7d1f4c6dc7f2511b98",
        "ba8ced36f327700d213f120b1a207a3b8c04330528586f414d09f2f7d9ccb7e6",
        "a5c4a7053fa86b64746d4bb688d06ad1f02a18fce9afd3e818fefaa7126bf73e",
    ].into_iter().enumerate() {
        assert_eq!(all[mode][1][0].as_slice(), hex::decode(anchor).unwrap());
    }
    Arc::new(all)
}

struct Buffer { bytes: Vec<u8>, sequence: usize, length: usize, seed: usize }
impl AsRef<[u8]> for Buffer { fn as_ref(&self) -> &[u8] { &self.bytes } }
struct Messages { expected: Arc<Expected>, mode: usize, next: usize, sender: mpsc::SyncSender<Buffer> }
impl MessageHandler for Messages {
    type Buffer = Buffer;
    fn hashed(&mut self, buffer: Buffer, hash: Hash) {
        assert_eq!(buffer.sequence, self.next, "message delivery order");
        assert_eq!(*hash.as_bytes(), self.expected[self.mode][buffer.length][buffer.seed]);
        self.next += 1;
        self.sender.try_send(buffer).expect("room for every in-flight return");
    }
}
struct Batches { expected: Arc<Expected>, mode: usize, next: usize, sender: mpsc::SyncSender<(Buffer, Vec<[u8; 32]>)> }
impl FixedHandler for Batches {
    type Buffer = Buffer;
    type Digests = Vec<[u8; 32]>;
    fn hashed(&mut self, buffer: Buffer, digests: Self::Digests) {
        assert_eq!(buffer.sequence, self.next, "batch delivery order");
        assert_eq!(digests.len(), BATCH);
        for (m, digest) in digests.iter().enumerate() {
            assert_eq!(*digest, self.expected[self.mode][buffer.length][(buffer.seed + m) % SEEDS]);
        }
        self.next += 1;
        self.sender.try_send((buffer, digests)).expect("room for every in-flight return");
    }
}
fn mode(index: usize) -> Mode<'static> {
    match index { 0 => Mode::Hash, 1 => Mode::Keyed(KEY), _ => Mode::DeriveKey(CONTEXT) }
}
fn worker(thread: usize, blocks: usize, expected: Arc<Expected>) -> usize {
    let mut completed = 0;
    for turn in 0..3 {
        let m = (thread + turn) % 3;
        let (sender, receiver) = mpsc::sync_channel(IN_FLIGHT);
        let queue = Queue::messages(mode(m), Efficiency::Time, Messages { expected: expected.clone(), mode: m, next: 0, sender });
        let mut free: Vec<_> = (0..IN_FLIGHT).map(|_| Buffer { bytes: Vec::new(), sequence: 0, length: 0, seed: 0 }).collect();
        let mut sequence = 0;
        for (length, &len) in LENGTHS.iter().enumerate() {
            for block in 0..blocks {
                for slot in 0..IN_FLIGHT {
                    let mut buffer = free.pop().unwrap();
                    buffer.seed = (thread + block + slot) % SEEDS;
                    buffer.length = length;
                    buffer.sequence = sequence; sequence += 1;
                    buffer.bytes = bytes(len, buffer.seed);
                    queue.submit(buffer);
                }
                for _ in 0..IN_FLIGHT { free.push(receiver.recv().unwrap()); completed += 1; }
            }
        }
        drop(queue);
        for (length, &len) in LENGTHS.iter().enumerate() {
            let (sender, receiver) = mpsc::sync_channel(IN_FLIGHT);
            let queue = Queue::fixed(len, mode(m), Efficiency::Time, Batches { expected: expected.clone(), mode: m, next: 0, sender });
            let mut free: Vec<_> = (0..IN_FLIGHT).map(|_| (Buffer { bytes: Vec::new(), sequence: 0, length, seed: 0 }, vec![[0; 32]; BATCH])).collect();
            let slot_len = len.next_multiple_of(64).max(64);
            for block in 0..blocks {
                for slot in 0..IN_FLIGHT {
                    let (mut buffer, digests) = free.pop().unwrap();
                    buffer.sequence = block * IN_FLIGHT + slot;
                    buffer.seed = (thread + block + slot) % SEEDS;
                    buffer.bytes.clear();
                    for message in 0..BATCH {
                        let seed = (buffer.seed + message) % SEEDS;
                        buffer.bytes.extend_from_slice(&bytes(len, seed));
                        buffer.bytes.resize((message + 1) * slot_len, 0);
                    }
                    queue.submit(buffer, digests);
                }
                for _ in 0..IN_FLIGHT { free.push(receiver.recv().unwrap()); completed += BATCH; }
            }
        }
    }
    completed
}
fn main() {
    let a: Vec<_> = std::env::args().skip(1).collect();
    assert_eq!(a.len(), 2, "linux_queue_stress THREADS BLOCKS");
    let threads: usize = a[0].parse().unwrap();
    let blocks: usize = a[1].parse().unwrap();
    assert!((1..=32).contains(&threads) && (1..=128).contains(&blocks));
    let expected = expectations();
    let workers: Vec<_> = (0..threads).map(|thread| {
        let expected = expected.clone();
        std::thread::spawn(move || worker(thread, blocks, expected))
    }).collect();
    let completed: usize = workers.into_iter().map(|w| w.join().unwrap()).sum();
    assert_eq!(completed, threads * 3 * LENGTHS.len() * blocks * IN_FLIGHT * (1 + BATCH));
    println!("validated {completed} digests and queue delivery order; threads={threads}, blocks={blocks}, fixed input generator i+17*seed modulo251");
}
