//! The queue on a process with one CPU (a container's quota, a pinned
//! process): the pool then has no worker, and on a CPU without SME2 no
//! thread at all to take tasks, so every queue hashes on its delivery
//! thread. Each shape completes with the reference implementation's
//! digests (once, the queue's tasks waited forever: fork NOTES, "The
//! queue on one CPU"). The test pins its process to one CPU before the
//! pool starts, so it is a binary of its own, with one test (Linux, where
//! the pool counts the process's affinity).
#![cfg(target_os = "linux")]

use blake3_servil::{FixedHandler, Hash, MessageHandler, Mode, PieceHandler, Queue};
use std::sync::mpsc;

unsafe extern "C" {
    fn sched_setaffinity(pid: i32, cpusetsize: usize, mask: *const core::ffi::c_ulong) -> i32;
}

/// Input byte i is i % 251, as the official vectors define their inputs.
fn input(len: usize) -> Vec<u8> {
    (0..len).map(|i| (i % 251) as u8).collect()
}

fn reference(data: &[u8]) -> [u8; 32] {
    let mut hasher = reference_impl::Hasher::new();
    hasher.update(data);
    let mut out = [0u8; 32];
    hasher.finalize(&mut out);
    out
}

struct Messages(mpsc::Sender<(Vec<u8>, Hash)>);
impl MessageHandler for Messages {
    type Buffer = Vec<u8>;
    fn hashed(&mut self, buffer: Vec<u8>, hash: Hash) {
        self.0.send((buffer, hash)).unwrap();
    }
}

struct Pieces(mpsc::Sender<Option<Hash>>);
impl PieceHandler for Pieces {
    type Buffer = Vec<u8>;
    fn piece_done(&mut self, _: Vec<u8>) {
        self.0.send(None).unwrap();
    }
    fn finished(&mut self, hash: Hash) {
        self.0.send(Some(hash)).unwrap();
    }
}

struct Fixed(mpsc::Sender<Vec<[u8; 32]>>);
impl FixedHandler for Fixed {
    type Buffer = Vec<u8>;
    type Digests = Vec<[u8; 32]>;
    fn hashed(&mut self, _: Vec<u8>, digests: Vec<[u8; 32]>) {
        self.0.send(digests).unwrap();
    }
}

#[test]
fn every_queue_completes_on_one_cpu() {
    // A cpu_set_t is an array of unsigned longs, CPU n at bit n % 64 of
    // long n / 64 (a byte array would set CPU 56 on big-endian targets).
    let mask: [core::ffi::c_ulong; 1] = [1];
    // Sound: one long with CPU 0's bit, for this process.
    assert_eq!(unsafe { sched_setaffinity(0, core::mem::size_of_val(&mask), mask.as_ptr()) }, 0, "pin the process to CPU 0");
    assert_eq!(std::thread::available_parallelism().unwrap().get(), 1);
    let timeout = std::time::Duration::from_secs(60);

    // Messages short (gathered into tasks elsewhere) and long (subtree tasks).
    let (tx, rx) = mpsc::channel();
    let queue = Queue::messages(Mode::Hash, Messages(tx));
    let lens = [0, 64, 1000, 16 << 10, 64 << 10, (1 << 20) + 1];
    for &len in &lens {
        queue.submit(input(len));
    }
    for &len in &lens {
        let (buffer, hash) = rx.recv_timeout(timeout).expect("every message comes back");
        assert_eq!(buffer.len(), len);
        assert_eq!(*hash.as_bytes(), reference(&input(len)), "{len} B");
    }

    // One long message in 64 KiB pieces.
    let (tx, rx) = mpsc::channel();
    let queue = Queue::pieces(Mode::Hash, Pieces(tx));
    let message = input(1 << 20);
    for piece in message.chunks(64 << 10) {
        queue.submit(piece.to_vec());
    }
    queue.finish();
    let hash = (0..=16).map(|_| rx.recv_timeout(timeout).expect("every piece comes back")).last().unwrap();
    assert_eq!(*hash.expect("the digest comes last").as_bytes(), reference(&message));

    // Batches of 64-byte messages, small (gathered) and large (tasks of their own).
    let (tx, rx) = mpsc::channel();
    let queue = Queue::fixed(64, Mode::Hash, Fixed(tx));
    for count in [16, 4096] {
        let buffer = input(64 * count);
        queue.submit(buffer.clone(), vec![[0u8; 32]; count]);
        let digests = rx.recv_timeout(timeout).expect("the batch comes back");
        let expected: Vec<[u8; 32]> = buffer.chunks(64).map(reference).collect();
        assert!(digests == expected, "a batch of {count}");
    }
}
