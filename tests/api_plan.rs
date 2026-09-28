//! Tests of the planned API (docs/api-design.md), written before it is
//! built: they state its contract, and the implementation's job is to make
//! them pass. Expected answers come from independent sources only: the
//! official BLAKE3 test vectors (test_vectors/test_vectors.json: input byte
//! i is i % 251, every mode) and, for inputs past the vectors' largest, the
//! reference implementation (reference_impl/). Nothing here computes an
//! expected answer with this crate.

use blake3_servil::{Efficiency, FixedHandler, Hash, MessageHandler, Mode, PieceHandler, Queue, Threads};
use std::sync::mpsc;

const KEY: &[u8; 32] = b"whats the Elvish word for friend";
const CONTEXT: &str = "BLAKE3 2019-12-27 16:29:52 test vectors context";

/// Input byte i is i % 251, as the official vectors define their inputs.
fn input(len: usize) -> Vec<u8> {
    (0..len).map(|i| (i % 251) as u8).collect()
}

/// (input length, [hash, keyed hash, derived key]) for every official vector.
fn vectors() -> Vec<(usize, [[u8; 32]; 3])> {
    let text = std::fs::read_to_string(concat!(env!("CARGO_MANIFEST_DIR"), "/test_vectors/test_vectors.json")).expect("the official test vectors");
    let json: serde_json::Value = serde_json::from_str(&text).expect("the vectors are JSON");
    assert_eq!(json["key"], std::str::from_utf8(KEY).unwrap());
    assert_eq!(json["context_string"], CONTEXT);
    let first32 = |hex_text: &serde_json::Value| -> [u8; 32] { hex::decode(&hex_text.as_str().unwrap()[..64]).unwrap().try_into().unwrap() };
    json["cases"]
        .as_array()
        .unwrap()
        .iter()
        .map(|case| (case["input_len"].as_u64().unwrap() as usize, [first32(&case["hash"]), first32(&case["keyed_hash"]), first32(&case["derive_key"])]))
        .collect()
}

/// The reference implementation's digest of `data` in mode `m` (0 hash, 1 keyed, 2 derive-key).
fn reference(m: usize, data: &[u8]) -> [u8; 32] {
    let mut hasher = match m {
        0 => reference_impl::Hasher::new(),
        1 => reference_impl::Hasher::new_keyed(KEY),
        _ => reference_impl::Hasher::new_derive_key(CONTEXT),
    };
    hasher.update(data);
    let mut out = [0u8; 32];
    hasher.finalize(&mut out);
    out
}

fn modes() -> [Mode<'static>; 3] {
    [Mode::Hash, Mode::Keyed(KEY), Mode::DeriveKey(CONTEXT)]
}

fn thread_choices() -> [Threads; 4] {
    [Threads::One, Threads::All, Threads::Budget(1), Threads::Budget(2)]
}

/// Lengths past the official vectors, around the multithreaded split (768 KiB) and a subtree edge.
const LARGE: [usize; 5] = [(768 << 10) - 1, 768 << 10, 1 << 20, (1 << 20) + 1, (3 << 20) + 12345];

// ---------- One-shot, one message ----------

#[test]
fn one_message_every_form_matches_the_vectors() {
    blake3_servil::initialize();
    blake3_servil::initialize_multithreaded();
    for (len, expected) in vectors() {
        let data = input(len);
        assert_eq!(blake3_servil::hash(&data), Hash::from(expected[0]), "hash, {len} bytes");
        assert_eq!(blake3_servil::hash_multithreaded(&data), Hash::from(expected[0]), "hash_multithreaded, {len} bytes");
        assert_eq!(blake3_servil::keyed_hash(KEY, &data), Hash::from(expected[1]), "keyed_hash, {len} bytes");
        assert_eq!(blake3_servil::derive_key(CONTEXT, &data), expected[2], "derive_key, {len} bytes");
        for (m, mode) in modes().into_iter().enumerate() {
            for threads in thread_choices() {
                assert_eq!(blake3_servil::hash_with(mode, threads, &data), Hash::from(expected[m]), "hash_with mode {m} {threads:?}, {len} bytes");
            }
        }
    }
}

/// A message in pieces through `Hasher::update_multithreaded` (and mixed
/// with `update`), in every mode: streams of 64 KiB pieces long enough to
/// keep the workers ready between updates (past the first 128 KiB), pieces
/// that leave a chunk part-filled, and pieces past the multithreaded split,
/// against the reference implementation.
#[test]
fn a_message_in_pieces_matches_the_reference() {
    blake3_servil::initialize_multithreaded();
    let hashers = |m: usize| match m {
        0 => blake3_servil::Hasher::new(),
        1 => blake3_servil::Hasher::new_keyed(KEY),
        _ => blake3_servil::Hasher::new_derive_key(CONTEXT),
    };
    let cases: [(usize, usize); 8] = [
        (64 << 10, 64 << 10),
        (2 << 20, 64 << 10),
        ((2 << 20) + 777, 64 << 10),
        (1 << 20, 1000),
        ((1 << 20) + 5, (64 << 10) + 1),
        (3 << 20, 100_000),
        (4 << 20, 1 << 20),
        (5 << 20, 192 << 10),
    ];
    for (len, piece) in cases {
        let data = input(len);
        for m in 0..3 {
            let expected = Hash::from(reference(m, &data));
            let mut hasher = hashers(m);
            for part in data.chunks(piece) {
                hasher.update_multithreaded(part);
            }
            assert_eq!(hasher.finalize(), expected, "update_multithreaded, {len} B in {piece} B pieces, mode {m}");
            // Alternating with update, a piece at a time.
            let mut hasher = hashers(m);
            for (k, part) in data.chunks(piece).enumerate() {
                if k % 3 == 1 { hasher.update(part); } else { hasher.update_multithreaded(part); }
            }
            assert_eq!(hasher.finalize(), expected, "update and update_multithreaded, {len} B in {piece} B pieces, mode {m}");
        }
    }
}

#[test]
fn one_message_large_inputs_match_the_reference() {
    for len in LARGE {
        let data = input(len);
        assert_eq!(blake3_servil::hash_multithreaded(&data), Hash::from(reference(0, &data)), "hash_multithreaded, {len} bytes");
        for (m, mode) in modes().into_iter().enumerate() {
            for threads in thread_choices() {
                assert_eq!(blake3_servil::hash_with(mode, threads, &data), Hash::from(reference(m, &data)), "hash_with mode {m} {threads:?}, {len} bytes");
            }
        }
    }
}

#[test]
#[should_panic]
fn a_budget_of_no_threads_is_refused() {
    blake3_servil::hash_with(Mode::Hash, Threads::Budget(0), b"abc");
}

// ---------- One-shot, batches ----------

/// `count` messages of `len` bytes each, message i the official input
/// pattern starting at i (so messages differ), laid out by the padded batch
/// contract: slot i at i x stride, stride len rounded up to 64 (64 for 0),
/// zeros between a message's end and the next slot.
fn padded_batch(count: usize, len: usize) -> (Vec<u8>, Vec<Vec<u8>>) {
    let stride = if len == 0 { 64 } else { len.next_multiple_of(64) };
    let mut buffer = vec![0u8; stride * count];
    let messages: Vec<Vec<u8>> = (0..count).map(|i| (0..len).map(|j| ((i + j) % 251) as u8).collect()).collect();
    for (i, message) in messages.iter().enumerate() {
        buffer[i * stride..i * stride + len].copy_from_slice(message);
    }
    (buffer, messages)
}

#[test]
fn batches_every_form_match_the_reference() {
    for (count, len) in [(1, 64), (2, 64), (4, 64), (12, 64), (16, 64), (17, 64), (1000, 64), (12288, 64), (13000, 64), (5, 0), (7, 1), (9, 63), (33, 100), (20, 1024), (3, 1025), (40, 4000), (2, 70000), (20, 60000)] {
        let (buffer, messages) = padded_batch(count, len);
        let expected: Vec<Vec<[u8; 32]>> = (0..3).map(|m| messages.iter().map(|message| reference(m, message)).collect()).collect();
        let mut out = vec![[0u8; 32]; count];
        blake3_servil::hash_many(&buffer, len, &mut out);
        assert_eq!(out, expected[0], "hash_many, {count} x {len} B");
        out.fill([0; 32]);
        blake3_servil::hash_many_multithreaded(&buffer, len, &mut out);
        assert_eq!(out, expected[0], "hash_many_multithreaded, {count} x {len} B");
        for (m, mode) in modes().into_iter().enumerate() {
            for threads in thread_choices() {
                out.fill([0; 32]);
                blake3_servil::hash_many_with(mode, threads, &buffer, len, &mut out);
                assert_eq!(out, expected[m], "hash_many_with mode {m} {threads:?}, {count} x {len} B");
            }
        }
    }
}

#[test]
#[should_panic]
fn a_batch_whose_buffer_is_not_whole_slots_is_refused() {
    let mut out = [[0u8; 32]; 2];
    blake3_servil::hash_many(&[0u8; 100], 64, &mut out);
}

// ---------- The queue: handlers that report to the test ----------

/// Records each call and forwards it to the test thread, which may block on
/// the channel (the test's choice; the queue never blocks).
struct Messages(mpsc::Sender<(Vec<u8>, Hash)>);
impl MessageHandler for Messages {
    type Buffer = Vec<u8>;
    fn hashed(&mut self, buffer: Vec<u8>, hash: Hash) {
        self.0.send((buffer, hash)).unwrap();
    }
}

enum PieceEvent {
    Piece(Vec<u8>),
    Finished(Hash),
}
struct Pieces(mpsc::Sender<PieceEvent>);
impl PieceHandler for Pieces {
    type Buffer = Vec<u8>;
    fn piece_done(&mut self, buffer: Vec<u8>) {
        self.0.send(PieceEvent::Piece(buffer)).unwrap();
    }
    fn finished(&mut self, hash: Hash) {
        self.0.send(PieceEvent::Finished(hash)).unwrap();
    }
}

struct Fixed(mpsc::Sender<(Vec<u8>, Vec<[u8; 32]>)>);
impl FixedHandler for Fixed {
    type Buffer = Vec<u8>;
    type Digests = Vec<[u8; 32]>;
    fn hashed(&mut self, buffer: Vec<u8>, digests: Vec<[u8; 32]>) {
        self.0.send((buffer, digests)).unwrap();
    }
}

const EFFICIENCIES: [Efficiency; 2] = [Efficiency::Time, Efficiency::Energy];

/// Messages of many lengths, the vectors' and larger, each its own buffer:
/// every buffer comes back once, in submission order, with its digest.
#[test]
fn queue_of_messages_returns_every_buffer_in_order_with_its_digest() {
    let mut lengths: Vec<usize> = vectors().iter().map(|(len, _)| *len).collect();
    lengths.extend(LARGE);
    for (m, mode) in modes().into_iter().enumerate() {
        for efficiency in EFFICIENCIES {
            let (tx, rx) = mpsc::channel();
            let queue = Queue::messages(mode, efficiency, Messages(tx));
            for &len in &lengths {
                queue.submit(input(len));
            }
            for &len in &lengths {
                let (buffer, hash) = rx.recv().expect("every buffer comes back");
                assert_eq!(buffer.len(), len, "submission order, mode {m} {efficiency:?}");
                assert_eq!(buffer, input(len), "the buffer comes back unchanged");
                assert_eq!(hash, Hash::from(reference(m, &buffer)), "mode {m} {efficiency:?}, {len} bytes");
            }
            drop(queue);
            assert!(rx.try_recv().is_err(), "one call per buffer");
        }
    }
}

/// One long message in pieces of odd sizes: each piece comes back, and one
/// digest arrives after finish, equal to the whole message's.
#[test]
fn queue_of_pieces_returns_each_piece_and_one_digest() {
    for total in [0usize, 1, 1024, 1025, 100_000, 1 << 20, (3 << 20) + 12345] {
        let data = input(total);
        for piece_len in [1usize, 63, 64, 1000, 4096, 65536, 1 << 20] {
            if total / piece_len > 5000 {
                continue;
            }
            for (m, mode) in modes().into_iter().enumerate() {
                for efficiency in EFFICIENCIES {
                    let (tx, rx) = mpsc::channel();
                    let queue = Queue::pieces(mode, efficiency, Pieces(tx));
                    let pieces: Vec<Vec<u8>> = data.chunks(piece_len).map(<[u8]>::to_vec).collect();
                    for piece in &pieces {
                        queue.submit(piece.clone());
                    }
                    queue.finish();
                    for piece in &pieces {
                        match rx.recv().unwrap() {
                            PieceEvent::Piece(buffer) => assert_eq!(&buffer, piece, "pieces return in order"),
                            PieceEvent::Finished(_) => panic!("finished before every piece returned"),
                        }
                    }
                    match rx.recv().unwrap() {
                        PieceEvent::Finished(hash) => assert_eq!(hash, Hash::from(reference(m, &data)), "{total} bytes in {piece_len}-byte pieces, mode {m} {efficiency:?}"),
                        PieceEvent::Piece(_) => panic!("a piece after the last"),
                    }
                }
            }
        }
    }
}

/// Fixed-length messages back to back, several buffers: each buffer comes
/// back with its digests, written into the space the caller handed over.
#[test]
fn queue_of_fixed_length_messages_fills_the_callers_digest_space() {
    for (len, per_buffer) in [(64usize, 1usize), (64, 4), (64, 16), (64, 1000), (64, 16384), (256, 50), (1024, 9), (100, 7)] {
        for (m, mode) in modes().into_iter().enumerate() {
            for efficiency in EFFICIENCIES {
                let (tx, rx) = mpsc::channel();
                let queue = Queue::fixed(len, mode, efficiency, Fixed(tx));
                let batches: Vec<(Vec<u8>, Vec<Vec<u8>>)> = (0..3).map(|b| {
                    let (buffer, messages) = padded_batch(per_buffer + b, len);
                    (buffer, messages)
                }).collect();
                for (buffer, messages) in &batches {
                    queue.submit(buffer.clone(), vec![[0u8; 32]; messages.len()]);
                }
                for (buffer, messages) in &batches {
                    let (returned, digests) = rx.recv().unwrap();
                    assert_eq!(&returned, buffer, "buffers return in order");
                    let expected: Vec<[u8; 32]> = messages.iter().map(|message| reference(m, message)).collect();
                    assert_eq!(digests, expected, "{} x {len} B, mode {m} {efficiency:?}", messages.len());
                }
            }
        }
    }
}

// ---------- The handler contract ----------

/// A handler may submit from inside its call (refill and resubmit): a fixed
/// set of four buffers cycles through the queue until 1000 messages are hashed.
#[test]
fn a_handler_may_resubmit_its_buffer() {
    struct Cycle {
        queue: std::sync::Arc<std::sync::OnceLock<Queue<Cycle>>>,
        left: usize,
        seen: Vec<Hash>,
        done: mpsc::Sender<Vec<Hash>>,
    }
    impl MessageHandler for Cycle {
        type Buffer = Vec<u8>;
        fn hashed(&mut self, mut buffer: Vec<u8>, hash: Hash) {
            self.seen.push(hash);
            if self.left == 0 {
                if self.seen.len() == 1000 {
                    self.done.send(std::mem::take(&mut self.seen)).unwrap();
                }
                return;
            }
            self.left -= 1;
            buffer[0] = buffer[0].wrapping_add(1);
            self.queue.get().unwrap().submit(buffer);
        }
    }
    let (tx, rx) = mpsc::channel();
    let cell = std::sync::Arc::new(std::sync::OnceLock::new());
    let queue = Queue::messages(Mode::Hash, Efficiency::Time, Cycle { queue: cell.clone(), left: 996, seen: Vec::new(), done: tx });
    let _ = cell.set(queue);
    for b in 0..4u8 {
        cell.get().unwrap().submit(vec![b; 1000]);
    }
    let seen = rx.recv_timeout(std::time::Duration::from_secs(60)).expect("1000 digests");
    assert_eq!(seen.len(), 1000);
    assert!(seen.iter().all(|hash| *hash != Hash::from([0u8; 32])));
}

/// Dropping a queue cancels nothing: every buffer in flight still comes back.
#[test]
fn dropping_a_queue_cancels_nothing() {
    let (tx, rx) = mpsc::channel();
    let queue = Queue::messages(Mode::Hash, Efficiency::Time, Messages(tx));
    for i in 0..200 {
        queue.submit(input(1000 + i));
    }
    drop(queue);
    for i in 0..200 {
        let (buffer, hash) = rx.recv_timeout(std::time::Duration::from_secs(60)).expect("buffers come back after the drop");
        assert_eq!(buffer.len(), 1000 + i);
        assert_eq!(hash, Hash::from(reference(0, &buffer)));
    }
}

/// Queues on several threads at once, of every shape, share the engine and
/// each keeps its own order and results.
#[test]
fn queues_on_several_threads_keep_their_own_order() {
    std::thread::scope(|scope| {
        for t in 0..6usize {
            scope.spawn(move || {
                let (tx, rx) = mpsc::channel();
                let queue = Queue::messages(if t % 2 == 0 { Mode::Hash } else { Mode::Keyed(KEY) }, if t % 3 == 0 { Efficiency::Energy } else { Efficiency::Time }, Messages(tx));
                let lengths: Vec<usize> = (0..300).map(|i| (i * 7919 + t * 104729) % 300_000).collect();
                for &len in &lengths {
                    queue.submit(input(len));
                }
                for &len in &lengths {
                    let (buffer, hash) = rx.recv().unwrap();
                    assert_eq!(buffer.len(), len, "thread {t}: its own order");
                    assert_eq!(hash, Hash::from(reference(t % 2, &buffer)), "thread {t}, {len} bytes");
                }
            });
        }
    });
}

/// A panic in a handler aborts the process (fail stop). Run in a child
/// process: the test binary reruns itself with only the panicking test.
#[cfg(unix)]
#[test]
fn a_panicking_handler_aborts_the_process() {
    if std::env::var_os("API_PLAN_PANIC_CHILD").is_some() {
        struct Panics;
        impl MessageHandler for Panics {
            type Buffer = Vec<u8>;
            fn hashed(&mut self, _: Vec<u8>, _: Hash) {
                panic!("a handler's panic");
            }
        }
        let queue = Queue::messages(Mode::Hash, Efficiency::Time, Panics);
        queue.submit(vec![1u8; 100]);
        std::thread::sleep(std::time::Duration::from_secs(30));
        std::process::exit(0); // reached only if the panic did not abort
    }
    let status = std::process::Command::new(std::env::current_exe().unwrap())
        .args(["--exact", "a_panicking_handler_aborts_the_process", "--nocapture"])
        .env("API_PLAN_PANIC_CHILD", "1")
        .status()
        .unwrap();
    use std::os::unix::process::ExitStatusExt;
    assert_eq!(status.signal(), Some(6), "the child aborted (SIGABRT), status {status:?}");
}
