//! The queue allocates nothing once a program cycling a fixed set of
//! buffers has warmed it up (the io_uring style its design rests on): every
//! allocation in the process, on any thread, is counted, and after warm-up
//! rounds more rounds of every shape at several sizes must make none. Its
//! own test binary, so no other test allocates beside it.
//! (A queue needs threads: none on wasm.)
#![cfg(not(target_family = "wasm"))]

use blake3_servil::{Efficiency, FixedHandler, Hash, MessageHandler, Mode, PieceHandler, Queue};
use std::alloc::{GlobalAlloc, Layout, System};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};

struct Counting;
static ALLOCATIONS: AtomicUsize = AtomicUsize::new(0);

unsafe impl GlobalAlloc for Counting {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        ALLOCATIONS.fetch_add(1, Ordering::SeqCst);
        unsafe { System.alloc(layout) }
    }
    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        unsafe { System.dealloc(ptr, layout) }
    }
    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        ALLOCATIONS.fetch_add(1, Ordering::SeqCst);
        unsafe { System.realloc(ptr, layout, new_size) }
    }
}

#[global_allocator]
static GLOBAL: Counting = Counting;

const BUFFERS: usize = 4;

/// Buffers handed back by a handler, taken by the test thread: a list with
/// room for them all from the start, so returning one allocates nothing.
type Returned<B> = Arc<Mutex<Vec<B>>>;

fn returned<B>() -> Returned<B> {
    Arc::new(Mutex::new(Vec::with_capacity(BUFFERS + 1)))
}

/// Wait for a returned buffer (the test's choice: it spins).
fn take<B>(returned: &Returned<B>) -> B {
    loop {
        if let Some(buffer) = returned.lock().unwrap().pop() {
            return buffer;
        }
        std::hint::spin_loop();
    }
}

struct Messages(Returned<Vec<u8>>);
impl MessageHandler for Messages {
    type Buffer = Vec<u8>;
    fn hashed(&mut self, buffer: Vec<u8>, hash: Hash) {
        std::hint::black_box(hash);
        self.0.lock().unwrap().push(buffer);
    }
}

struct Pieces(Returned<Vec<u8>>, Arc<AtomicUsize>);
impl PieceHandler for Pieces {
    type Buffer = Vec<u8>;
    fn piece_done(&mut self, buffer: Vec<u8>) {
        self.0.lock().unwrap().push(buffer);
    }
    fn finished(&mut self, hash: Hash) {
        std::hint::black_box(hash);
        self.1.fetch_add(1, Ordering::SeqCst);
    }
}

struct Fixed(Returned<(Vec<u8>, Vec<[u8; 32]>)>);
impl FixedHandler for Fixed {
    type Buffer = Vec<u8>;
    type Digests = Vec<[u8; 32]>;
    fn hashed(&mut self, buffer: Vec<u8>, digests: Vec<[u8; 32]>) {
        self.0.lock().unwrap().push((buffer, digests));
    }
}

/// Run `round` `warm` times, then `rounds` times more, and return the
/// allocations those made.
fn allocations_after_warm_up(warm: usize, rounds: usize, mut round: impl FnMut()) -> usize {
    for _ in 0..warm {
        round();
    }
    let before = ALLOCATIONS.load(Ordering::SeqCst);
    for _ in 0..rounds {
        round();
    }
    ALLOCATIONS.load(Ordering::SeqCst) - before
}

#[test]
fn a_warm_queue_allocates_nothing() {
    blake3_servil::initialize_multithreaded();
    for efficiency in [Efficiency::Time, Efficiency::Energy] {
        for len in [64usize, 1024, 64 << 10, 1 << 20] {
            let back = returned();
            let queue = Queue::messages(Mode::Hash, efficiency, Messages(back.clone()));
            for _ in 0..BUFFERS {
                back.lock().unwrap().push(vec![7u8; len]);
            }
            let made = allocations_after_warm_up(50, 500, || {
                let buffer = take(&back);
                queue.submit(buffer);
            });
            assert_eq!(made, 0, "Queue::messages, {len} B, {efficiency:?}: allocations after warm-up");
        }

        for (total, piece) in [(256usize << 10, 64usize << 10), (4 << 20, 64 << 10), (1 << 20, 100_000)] {
            let back = returned();
            let finished = Arc::new(AtomicUsize::new(0));
            let queue = Queue::pieces(Mode::Keyed(&[3; 32]), efficiency, Pieces(back.clone(), finished.clone()));
            for _ in 0..BUFFERS {
                back.lock().unwrap().push(vec![9u8; piece]);
            }
            let mut streams = 0;
            let made = allocations_after_warm_up(5, 30, || {
                let mut left = total;
                while left > 0 {
                    let mut buffer = take(&back);
                    buffer.truncate(left.min(piece));
                    buffer.resize(left.min(piece), 9);
                    left -= buffer.len();
                    queue.submit(buffer);
                }
                queue.finish();
                streams += 1;
                while finished.load(Ordering::SeqCst) < streams {
                    std::hint::spin_loop();
                }
            });
            assert_eq!(made, 0, "Queue::pieces, {total} B in {piece} B pieces, {efficiency:?}: allocations after warm-up");
        }

        for (message_len, count) in [(64usize, 16usize), (64, 16384), (1000, 100)] {
            let back = returned();
            let queue = Queue::fixed(message_len, Mode::Hash, efficiency, Fixed(back.clone()));
            let slot = message_len.next_multiple_of(64);
            for _ in 0..BUFFERS {
                back.lock().unwrap().push((vec![0u8; slot * count], vec![[0u8; 32]; count]));
            }
            let made = allocations_after_warm_up(50, 300, || {
                let (buffer, digests) = take(&back);
                queue.submit(buffer, digests);
            });
            assert_eq!(made, 0, "Queue::fixed, {count} x {message_len} B, {efficiency:?}: allocations after warm-up");
        }
    }
}
