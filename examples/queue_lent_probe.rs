//! probe/devon-queue-lent-baseline: servil's side of probe/devon-job-trace's
//! `every10 cell` measurement. Lent batches (hash_many_multithreaded) of N
//! 64-byte messages, each call's whole sample as the bench's lent cell
//! makes it (the input copied into a kept buffer, the call, each digest
//! copied into a ring of 1024 slots), 10 calls after each block of
//! streaming (256 messages of 64 KiB through a Queue), the calls alone
//! timed; DUO=1 streams the block on two threads at once.
//!
//!     cargo run --release --example queue_lent_probe -- 16384 3000 every10
//!     cargo run --release --example queue_lent_probe -- 16384 3000 none
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;

struct Count(Arc<AtomicUsize>);

impl blake3_servil::MessageHandler for Count {
    type Buffer = Arc<[u8]>;
    fn hashed(&mut self, _: Arc<[u8]>, hash: blake3_servil::Hash) {
        std::hint::black_box(hash);
        self.0.fetch_add(1, Ordering::Release);
    }
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let n: usize = args.first().map_or(16384, |a| a.parse().expect("a count"));
    let calls: usize = args.get(1).map_or(3000, |a| a.parse().expect("a count"));
    let every10 = args.get(2).is_some_and(|a| a == "every10");
    let duo = std::env::var_os("DUO").is_some();
    blake3_servil::initialize_multithreaded();
    let messages: Vec<Arc<[u8]>> = (0..256u32).map(|i| Arc::from(i.to_le_bytes().repeat(16384))).collect();
    let one_stream = || {
        let done = Arc::new(AtomicUsize::new(0));
        let queue = blake3_servil::Queue::messages(blake3_servil::Mode::Hash, Count(done.clone()));
        for m in &messages {
            queue.submit(m.clone());
        }
        while done.load(Ordering::Acquire) < messages.len() {
            std::hint::spin_loop();
        }
        drop(queue);
    };
    let block = || {
        if duo {
            std::thread::scope(|scope| {
                scope.spawn(one_stream);
                scope.spawn(one_stream);
            });
        } else {
            one_stream();
        }
    };
    let source = vec![0x5au8; n * 64];
    let mut kept = vec![0u8; n * 64];
    let mut out = vec![[0u8; 32]; n];
    let mut slots = vec![[0u8; 32]; 1024];
    let mut next = 0usize;
    let mut call = || {
        kept.copy_from_slice(std::hint::black_box(&source));
        blake3_servil::hash_many_multithreaded(&kept, 64, &mut out);
        for digest in &out {
            slots[next % 1024] = *std::hint::black_box(digest);
            next += 1;
        }
        std::hint::black_box(&slots);
    };
    for _ in 0..200 {
        call();
    }
    let mut timed_ns = 0u128;
    for _ in 0..calls / 10 {
        if every10 {
            block();
        }
        let began = std::time::Instant::now();
        for _ in 0..10 {
            call();
        }
        timed_ns += began.elapsed().as_nanos();
    }
    println!("batch {n}: {} ns a call ({} calls, {})", timed_ns / (calls / 10 * 10) as u128, calls / 10 * 10, if every10 { if duo { "two streams before each 10" } else { "a stream before each 10" } } else { "no streams" });
}
