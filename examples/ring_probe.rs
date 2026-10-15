//! An experiment in a different streaming API: a BLAKE3-owned ring of
//! bytes that the program writes its messages into (as io_uring could read
//! a socket or a file into it), and that hashing threads read from in
//! place. Its layout is hash_many's: each message in a slot of whole
//! blocks, zero-padded, so a run of equal-length messages is one hash_many
//! call. Messages are published with a plain store (no locked instruction
//! per message); threads claim batches of up to 64 messages (one
//! compare-and-swap a batch); the program reads the digests back, in order,
//! on its own thread (no delivery thread), and hashes a batch itself when
//! the ring is full. Built on the public API (hash_many) alone.
//!
//!   ring_probe ring LEN       the ring, messages of LEN bytes
//!   ring_probe queue LEN      Queue::messages, owned buffers cycled back
//!                             through a channel (bench-hashes' pattern)
//!   ring_probe hash LEN       hash() of each message on this thread
//!   ring_probe check          the ring's digests against hash(), mixed lengths
//!
//! One line: ns per message (clocks::measure 2 ms batches,
//! clocks::summary::mean), then each thread's share of the wall time
//! (clocks::threads).
use std::cell::UnsafeCell;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::{mpsc, Arc, Mutex};

const RING_BYTES: usize = 4 << 20;
const SLOTS: usize = 1 << 14;
const BATCH_MESSAGES: usize = 64;
const BATCH_BYTES: usize = 64 << 10;
/// How long an idle thread polls before it sleeps (env IDLE_NS for the experiment).
static IDLE_NS: AtomicUsize = AtomicUsize::new(0);
/// Batches waiting before the program wakes a sleeping thread (env WAKE_AT).
static WAKE_AT: AtomicUsize = AtomicUsize::new(2);

fn slot_len(len: usize) -> usize {
    len.div_ceil(64).max(1) * 64
}

struct Shared {
    bytes: Box<[UnsafeCell<u8>]>,
    offset: Box<[UnsafeCell<usize>]>,
    len: Box<[UnsafeCell<usize>]>,
    digest: Box<[UnsafeCell<[u8; 32]>]>,
    /// The messages of a finished batch, at its first message's slot; 0 until then.
    done: Box<[AtomicUsize]>,
    committed: AtomicUsize,
    claimed: AtomicUsize,
    asleep: Mutex<Vec<std::thread::Thread>>,
    sleepers: AtomicUsize,
    stop: AtomicBool,
}
// Sound: the cells are written by one side and read by the other only
// across the Release/Acquire pairs below (committed, done).
unsafe impl Sync for Shared {}

impl Shared {
    /// Claim and hash one batch, if any is committed and unclaimed.
    fn hash_one_batch(&self) -> bool {
        loop {
            let first = self.claimed.load(Ordering::Acquire);
            let committed = self.committed.load(Ordering::Acquire);
            if first == committed {
                return false;
            }
            // Sound: messages below `committed` are published.
            let off = |i: usize| unsafe { *self.offset[i % SLOTS].get() };
            let len_of = |i: usize| unsafe { *self.len[i % SLOTS].get() };
            let mut end = first + 1;
            let mut bytes = slot_len(len_of(first));
            while end < committed
                && end - first < BATCH_MESSAGES
                && end % SLOTS != 0
                && bytes + slot_len(len_of(end)) <= BATCH_BYTES
                && off(end) == off(end - 1) + slot_len(len_of(end - 1))
            {
                bytes += slot_len(len_of(end));
                end += 1;
            }
            if self.claimed.compare_exchange(first, end, Ordering::AcqRel, Ordering::Relaxed).is_err() {
                continue;
            }
            // Runs of one length, each one hash_many call over the ring in place.
            let mut i = first;
            while i < end {
                let l = len_of(i);
                let mut j = i + 1;
                while j < end && len_of(j) == l {
                    j += 1;
                }
                let start = off(i);
                // Sound: the claimed messages' bytes and digest slots are this
                // thread's until it marks the batch done.
                let input = unsafe { std::slice::from_raw_parts(self.bytes[start].get() as *const u8, slot_len(l) * (j - i)) };
                let out = unsafe { std::slice::from_raw_parts_mut(self.digest[i % SLOTS].get(), j - i) };
                blake3_servil::hash_many(input, l, out);
                i = j;
            }
            self.done[first % SLOTS].store(end - first, Ordering::Release);
            return true;
        }
    }

    fn worker(&self) {
        let mut idle = clocks::now();
        while !self.stop.load(Ordering::Relaxed) {
            if self.hash_one_batch() {
                idle = clocks::now();
                continue;
            }
            if clocks::since_ns(idle) < IDLE_NS.load(Ordering::Relaxed) as u64 {
                std::hint::spin_loop();
                continue;
            }
            self.asleep.lock().unwrap().push(std::thread::current());
            self.sleepers.fetch_add(1, Ordering::SeqCst);
            if self.committed.load(Ordering::SeqCst) == self.claimed.load(Ordering::SeqCst) {
                std::thread::park();
            }
            self.sleepers.fetch_sub(1, Ordering::SeqCst);
            idle = clocks::now();
        }
    }
}

/// The program's side: write messages in, take digests out, in order.
struct Ring {
    shared: Arc<Shared>,
    /// The next message's index, and the bytes' head.
    next: usize,
    head: usize,
    /// The oldest message whose digest is not yet handed back.
    delivered: usize,
}

impl Ring {
    fn new() -> Ring {
        let cells = |n: usize| (0..n).map(|_| UnsafeCell::new(0usize)).collect::<Vec<_>>().into_boxed_slice();
        let shared = Arc::new(Shared {
            bytes: (0..RING_BYTES).map(|_| UnsafeCell::new(0u8)).collect(),
            offset: cells(SLOTS),
            len: cells(SLOTS),
            digest: (0..SLOTS).map(|_| UnsafeCell::new([0u8; 32])).collect(),
            done: (0..SLOTS).map(|_| AtomicUsize::new(0)).collect(),
            committed: AtomicUsize::new(0),
            claimed: AtomicUsize::new(0),
            asleep: Mutex::new(Vec::new()),
            sleepers: AtomicUsize::new(0),
            stop: AtomicBool::new(false),
        });
        let threads = std::thread::available_parallelism().map_or(1, |n| n.get()) - 1;
        for _ in 0..threads {
            let s = shared.clone();
            std::thread::Builder::new().name("ring-worker".into()).spawn(move || s.worker()).unwrap();
        }
        Ring { shared, next: 0, head: 0, delivered: 0 }
    }

    /// The ring offset of the oldest undelivered message (the bytes in use start there).
    fn tail(&self) -> Option<usize> {
        (self.delivered < self.next).then(|| unsafe { *self.shared.offset[self.delivered % SLOTS].get() })
    }

    /// Room for `slot` bytes at the head, wrapping to the start when the end has too little.
    fn room(&self, slot: usize) -> Option<usize> {
        if self.next - self.delivered == SLOTS {
            return None;
        }
        match self.tail() {
            None => Some(if self.head + slot <= RING_BYTES { self.head } else { 0 }),
            // In use: [tail, head), free at the end and before tail.
            Some(tail) if tail < self.head => {
                if self.head + slot <= RING_BYTES {
                    Some(self.head)
                } else {
                    (slot <= tail).then_some(0)
                }
            }
            // Wrapped: in use from tail to the end and from the start to head.
            Some(tail) => (self.head + slot <= tail).then_some(self.head),
        }
    }

    /// Write one message: `fill` writes its `len` bytes into the ring.
    fn submit(&mut self, len: usize, mut fill: impl FnMut(&mut [u8]), mut digest: impl FnMut(&[u8; 32])) {
        let slot = slot_len(len);
        assert!(slot <= RING_BYTES / 2, "a message under half the ring");
        let at = loop {
            if let Some(at) = self.room(slot) {
                break at;
            }
            // Full: hand back what is done, else hash a batch here.
            self.publish();
            if self.collect(&mut digest) == 0 && !self.shared.hash_one_batch() {
                std::hint::spin_loop();
            }
        };
        // Sound: [at, at + slot) is free: no thread reads it until committed.
        let bytes = unsafe { std::slice::from_raw_parts_mut(self.shared.bytes[at].get(), slot) };
        fill(&mut bytes[..len]);
        bytes[len..].fill(0);
        let i = self.next;
        unsafe {
            *self.shared.offset[i % SLOTS].get() = at;
            *self.shared.len[i % SLOTS].get() = len;
        }
        self.next = i + 1;
        self.head = at + slot;
        // Published a batch at a time: one store per 64 messages (or when
        // the batch reaches its bytes), so the hashing threads polling the
        // count take its line away from this thread that seldom.
        if self.next % BATCH_MESSAGES == 0 || (self.next - self.shared.committed.load(Ordering::Relaxed)) * slot >= BATCH_BYTES {
            self.publish();
        }
    }

    /// Publish every message written, and wake a sleeping thread for them.
    fn publish(&mut self) {
        if self.shared.committed.load(Ordering::Relaxed) == self.next {
            return;
        }
        self.shared.committed.store(self.next, Ordering::SeqCst);
        // Waiting work in batches' worth of bytes (this message's slot as the measure).
        let slot = slot_len(unsafe { *self.shared.len[(self.next - 1) % SLOTS].get() });
        let waiting = ((self.next - self.shared.claimed.load(Ordering::Relaxed)) * slot).div_ceil(BATCH_BYTES).max((self.next - self.shared.claimed.load(Ordering::Relaxed)) / BATCH_MESSAGES);
        if self.shared.sleepers.load(Ordering::SeqCst) > 0 && waiting >= WAKE_AT.load(Ordering::Relaxed) {
            if let Some(t) = self.shared.asleep.lock().unwrap().pop() {
                t.unpark();
            }
        }
    }

    /// Hand back every digest done, in order; how many.
    fn collect(&mut self, mut digest: impl FnMut(&[u8; 32])) -> usize {
        let mut n = 0;
        while self.delivered < self.next {
            let k = self.shared.done[self.delivered % SLOTS].load(Ordering::Acquire);
            if k == 0 {
                break;
            }
            self.shared.done[self.delivered % SLOTS].store(0, Ordering::Relaxed);
            for i in self.delivered..self.delivered + k {
                // Sound: the batch is done (Acquire above).
                digest(unsafe { &*self.shared.digest[i % SLOTS].get() });
            }
            self.delivered += k;
            n += k;
        }
        n
    }

    /// Every message's digest back: hashes what no thread has taken.
    fn finish(&mut self, mut digest: impl FnMut(&[u8; 32])) {
        self.publish();
        while self.delivered < self.next {
            if self.collect(&mut digest) == 0 && !self.shared.hash_one_batch() {
                std::hint::spin_loop();
            }
        }
    }
}

struct Back(mpsc::SyncSender<Vec<u8>>);
impl blake3_servil::MessageHandler for Back {
    type Buffer = Vec<u8>;
    fn hashed(&mut self, buffer: Vec<u8>, hash: blake3_servil::Hash) {
        std::hint::black_box(hash);
        self.0.send(buffer).unwrap();
    }
}

const PER_CALL: usize = 1024;

const LENS: [usize; 6] = [64, 256, 1024, 4096, 16384, 65536];

/// One mode's batches at messages of `len` bytes.
fn measure(mode: &str, len: usize) -> Vec<clocks::Batch> {
    let source: Vec<u8> = (0..len).map(|i| (i % 251) as u8).collect();
    match mode {
        "hash" => clocks::measure(64, 2_000_000, || {
            for _ in 0..PER_CALL {
                std::hint::black_box(blake3_servil::hash(std::hint::black_box(&source)));
            }
        }),
        "ring" => {
            let mut ring = Ring::new();
            let b = clocks::measure(64, 2_000_000, || {
                for _ in 0..PER_CALL {
                    ring.submit(len, |b| b.copy_from_slice(&source), |d| { std::hint::black_box(d); });
                }
                ring.collect(|d| { std::hint::black_box(d); });
            });
            ring.finish(|d| { std::hint::black_box(d); });
            b
        }
        "queue" => {
            let (tx, rx) = mpsc::sync_channel::<Vec<u8>>(PER_CALL);
            let queue = blake3_servil::Queue::messages(blake3_servil::Mode::Hash, Back(tx));
            let mut free: Vec<Vec<u8>> = (0..PER_CALL).map(|_| vec![0u8; len]).collect();
            let b = clocks::measure(64, 2_000_000, || {
                for _ in 0..PER_CALL {
                    let mut buf = match free.pop() { Some(b) => b, None => rx.recv().unwrap() };
                    buf.copy_from_slice(&source);
                    queue.submit(buf);
                }
            });
            for _ in free.len()..PER_CALL {
                rx.recv().unwrap();
            }
            b
        }
        _ => panic!("ring | queue | hash LEN, or check"),
    }
}

fn main() {
    blake3_servil::initialize_multithreaded();
    for (name, var) in [("IDLE_NS", &IDLE_NS), ("WAKE_AT", &WAKE_AT)] {
        if let Some(v) = std::env::var_os(name) {
            var.store(v.to_str().unwrap().parse().unwrap(), Ordering::Relaxed);
        }
    }
    let args: Vec<String> = std::env::args().skip(1).collect();
    let mode = args[0].as_str();
    if mode == "check" {
        let source: Vec<u8> = (0..70_000).map(|i| (i * 7 % 251) as u8).collect();
        let mut ring = Ring::new();
        let lens: Vec<usize> = (0..200_000).map(|i| [64, 64, 64, 1, 100, 1024, 3000, 64, 65536, 0][i % 10] + (i % 3) * (i % 10 == 6) as usize).collect();
        let mut got = Vec::new();
        for (i, &len) in lens.iter().enumerate() {
            ring.submit(len, |b| b.copy_from_slice(&source[i % 997..][..len]), |d| got.push(*d));
        }
        ring.finish(|d| got.push(*d));
        for (i, &len) in lens.iter().enumerate() {
            assert_eq!(&got[i], blake3_servil::hash(&source[i % 997..][..len]).as_bytes(), "message {i}, {len} bytes");
        }
        println!("check: {} digests equal hash()'s", lens.len());
        return;
    }
    if let Some(which) = mode.strip_prefix("sporadic-") {
        // One message at a time after a 1 ms sleep, its digest awaited: a
        // server's request, a wait, the next (clocks' gaps, idle).
        let len: usize = args[1].parse().unwrap();
        let source: Vec<u8> = (0..len).map(|i| (i % 251) as u8).collect();
        let calls = 400;
        let ns = match which {
            "hash" => {
                let mut input = source.clone();
                clocks::measure_after_gaps_prepared(calls, clocks::Gap::Idle, 1_000_000, &mut input, |b| b.copy_from_slice(&source), |b| { std::hint::black_box(blake3_servil::hash(b)); }).calls.wall_ns
            }
            "ring" => {
                let ring = std::cell::RefCell::new(Ring::new());
                let mut unit = ();
                clocks::measure_after_gaps_prepared(calls, clocks::Gap::Idle, 1_000_000, &mut unit, |_| {}, |_| {
                    let mut r = ring.borrow_mut();
                    r.submit(len, |b| b.copy_from_slice(&source), |d| { std::hint::black_box(d); });
                    r.finish(|d| { std::hint::black_box(d); });
                }).calls.wall_ns
            }
            "queue" => {
                let (tx, rx) = mpsc::sync_channel::<Vec<u8>>(1);
                let queue = blake3_servil::Queue::messages(blake3_servil::Mode::Hash, Back(tx));
                let free = std::cell::RefCell::new(Some(vec![0u8; len]));
                let mut unit = ();
                clocks::measure_after_gaps_prepared(calls, clocks::Gap::Idle, 1_000_000, &mut unit, |_| {}, |_| {
                    let mut buf = free.borrow_mut().take().unwrap();
                    buf.copy_from_slice(&source);
                    queue.submit(buf);
                    *free.borrow_mut() = Some(rx.recv().unwrap());
                }).calls.wall_ns
            }
            "channel" => {
                // The handover alone: a thread that returns each buffer it
                // receives, both sides asleep between messages.
                let (to_tx, to_rx) = mpsc::sync_channel::<Vec<u8>>(1);
                let (back_tx, back_rx) = mpsc::sync_channel::<Vec<u8>>(1);
                std::thread::spawn(move || { for b in to_rx { back_tx.send(b).unwrap(); } });
                let free = std::cell::RefCell::new(Some(vec![0u8; len]));
                let mut unit = ();
                clocks::measure_after_gaps_prepared(calls, clocks::Gap::Idle, 1_000_000, &mut unit, |_| {}, |_| {
                    let mut buf = free.borrow_mut().take().unwrap();
                    buf.copy_from_slice(&source);
                    to_tx.send(buf).unwrap();
                    *free.borrow_mut() = Some(back_rx.recv().unwrap());
                }).calls.wall_ns
            }
            _ => panic!("sporadic-hash | sporadic-ring | sporadic-queue | sporadic-channel LEN"),
        };
        println!("{mode} {len} B: {:.1} us a message", ns as f64 / calls as f64 / 1000.0);
        return;
    }
    if mode == "samples" {
        // ring_probe samples MODE OUT: every length, one samples file in
        // bench-hashes' format, for `bench-hashes compare`.
        let (which, out) = (args[1].as_str(), &args[2]);
        let mut rows = String::new();
        let mut busy = String::new();
        for len in LENS {
            let before = clocks::threads::snapshot();
            let started = clocks::now();
            let batches = measure(which, len);
            let wall = clocks::since_ns(started);
            if let (Some(b), Some(a)) = (before, clocks::threads::snapshot()) {
                let total: u64 = clocks::threads::since(&b, &a).iter().map(|x| x.cpu_ns).sum();
                busy += &format!("# cpus busy at {len} B: {}.{:02}\n", total / wall, total % wall * 100 / wall);
            }
            let samples: Vec<String> = batches.iter().map(|b| format!("{}/{}", b.wall_ns, b.calls * PER_CALL as u64 * len.max(1) as u64)).collect();
            let starts: Vec<String> = batches.iter().map(|b| (b.started_ns / 1_000_000).to_string()).collect();
            rows += &format!("stream\tsolo\tOwnedMessages\t{len} B\tB\t{}\t{}\n", samples.join(","), starts.join(","));
        }
        let load = clocks::load::describe(&clocks::load::windows());
        std::fs::write(out, format!("# bench-hashes samples v4\n# probe: ring_probe {which}\n# load: {load}\n# power: not reported by this probe\n{busy}contender\tscenario\tuse_case\tpoint\tunit\tns/units\tstart ms\n{rows}")).unwrap();
        return;
    }
    let len: usize = args[1].parse().unwrap();
    let before = clocks::threads::snapshot();
    let started = clocks::now();
    let batches = measure(mode, len);
    let wall = clocks::since_ns(started);
    let mean = clocks::summary::mean(batches.iter().map(|b| (b.wall_ns, b.calls * PER_CALL as u64)));
    let milli = (mean * 1000 + (1 << 63)) >> 64;
    let threads = match (before, clocks::threads::snapshot()) {
        (Some(b), Some(a)) => {
            let t = clocks::threads::since(&b, &a);
            let total: u64 = t.iter().map(|x| x.cpu_ns).sum();
            format!("CPUs busy {}.{:02}", total / wall, total % wall * 100 / wall)
        }
        _ => "per-thread CPU time not given on this platform".into(),
    };
    println!("{mode} {len} B: {}.{:03} ns/message; {threads}; {}", milli / 1000, milli % 1000, clocks::load::describe(&clocks::load::windows()));
}
