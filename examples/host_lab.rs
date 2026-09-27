//! Probe (probe/queue-process-state): some processes run the queue's small
//! inputs about 3.5x slower on the Mac (bench-hashes jobs 446-449: many
//! 64 B inputs through Queue::messages 77 ns/B in one process, 21 in the
//! next; servil st level). Each child process here times 64 B inputs the
//! way bench-hashes does (four buffers cycled, the program waiting on its
//! channel) and reads, from inside the handler (on the queue's engine
//! thread) and on the program's thread, their time per core kind: which
//! kind of core each thread ran on, and its clock (wall time and cycles).
use blake3_servil::{Efficiency, Hash, MessageHandler, Mode, Queue};
use std::sync::{mpsc, Mutex};

static ENGINE_COUNTS: Mutex<Option<(clocks::Counts, u64)>> = Mutex::new(None);

struct Handler(mpsc::Sender<(Vec<u8>, Hash)>, Option<clocks::Counts>, u64);
impl MessageHandler for Handler {
    type Buffer = Vec<u8>;
    fn hashed(&mut self, buffer: Vec<u8>, hash: Hash) {
        // The engine thread's counts since its first call here.
        if let Some(now) = clocks::Counts::read() {
            let first = *self.1.get_or_insert(now);
            self.2 += 1;
            *ENGINE_COUNTS.lock().unwrap() = Some((now.since(first), self.2));
        }
        self.0.send((buffer, hash)).unwrap();
    }
}

fn show(c: &clocks::Counts) -> String {
    let ns = c.p.time_ns + c.e.time_ns;
    if ns == 0 {
        return "no time counted".into();
    }
    format!("{} us on cores, {} MHz, {}% on E", ns / 1000, c.mhz(), c.e_percent())
}

/// 64 B inputs through a fresh queue, the program cycling four buffers:
/// ns per input, and the engine thread's counts over them.
fn small_inputs(inputs: u64) -> (u64, Option<clocks::Counts>) {
    *ENGINE_COUNTS.lock().unwrap() = None;
    let (tx, rx) = mpsc::channel();
    let queue = Queue::messages(Mode::Hash, Efficiency::Time, Handler(tx, None, 0));
    let input = [7u8; 64];
    let mut free: Vec<Vec<u8>> = (0..4).map(|_| Vec::with_capacity(64)).collect();
    let start = clocks::now();
    for _ in 0..inputs {
        let mut buffer = match free.pop() {
            Some(buffer) => buffer,
            None => rx.recv().unwrap().0,
        };
        buffer.clear();
        buffer.extend_from_slice(&input);
        queue.submit(buffer);
    }
    while free.len() < 4 {
        free.push(rx.recv().unwrap().0);
    }
    (clocks::since_ns(start) / inputs, ENGINE_COUNTS.lock().unwrap().map(|(c, _)| c))
}

/// A 32 MiB stream through Queue::pieces, 64 KiB pieces, four buffers.
fn stream(input: &[u8]) {
    struct P(mpsc::Sender<Option<Vec<u8>>>);
    impl blake3_servil::PieceHandler for P {
        type Buffer = Vec<u8>;
        fn piece_done(&mut self, b: Vec<u8>) { self.0.send(Some(b)).unwrap(); }
        fn finished(&mut self, _: Hash) { self.0.send(None).unwrap(); }
    }
    let (tx, rx) = mpsc::channel();
    let queue = Queue::pieces(Mode::Hash, Efficiency::Time, P(tx));
    let mut free: Vec<Vec<u8>> = (0..4).map(|_| Vec::with_capacity(65536)).collect();
    for piece in input.chunks(65536) {
        let mut b = match free.pop() { Some(b) => b, None => loop { if let Some(b) = rx.recv().unwrap() { break b } } };
        b.clear(); b.extend_from_slice(piece); queue.submit(b);
    }
    queue.finish();
    while rx.recv().unwrap().is_some() {}
}

fn report(phase: &str) {
    let (ns, engine) = small_inputs(50_000);
    println!("  after {phase}: {ns} ns per 64 B input; engine thread: {}", engine.map_or("no counts".into(), |c| show(&c)));
}

fn child() {
    blake3_servil::initialize_multithreaded();
    report("start");
    let big = vec![3u8; 32 << 20];
    for _ in 0..20 { stream(&big); }
    report("20 streams of 32 MiB");
    std::thread::scope(|scope| {
        for _ in 0..2 { scope.spawn(|| { for _ in 0..20 { small_inputs(20_000); stream(&big[..4 << 20]); } }); }
    });
    report("two threads at once (shared)");
    for _ in 0..300 {
        std::thread::sleep(std::time::Duration::from_millis(1));
        small_inputs(8);
    }
    report("300 calls after 1 ms sleeps (after idle)");
    for _ in 0..20 { std::hint::black_box(blake3_servil::hash_multithreaded(&big)); }
    report("20 hash_multithreaded of 32 MiB");
    println!("--");
}

fn main() {
    if std::env::var_os("QUEUE_PROBE_CHILD").is_some() {
        return child();
    }
    for _ in 0..8 {
        let out = std::process::Command::new(std::env::current_exe().unwrap()).env("QUEUE_PROBE_CHILD", "1").output().unwrap();
        print!("{}", String::from_utf8_lossy(&out.stdout));
    }
}
