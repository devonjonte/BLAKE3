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

fn child() {
    blake3_servil::initialize_multithreaded();
    let (tx, rx) = mpsc::channel();
    let queue = Queue::messages(Mode::Hash, Efficiency::Time, Handler(tx, None, 0));
    let input = [7u8; 64];
    let mut free: Vec<Vec<u8>> = (0..4).map(|_| Vec::with_capacity(64)).collect();
    let inputs = 200_000;
    let program_before = clocks::Counts::read();
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
    let ns = clocks::since_ns(start);
    let program = program_before.zip(clocks::Counts::read()).map(|(before, after)| after.since(before));
    let engine = *ENGINE_COUNTS.lock().unwrap();
    println!(
        "{} ns per input; program thread: {}; engine thread: {}",
        ns / inputs,
        program.map_or("no counts".into(), |c| show(&c)),
        engine.map_or("no counts".into(), |(c, _)| show(&c)),
    );
}

fn main() {
    if std::env::var_os("QUEUE_PROBE_CHILD").is_some() {
        return child();
    }
    for _ in 0..16 {
        let out = std::process::Command::new(std::env::current_exe().unwrap()).env("QUEUE_PROBE_CHILD", "1").output().unwrap();
        print!("{}", String::from_utf8_lossy(&out.stdout));
    }
}
