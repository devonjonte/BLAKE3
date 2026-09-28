//! Probe (probe/submit-64): where a 64-byte message's time goes in the
//! benchmark's continuous program (1024 buffers in flight, an mpsc channel
//! back), against the single-threaded loop. Mac, after a 300 ms spin.
use blake3_servil::{Efficiency, Hash, MessageHandler, Mode, Queue};
use std::hint::black_box;
use std::sync::mpsc;

struct Back(mpsc::Sender<(Vec<u8>, Hash)>);
impl MessageHandler for Back {
    type Buffer = Vec<u8>;
    fn hashed(&mut self, buffer: Vec<u8>, hash: Hash) {
        self.0.send((buffer, hash)).unwrap();
    }
}

fn spin(ns: u64) {
    let t = clocks::now();
    let mut x = 1u64;
    while clocks::since_ns(t) < ns {
        for _ in 0..1000 {
            x = x.wrapping_mul(6364136223846793005).wrapping_add(1);
        }
    }
    black_box(x);
}

/// The benchmark's program; `timers` adds stage timers on the submitter.
fn queue_run(len: usize, n: usize, flight: usize, timers: bool) -> String {
    let input = vec![7u8; len];
    let (tx, rx) = mpsc::channel();
    let mut free: Vec<Vec<u8>> = (0..flight).map(|_| Vec::with_capacity(len)).collect();
    let queue = Queue::messages(Mode::Hash, Efficiency::Time, Back(tx));
    let (mut wait, mut copy, mut submit, mut waits) = (0u64, 0u64, 0u64, 0u64);
    let cpu0 = clocks::process_cpu_ns();
    let c0 = clocks::Counts::read();
    let t0 = clocks::now();
    let mut got = 0usize;
    for _ in 0..n {
        let t = if timers { Some(clocks::now()) } else { None };
        while free.is_empty() {
            let (b, h) = rx.recv().unwrap();
            black_box(h);
            got += 1;
            free.push(b);
            waits += 1;
        }
        let mut b = free.pop().unwrap();
        let t2 = t.map(|t| {
            wait += clocks::since_ns(t);
            clocks::now()
        });
        b.clear();
        b.extend_from_slice(black_box(&input));
        let t3 = t2.map(|t2| {
            copy += clocks::since_ns(t2);
            clocks::now()
        });
        queue.submit(b);
        if let Some(t3) = t3 {
            submit += clocks::since_ns(t3);
        }
    }
    while got < n {
        black_box(rx.recv().unwrap());
        got += 1;
    }
    let wall = clocks::since_ns(t0);
    let cpu = clocks::process_cpu_ns() - cpu0;
    let c = c0.and_then(|c0| clocks::Counts::read().map(|c1| c1.since(c0)));
    let (mhz, eperc, busy) = c.map_or((0, 0, 0), |c| (c.mhz(), c.e_percent(), (c.p.time_ns + c.e.time_ns) * 100 / wall.max(1)));
    let mut s = format!(
        "queue {len} B x{n}, {flight} in flight{}: {} ps/B, {} ns/msg; submitter busy {busy}% at {mhz} MHz, E {eperc}%; process CPU {} ns/msg",
        if timers { " (timers)" } else { "" },
        wall * 1000 / (n * len) as u64,
        wall / n as u64,
        cpu / n as u64
    );
    if timers {
        s += &format!("; per msg: wait {} ns ({} waits), copy {} ns, submit {} ns", wait / n as u64, waits, copy / n as u64, submit / n as u64);
    }
    s
}

fn st_run(len: usize, n: usize) -> String {
    let input = vec![7u8; len];
    let mut b: Vec<u8> = Vec::with_capacity(len);
    let c0 = clocks::Counts::read();
    let t0 = clocks::now();
    for _ in 0..n {
        b.clear();
        b.extend_from_slice(black_box(&input));
        black_box(blake3_servil::hash(&b));
    }
    let wall = clocks::since_ns(t0);
    let c = c0.and_then(|c0| clocks::Counts::read().map(|c1| c1.since(c0)));
    format!("hash loop {len} B x{n}: {} ps/B, {} ns/msg at {} MHz", wall * 1000 / (n * len) as u64, wall / n as u64, c.map_or(0, |c| c.mhz()))
}

fn main() {
    blake3_servil::initialize_multithreaded();
    spin(300_000_000);
    for len in [64usize, 256] {
        for _ in 0..3 {
            println!("{}", st_run(len, 200_000));
            println!("{}", queue_run(len, 200_000, 1024, false));
            println!("{}", queue_run(len, 200_000, 1024, true));
            println!("{}", queue_run(len, 200_000, 4096, false));
        }
    }
}
