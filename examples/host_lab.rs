//! probe/idle-wake-*: what a multithreaded call after idle pays, and where.
//! 1. The cost of waking k condvar sleepers to the waker, and each sleeper's arrival.
//! 2. st against mt after 1 ms of sleep and back to back, by size (median of 101), with the caller's clock.
//! 3. 64 KiB after idle by thread budget.
//! 4. Timelines of single after-idle calls (the library's temporary TRACE hooks), µs from registration.
//! Times are wall ns; the clock is the caller's cycles over its time on cores (P or E).
use std::sync::atomic::{AtomicU64, AtomicUsize, Ordering::SeqCst};
use std::sync::{Arc, Condvar, Mutex};
use std::time::Duration;

fn clock(c: Option<clocks::Counts>) -> String {
    match c {
        Some(c) if c.p.time_ns + c.e.time_ns > 0 => format!(" @{}MHz{}", c.mhz(), if c.e_percent() > 4 { format!(" {}%E", c.e_percent()) } else { String::new() }),
        _ => String::new(),
    }
}

fn median(v: &mut [u64]) -> u64 {
    v.sort();
    v[v.len() / 2]
}

/// Tenths of a microsecond, from ns.
fn us(ns: u64) -> String {
    let t = (ns + 50) / 100;
    format!("{}.{}", t / 10, t % 10)
}

struct Sleepers { m: Mutex<u64>, cv: Condvar, epoch: std::time::Instant, arrived: Vec<AtomicU64>, asleep: AtomicUsize }

fn wake_costs(report: &mut String) {
    let n = std::thread::available_parallelism().unwrap().get() - 1;
    let s = Arc::new(Sleepers { m: Mutex::new(0), cv: Condvar::new(), epoch: clocks::now(), arrived: (0..n).map(|_| AtomicU64::new(0)).collect(), asleep: AtomicUsize::new(0) });
    for i in 0..n {
        let s = s.clone();
        std::thread::spawn(move || {
            let mut seen = 0;
            loop {
                let mut g = s.m.lock().unwrap();
                s.asleep.fetch_add(1, SeqCst);
                while *g == seen {
                    g = s.cv.wait(g).unwrap();
                }
                seen = *g;
                drop(g);
                s.arrived[i].store(clocks::since_ns(s.epoch), SeqCst);
            }
        });
    }
    *report += &format!("1. waking k of {n} condvar sleepers after 1 ms (median of 51): the waker's cost, first and k-th arrival from the wake's start\n");
    for (mode, k) in [("notify_all", n), ("notify_one x k", 1), ("notify_one x k", 2), ("notify_one x k", 4), ("notify_one x k", 7), ("notify_one x k", n)] {
        let (mut cost, mut first, mut last) = (vec![], vec![], vec![]);
        let mut clocks_seen = None;
        for _ in 0..51 {
            while s.asleep.load(SeqCst) < n {
                std::thread::yield_now();
            }
            std::thread::sleep(Duration::from_millis(1));
            for a in &s.arrived {
                a.store(0, SeqCst);
            }
            let all = mode == "notify_all";
            let c0 = clocks::Counts::read();
            let t0 = clocks::since_ns(s.epoch);
            *s.m.lock().unwrap() += 1;
            s.asleep.fetch_sub(if all { n } else { k }, SeqCst);
            if all { s.cv.notify_all() } else { for _ in 0..k { s.cv.notify_one() } }
            let t1 = clocks::since_ns(s.epoch);
            clocks_seen = c0.zip(clocks::Counts::read()).map(|(a, b)| b.since(a));
            cost.push(t1 - t0);
            let mut times: Vec<u64>;
            loop {
                times = s.arrived.iter().map(|a| a.load(SeqCst)).filter(|&t| t != 0).collect();
                if times.len() >= k {
                    break;
                }
                std::hint::spin_loop();
            }
            if !all && k < n {
                s.asleep.fetch_sub(n - k, SeqCst);
                s.cv.notify_all();
                while s.arrived.iter().filter(|a| a.load(SeqCst) != 0).count() < n {
                    std::thread::yield_now();
                }
            }
            times.sort();
            first.push(times[0] - t0);
            last.push(times[k - 1] - t0);
        }
        *report += &format!("  {mode:<14} k={k:>2}: waker {:>6} ns{}  first {:>6}  k-th {:>6}\n", median(&mut cost), clock(clocks_seen), median(&mut first), median(&mut last));
    }
}

/// Median of 101 calls of `f`, each after 1 ms of sleep when `idle`; the caller's clock in that call.
fn calls(f: &dyn Fn(), idle: bool) -> (u64, Option<clocks::Counts>) {
    let mut v: Vec<(u64, Option<clocks::Counts>)> = (0..101)
        .map(|_| {
            if idle {
                std::thread::sleep(Duration::from_millis(1));
            }
            let c0 = clocks::Counts::read();
            let t = clocks::now();
            f();
            let d = clocks::since_ns(t);
            (d, c0.zip(clocks::Counts::read()).map(|(a, b)| b.since(a)))
        })
        .collect();
    v.sort_by_key(|x| x.0);
    v[50]
}

fn show((ns, c): (u64, Option<clocks::Counts>)) -> String {
    format!("{:>7}{}", ns, clock(c))
}

fn timeline(report: &mut String, kib: usize, budget: usize, idle_us: u64) {
    let input = vec![5u8; kib << 10];
    for _ in 0..20 {
        blake3_servil::hash_multithreaded_with_budget(&input, budget);
    }
    *report += &format!("4. timelines, {kib} KiB, budget {budget}, after {idle_us} us (reg: caller registers; reg'd: its wakes done; wokeR/takeR/finR: worker R woke, took, finished a piece; own-done: the caller's last piece; wait-done: return)\n");
    for trial in 0..8 {
        std::thread::sleep(Duration::from_micros(idle_us));
        blake3_servil::trace_take();
        let t = clocks::now();
        std::hint::black_box(blake3_servil::hash_multithreaded_with_budget(std::hint::black_box(&input), budget));
        let total = clocks::since_ns(t);
        let events = blake3_servil::trace_take();
        let Some(&(_, t0)) = events.first() else {
            *report += &format!("  trial {trial}: {} us, on the caller alone (no job)\n", us(total));
            continue;
        };
        let name = |k: u64| match k {
            0 => "reg".to_owned(),
            1 => "reg'd".to_owned(),
            2 => "own-done".to_owned(),
            3 => "wait-done".to_owned(),
            100..=199 => format!("woke{}", k - 100),
            200..=299 => format!("take{}", k - 200),
            _ => format!("fin{}", k - 300),
        };
        let line: Vec<String> = events.iter().map(|&(k, ns)| format!("{}@{}", name(k), us(ns.saturating_sub(t0)))).collect();
        *report += &format!("  trial {trial}: {} us: {}\n", us(total), line.join(" "));
    }
}

fn main() {
    blake3_servil::initialize();
    clocks::set_qos(clocks::USER_INTERACTIVE);
    let mut report = format!("cpus {}\n", std::thread::available_parallelism().unwrap());
    wake_costs(&mut report);
    report += "2. median of 101 calls, ns: after 1 ms of sleep, and back to back\n";
    for kib in [512usize, 768, 1024, 2048, 4096] {
        let input = vec![5u8; kib << 10];
        let st = || {
            std::hint::black_box(blake3_servil::hash(std::hint::black_box(&input)));
        };
        let mt = || {
            std::hint::black_box(blake3_servil::hash_multithreaded(std::hint::black_box(&input)));
        };
        report += &format!("  {kib:>5} KiB  after idle: st {}  mt {}   back to back: st {}  mt {}\n", show(calls(&st, true)), show(calls(&mt, true)), show(calls(&st, false)), show(calls(&mt, false)));
    }
    let input = vec![5u8; 64 << 10];
    report += "3. 64 KiB after idle, by budget, ns:";
    for budget in [1usize, 2, 4, 8, 16] {
        let f = || {
            std::hint::black_box(blake3_servil::hash_multithreaded_with_budget(std::hint::black_box(&input), budget));
        };
        report += &format!("  {budget}: {}", show(calls(&f, true)));
    }
    report += "\n";
    for (kib, budget, idle_us) in [(1024, 16, 0), (1024, 16, 1000), (4096, 16, 0), (4096, 16, 1000)] {
        timeline(&mut report, kib, budget, idle_us);
    }
    print!("{report}");
    std::fs::write("host-lab-report.txt", report).unwrap();
}
