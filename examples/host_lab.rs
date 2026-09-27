//! probe/clock-pauses: how far the core's clock falls after a pause, and how fast it recovers.
//! Each trial: 20 ms of back-to-back calls (a warm core), a pause, then calls timed one by one.
//! A. hash(64 KiB): the calls after the pause, by index: median wall ns, median caller clock (MHz), calls on E.
//! B. the first call after the pause for hash and hash_multithreaded at 64 KiB and 1 MiB: median wall ns.
//! Trials rotate through the pauses, 15 per pause. Integers throughout.
use std::time::Duration;

#[derive(Clone, Copy)]
enum Pause { Sleep(u64), Spin(u64) }

impl Pause {
    fn name(self) -> String {
        match self {
            Pause::Sleep(0) => "none".to_owned(),
            Pause::Sleep(us) => format!("sleep {us} us"),
            Pause::Spin(us) => format!("spin {us} us"),
        }
    }
    fn run(self) {
        match self {
            Pause::Sleep(0) => {}
            Pause::Sleep(us) => std::thread::sleep(Duration::from_micros(us)),
            Pause::Spin(us) => {
                let t = clocks::now();
                while clocks::since_ns(t) < us * 1000 {
                    std::hint::spin_loop();
                }
            }
        }
    }
}

const PAUSES: [Pause; 12] = [Pause::Sleep(0), Pause::Sleep(20), Pause::Sleep(50), Pause::Sleep(100), Pause::Sleep(200), Pause::Sleep(500),
    Pause::Sleep(1000), Pause::Sleep(2000), Pause::Sleep(5000), Pause::Sleep(20000), Pause::Sleep(100000), Pause::Spin(1000)];
const TRIALS: usize = 15;
const AFTER: usize = 40;
const SHOWN: [usize; 8] = [1, 2, 3, 5, 10, 20, 30, 40];

fn warm(f: &dyn Fn()) {
    let t = clocks::now();
    while clocks::since_ns(t) < 20_000_000 {
        f();
    }
}

fn median(mut v: Vec<u64>) -> u64 {
    v.sort();
    v[v.len() / 2]
}

/// One call's wall ns, clock in MHz (0 without counts), and whether most of its time was on E.
fn timed(f: &dyn Fn()) -> (u64, u64, bool) {
    let a = clocks::Counts::read();
    let t = clocks::now();
    f();
    let ns = clocks::since_ns(t);
    match a.zip(clocks::Counts::read()).map(|(a, b)| b.since(a)) {
        Some(c) if c.p.time_ns + c.e.time_ns > 0 => (ns, c.mhz(), c.e_percent() > 50),
        _ => (ns, 0, false),
    }
}

fn main() {
    blake3_servil::initialize();
    clocks::set_qos(clocks::USER_INTERACTIVE);
    let small = vec![5u8; 64 << 10];
    let large = vec![5u8; 1 << 20];
    let st_small = || { std::hint::black_box(blake3_servil::hash(std::hint::black_box(&small))); };
    let mut report = format!("cpus {}\nA. hash(64 KiB), calls after the pause: median wall ns @ median MHz; calls mostly on E of {TRIALS} x {AFTER}\n", std::thread::available_parallelism().unwrap());
    // results[pause][call] = (ns, mhz, on_e) over trials
    let mut results = vec![vec![Vec::new(); AFTER]; PAUSES.len()];
    for _ in 0..TRIALS {
        for (p, pause) in PAUSES.iter().enumerate() {
            warm(&st_small);
            pause.run();
            for call in 0..AFTER {
                results[p][call].push(timed(&st_small));
            }
        }
    }
    report += &format!("  {:>16}", "pause \\ call");
    for i in SHOWN {
        report += &format!("  {:>14}", format!("#{i}"));
    }
    report += "  on E\n";
    for (p, pause) in PAUSES.iter().enumerate() {
        report += &format!("  {:>16}", pause.name());
        for i in SHOWN {
            let calls = &results[p][i - 1];
            report += &format!("  {:>14}", format!("{}@{}", median(calls.iter().map(|c| c.0).collect()), median(calls.iter().map(|c| c.1).collect())));
        }
        report += &format!("  {}\n", results[p].iter().flatten().filter(|c| c.2).count());
    }
    let mt_small = || { std::hint::black_box(blake3_servil::hash_multithreaded(std::hint::black_box(&small))); };
    let st_large = || { std::hint::black_box(blake3_servil::hash(std::hint::black_box(&large))); };
    let mt_large = || { std::hint::black_box(blake3_servil::hash_multithreaded(std::hint::black_box(&large))); };
    let fs: [(&str, &dyn Fn()); 4] = [("st 64 KiB", &st_small), ("mt 64 KiB", &mt_small), ("st 1 MiB", &st_large), ("mt 1 MiB", &mt_large)];
    report += "B. the first call after the pause, each after 20 ms of its own calls: median wall ns @ median MHz\n";
    report += &format!("  {:>16}", "pause");
    for (name, _) in fs {
        report += &format!("  {name:>16}");
    }
    report += "\n";
    let mut first = vec![vec![Vec::new(); fs.len()]; PAUSES.len()];
    for _ in 0..TRIALS {
        for (p, pause) in PAUSES.iter().enumerate() {
            for (k, (_, f)) in fs.iter().enumerate() {
                warm(*f);
                pause.run();
                first[p][k].push(timed(*f));
            }
        }
    }
    for (p, pause) in PAUSES.iter().enumerate() {
        report += &format!("  {:>16}", pause.name());
        for k in 0..fs.len() {
            let calls = &first[p][k];
            report += &format!("  {:>16}", format!("{}@{}", median(calls.iter().map(|c| c.0).collect()), median(calls.iter().map(|c| c.1).collect())));
        }
        report += "\n";
    }
    print!("{report}");
    std::fs::write("host-lab-report.txt", report).unwrap();
}
