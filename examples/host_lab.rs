//! probe/no-linger-*: st against mt by input size, at three caller gaps: back to back, 20 us of
//! the caller's own work between calls, and 1 ms of sleep. Median of 101 calls, wall ns, each call
//! timed alone (the gap untimed), with the caller's clock (MHz, E share) in the median call.
use std::time::Duration;

#[derive(Clone, Copy)]
enum Gap { None, Work(u64), Sleep(u64) }

fn gap(g: Gap) {
    match g {
        Gap::None => {}
        Gap::Work(us) => {
            // Integer work the optimizer keeps: the caller handling a result.
            let t = clocks::now();
            let mut x = 1u64;
            while clocks::since_ns(t) < us * 1000 {
                for _ in 0..64 {
                    x = std::hint::black_box(x.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407));
                }
            }
        }
        Gap::Sleep(us) => std::thread::sleep(Duration::from_micros(us)),
    }
}

fn calls(f: &dyn Fn(), g: Gap) -> String {
    let mut v: Vec<(u64, Option<clocks::Counts>)> = (0..101)
        .map(|_| {
            gap(g);
            let c0 = clocks::Counts::read();
            let t = clocks::now();
            f();
            let ns = clocks::since_ns(t);
            (ns, c0.zip(clocks::Counts::read()).map(|(a, b)| b.since(a)))
        })
        .collect();
    v.sort_by_key(|x| x.0);
    let (ns, c) = v[50];
    let clock = match c {
        Some(c) if c.p.time_ns + c.e.time_ns > 0 => format!("@{}{}", c.mhz(), if c.e_percent() > 50 { "E" } else { "" }),
        _ => String::new(),
    };
    format!("{ns}{clock}")
}

fn main() {
    blake3_servil::initialize();
    clocks::set_qos(clocks::USER_INTERACTIVE);
    let gaps = [("back to back", Gap::None), ("20 us work", Gap::Work(20)), ("1 ms sleep", Gap::Sleep(1000))];
    let mut report = format!("cpus {}\nmedian of 101 calls, wall ns @ caller MHz (E: mostly on E-cores); each row st | mt at each gap\n", std::thread::available_parallelism().unwrap());
    report += &format!("  {:>8}", "size");
    for (name, _) in gaps {
        report += &format!("  {:>30}", name);
    }
    report += "\n";
    for kib in [64usize, 128, 256, 384, 512, 768, 1024, 2048, 4096] {
        let input = vec![5u8; kib << 10];
        let st = || { std::hint::black_box(blake3_servil::hash(std::hint::black_box(&input))); };
        let mt = || { std::hint::black_box(blake3_servil::hash_multithreaded(std::hint::black_box(&input))); };
        report += &format!("  {:>4} KiB", kib);
        for (_, g) in gaps {
            report += &format!("  {:>30}", format!("{} | {}", calls(&st, g), calls(&mt, g)));
        }
        report += "\n";
    }
    print!("{report}");
    std::fs::write("host-lab-report.txt", report).unwrap();
}
