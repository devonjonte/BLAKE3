//! probe/idle-wake: what a multithreaded call after idle pays, by the number
//! of pool workers woken (the process confined to fewer CPUs by budget is not
//! possible on macOS, so budgets and sizes stand in), beside st and back to back.
//! Median of 101 calls, ns, and the clock the caller ran at.
fn after_idle(f: &dyn Fn(), idle: bool) -> (u64, Option<clocks::Counts>) {
    let mut ns: Vec<(u64, Option<clocks::Counts>)> = (0..101)
        .map(|_| {
            if idle {
                std::thread::sleep(std::time::Duration::from_millis(1));
            }
            let c0 = clocks::Counts::read();
            let t = clocks::now();
            f();
            let d = clocks::since_ns(t);
            (d, c0.zip(clocks::Counts::read()).map(|(a, b)| b.since(a)))
        })
        .collect();
    ns.sort_by_key(|x| x.0);
    ns[50]
}

fn main() {
    blake3_servil::initialize();
    clocks::set_qos(clocks::USER_INTERACTIVE);
    let show = |(ns, c): (u64, Option<clocks::Counts>)| format!("{ns} ns{}", c.map_or(String::new(), |c| format!(" @{}MHz", c.mhz())));
    let mut report = format!("cpus {}\n", std::thread::available_parallelism().unwrap());
    for len in [64usize << 10, 128 << 10, 256 << 10, 1 << 20] {
        let input = vec![5u8; len];
        let st = || { std::hint::black_box(blake3_servil::hash(std::hint::black_box(&input))); };
        let mt = || { std::hint::black_box(blake3_servil::hash_multithreaded(std::hint::black_box(&input))); };
        report += &format!("{:>5} KiB  after idle: st {}  mt {}   back to back: st {}  mt {}\n", len >> 10,
            show(after_idle(&st, true)), show(after_idle(&mt, true)), show(after_idle(&st, false)), show(after_idle(&mt, false)));
    }
    let input = vec![5u8; 64 << 10];
    let mut line = "64 KiB after idle, by budget:".to_owned();
    for budget in [1usize, 2, 4, 8, 16] {
        let f = || { std::hint::black_box(blake3_servil::hash_multithreaded_with_budget(std::hint::black_box(&input), budget)); };
        line += &format!("  {budget}: {}", after_idle(&f, true).0);
    }
    report += &line;
    println!("{report}");
    std::fs::write("host-lab-report.txt", report).unwrap();
}
