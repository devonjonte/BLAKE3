//! probe/clocks-levels: the machine's load, and per-call distributions of hash(64 KiB),
//! back to back and after 1 ms of sleep, with each call's core kind and clock.
fn main() {
    let mut report = String::new();
    for cmd in [&["sh", "-c", "top -l 2 -n 12 -o cpu -stats pid,command,cpu,threads | tail -22"][..], &["pmset", "-g", "batt"]] {
        let out = std::process::Command::new(cmd[0]).args(&cmd[1..]).output().map(|o| String::from_utf8_lossy(&o.stdout).into_owned()).unwrap_or_else(|e| e.to_string());
        report += &format!("$ {}\n{out}", cmd.join(" "));
    }
    blake3_servil::initialize();
    for qos in [None, Some(clocks::USER_INTERACTIVE)] {
        if let Some(q) = qos {
            clocks::set_qos(q);
        }
        let input = vec![5u8; 64 << 10];
        for idle in [false, true, false] {
            let mut calls: Vec<(u64, u64, u64)> = (0..400)
                .map(|_| {
                    if idle {
                        std::thread::sleep(std::time::Duration::from_millis(1));
                    }
                    let a = clocks::Counts::read().unwrap();
                    let t = clocks::now();
                    std::hint::black_box(blake3_servil::hash(std::hint::black_box(&input)));
                    let ns = clocks::since_ns(t);
                    let c = clocks::Counts::read().unwrap().since(a);
                    let t_all = (c.p.time_ns + c.e.time_ns).max(1);
                    (ns, c.e.time_ns * 100 / t_all, (c.p.cycles + c.e.cycles) * 1000 / t_all)
                })
                .collect();
            let e_calls = calls.iter().filter(|c| c.1 > 50).count();
            calls.sort();
            let q = |p: usize| calls[p * (calls.len() - 1) / 100];
            report += &format!("qos {:>16} {:>13}: {} of 400 calls mostly on E;  ns (E%, MHz) at p5 {:?} p25 {:?} p50 {:?} p75 {:?} p95 {:?}\n",
                if qos.is_some() { "user-interactive" } else { "default" }, if idle { "after 1 ms" } else { "back to back" }, e_calls, q(5), q(25), q(50), q(75), q(95));
        }
    }
    print!("{report}");
    std::fs::write("host-lab-report.txt", report).unwrap();
}
