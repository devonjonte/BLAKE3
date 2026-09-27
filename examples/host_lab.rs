//! probe/clocks-levels: which thread_selfcounts level is which core kind, and the machine's power state.
fn spin(ms: u64) -> u64 {
    let t = clocks::now();
    let mut x = 1u64;
    while clocks::since_ns(t) < ms * 1_000_000 {
        for _ in 0..1000 {
            x = std::hint::black_box(x.wrapping_mul(6364136223846793005).wrapping_add(1));
        }
    }
    x
}

fn main() {
    let mut report = String::new();
    for cmd in [&["sysctl", "hw.nperflevels", "hw.perflevel0.name", "hw.perflevel0.physicalcpu", "hw.perflevel1.name", "hw.perflevel1.physicalcpu"][..], &["pmset", "-g"], &["pmset", "-g", "therm"]] {
        let out = std::process::Command::new(cmd[0]).args(&cmd[1..]).output().map(|o| String::from_utf8_lossy(&o.stdout).into_owned() + &String::from_utf8_lossy(&o.stderr)).unwrap_or_else(|e| e.to_string());
        report += &format!("$ {}\n{out}", cmd.join(" "));
    }
    for (name, qos) in [("background", clocks::BACKGROUND), ("user-interactive", clocks::USER_INTERACTIVE), ("background", clocks::BACKGROUND), ("user-interactive", clocks::USER_INTERACTIVE)] {
        let line = std::thread::spawn(move || {
            clocks::set_qos(qos);
            spin(50);
            let a = clocks::Counts::read().unwrap();
            std::hint::black_box(spin(200));
            let c = clocks::Counts::read().unwrap().since(a);
            format!("{name:>16}: level0 {} cycles {} ns ({} MHz)   level1 {} cycles {} ns ({} MHz)\n", c.p.cycles, c.p.time_ns, if c.p.time_ns > 0 { c.p.cycles * 1000 / c.p.time_ns } else { 0 }, c.e.cycles, c.e.time_ns, if c.e.time_ns > 0 { c.e.cycles * 1000 / c.e.time_ns } else { 0 })
        }).join().unwrap();
        report += &line;
    }
    print!("{report}");
    std::fs::write("host-lab-report.txt", report).unwrap();
}
