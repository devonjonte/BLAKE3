//! probe/p4-*-ecore: hash_many of four 64-byte messages, cycles per call on each core kind,
//! from a thread at background QoS (E-cores) and one at user-interactive (P-cores).
fn main() {
    let input = vec![7u8; 4 * 64];
    let mut report = String::new();
    for (name, qos) in [("background", clocks::BACKGROUND), ("user-interactive", clocks::USER_INTERACTIVE), ("background", clocks::BACKGROUND), ("user-interactive", clocks::USER_INTERACTIVE)] {
        let input = input.clone();
        report += &std::thread::spawn(move || {
            clocks::set_qos(qos);
            let mut out = [[0u8; 32]; 4];
            let t = clocks::now();
            while clocks::since_ns(t) < 50_000_000 {
                blake3_servil::hash_many(std::hint::black_box(&input), 64, &mut out);
            }
            let mut lines = String::new();
            for _ in 0..3 {
                let a = clocks::Counts::read().unwrap();
                let calls = 200_000u64;
                for _ in 0..calls {
                    blake3_servil::hash_many(std::hint::black_box(&input), 64, &mut out);
                    std::hint::black_box(&out);
                }
                let c = clocks::Counts::read().unwrap().since(a);
                let per = |cyc: u64, ns: u64| if ns > 0 { format!("{} cycles/call over {} ms", cyc / calls, ns / 1_000_000) } else { "-".to_owned() };
                lines += &format!("{name:>16}: P {}  |  E {}  (E share {}%)\n", per(c.p.cycles, c.p.time_ns), per(c.e.cycles, c.e.time_ns), c.e_percent());
            }
            lines
        }).join().unwrap();
    }
    print!("{report}");
    std::fs::write("host-lab-report.txt", report).unwrap();
}
