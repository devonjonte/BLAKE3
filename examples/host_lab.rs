//! probe/p4-*-ecore: hash_many of four 64-byte messages, cycles per call on each core kind,
//! from a thread at background QoS (E-cores) and one at user-interactive (P-cores).
fn main() {
    // Occupy every P-core (12 on an M4 Max) at user-interactive QoS so that
    // threads at background QoS land on the E-cores.
    let stop = std::sync::Arc::new(std::sync::atomic::AtomicBool::new(false));
    let spinners: Vec<_> = (0..14).map(|_| { let stop = stop.clone(); std::thread::spawn(move || {
        clocks::set_qos(clocks::USER_INTERACTIVE);
        let mut x = 1u64;
        while !stop.load(std::sync::atomic::Ordering::Relaxed) { for _ in 0..1000 { x = std::hint::black_box(x.wrapping_mul(3).wrapping_add(1)); } }
    }) }).collect();
    std::thread::sleep(std::time::Duration::from_millis(50));
    let input = vec![7u8; 4 * 64];
    let mut report = String::new();
    for (name, qos) in [("background", clocks::BACKGROUND), ("background", clocks::BACKGROUND)] {
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
                let calls = 2_000_000u64;
                for _ in 0..calls {
                    blake3_servil::hash_many(std::hint::black_box(&input), 64, &mut out);
                    std::hint::black_box(&out);
                }
                let c = clocks::Counts::read().unwrap().since(a);
                // Instructions per call are the same on either core kind, so a
                // level's cycles per call = its cycles per instruction x instructions per call.
                let ipc = (c.p.instructions + c.e.instructions) / calls;
                let per = |cyc: u64, ins: u64, ns: u64| if ins > 0 && ns > 1_000_000 { format!("{} cycles/call ({} ms)", cyc * ipc / ins, ns / 1_000_000) } else { "-".to_owned() };
                lines += &format!("{name:>16}: {ipc} instructions/call; P {}  |  E {}\n", per(c.p.cycles, c.p.instructions, c.p.time_ns), per(c.e.cycles, c.e.instructions, c.e.time_ns));
            }
            lines
        }).join().unwrap();
    }
    stop.store(true, std::sync::atomic::Ordering::Relaxed);
    for s in spinners { s.join().unwrap(); }
    print!("{report}");
    std::fs::write("host-lab-report.txt", report).unwrap();
}
