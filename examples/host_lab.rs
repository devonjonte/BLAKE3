//! probe/caller-relevance: does the benchmark's cold-call cost describe
//! real callers? The same calls (servil `hash` at five lengths and
//! `hash_many` with one 64-byte message), the same producer (a copy into
//! a kept buffer before each call), and the same timer (clocks), after
//! seven kinds of caller work between calls, each changing one factor
//! from "busy 1 ms" (register work, the benchmark's gap without its
//! sweep):
//!
//!   nonstop       no work between calls
//!   busy 50 us    shorter register work
//!   busy 1 ms     the base
//!   sleep 1 ms    the thread waits (I/O) instead of computing
//!   read 1 MiB    reads 1 MiB of its own data, then register work to 1 ms
//!   read 8 MiB    8 MiB
//!   read 128 MiB  128 MiB: the benchmark's gap (clocks::measure_after_gaps_prepared)
//!
//! Four fresh processes run it in turn, each beside a run of the
//! benchmark on the same cells (bench-hashes 8ec278d, fork a07a576), so
//! process-to-process spread and harness effects show side by side. Every
//! sample (four calls, each after its own gap) is kept raw; summaries go
//! through clocks::speeds.
use std::hint::black_box;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

const CONDITIONS: [&str; 7] = ["nonstop", "busy 50 us", "busy 1 ms", "sleep 1 ms", "read 1 MiB", "read 8 MiB", "read 128 MiB"];
const CELLS: [(&str, usize); 6] = [("hash", 64), ("hash", 1024), ("hash", 4096), ("hash", 16384), ("hash", 65536), ("hash_many 1", 64)];
const ROUNDS: usize = 48;
const CALLS: u64 = 4;
const PROCESSES: usize = 4;
const BENCH_COMMIT: &str = "8ec278d";
const FORK_COMMIT: &str = "a07a576";

fn show(values: &[u128]) -> String {
    let mut values = values.to_vec();
    values.sort_unstable();
    let n = values.len();
    clocks::speeds::speeds(&values).into_iter().map(|speed| {
        let v = (speed.median + (1u128 << 63)) >> 64;
        let share = (speed.count * 1000 + n / 2) / n;
        format!("{v} ({share}/1000)")
    }).collect::<Vec<_>>().join(" | ")
}

fn child(index: usize) {
    blake3_servil::initialize();
    let work: Vec<u8> = (0..128 * 1024 * 1024usize).map(|i| (i / 64) as u8).collect();
    let source: Vec<u8> = (0..65536usize).map(|i| (i / 8) as u8).collect();
    let mut produced = vec![0u8; 65536];
    let mut digests = [[0u8; 32]; 1];
    let mut samples: Vec<Vec<clocks::PreparedBatch>> = (0..CONDITIONS.len() * CELLS.len()).map(|_| Vec::new()).collect();
    let mut raw = String::from("process,round,condition,api,length,calls,started_ns,wall_ns,p_cycles,p_instructions,p_time_ns,e_cycles,e_instructions,e_time_ns,prep_wall_ns\n");
    let n = samples.len();
    for round in 0..ROUNDS {
        for k in 0..n {
            let slot = (k + round * 5) % n;
            let (c, (api, len)) = (slot / CELLS.len(), CELLS[slot % CELLS.len()]);
            let prepare = |buffer: &mut [u8]| buffer.copy_from_slice(black_box(&source[..len]));
            let one = api == "hash_many 1";
            let mut call = |buffer: &[u8]| {
                if one {
                    blake3_servil::hash_many(black_box(buffer), 64, &mut digests);
                    black_box(digests.as_flattened());
                } else {
                    black_box(blake3_servil::hash(black_box(buffer)));
                }
            };
            let input = &mut produced[..len];
            let m = match CONDITIONS[c] {
                "nonstop" => clocks::measure_after(CALLS, || {}, input, prepare, &mut call),
                "busy 50 us" => clocks::measure_after(CALLS, || clocks::busy_work(50_000), input, prepare, &mut call),
                "busy 1 ms" => clocks::measure_after(CALLS, || clocks::busy_work(1_000_000), input, prepare, &mut call),
                "sleep 1 ms" => clocks::measure_after(CALLS, || std::thread::sleep(std::time::Duration::from_millis(1)), input, prepare, &mut call),
                "read 1 MiB" => clocks::measure_after_gaps_prepared(CALLS, 1_000_000, &work[..1 << 20], input, prepare, &mut call),
                "read 8 MiB" => clocks::measure_after_gaps_prepared(CALLS, 1_000_000, &work[..8 << 20], input, prepare, &mut call),
                "read 128 MiB" => clocks::measure_after_gaps_prepared(CALLS, 1_000_000, &work, input, prepare, &mut call),
                _ => unreachable!(),
            };
            let clocks::Counts { p, e } = m.calls.counts.unwrap_or_default();
            raw += &format!("{index},{round},{},{api},{len},{},{},{},{},{},{},{},{},{},{}\n", CONDITIONS[c], m.calls.calls,
                m.calls.started_ns, m.calls.wall_ns, p.cycles, p.instructions, p.time_ns, e.cycles, e.instructions, e.time_ns,
                m.preparation.wall_ns);
            samples[slot].push(m);
        }
    }
    std::fs::write(format!("process-{index}.csv"), raw).unwrap();

    let mut report = format!("process {index}; load: {}\n", clocks::load::describe(&clocks::load::windows()));
    if index == 0 {
        for batch in clocks::measure(5, 20_000_000, || { black_box(clocks::load::probe_reading()); }) {
            report += &format!("a load reading: {}\n", batch.show());
        }
    }
    for (slot, batches) in samples.iter().enumerate() {
        let (c, (api, len)) = (slot / CELLS.len(), CELLS[slot % CELLS.len()]);
        let wall: Vec<u128> = batches.iter().map(|b| clocks::speeds::per_unit(b.calls.wall_ns, b.calls.calls)).collect();
        let mut line = format!("{api} {len} B, {}: ns/call {}", CONDITIONS[c], show(&wall));
        if batches.iter().all(|b| b.calls.counts.is_some()) {
            let cycles: Vec<u128> = batches.iter().map(|b| { let x = b.calls.counts.unwrap(); clocks::speeds::per_unit(x.p.cycles + x.e.cycles, b.calls.calls) }).collect();
            let instructions: Vec<u128> = batches.iter().map(|b| { let x = b.calls.counts.unwrap(); clocks::speeds::per_unit(x.p.instructions + x.e.instructions, b.calls.calls) }).collect();
            let mhz: Vec<u128> = batches.iter().filter(|b| { let x = b.calls.counts.unwrap(); x.p.time_ns + x.e.time_ns > 0 }).map(|b| u128::from(b.calls.counts.unwrap().mhz()) << 64).collect();
            let e_ns: u64 = batches.iter().map(|b| b.calls.counts.unwrap().e.time_ns).sum();
            let all_ns: u64 = batches.iter().map(|b| { let x = b.calls.counts.unwrap(); x.p.time_ns + x.e.time_ns }).sum();
            line += &format!("; cycles/call {}; instructions/call {}; MHz {}; E time {}/1000", show(&cycles), show(&instructions),
                if mhz.is_empty() { "none".into() } else { show(&mhz) }, (e_ns * 1000 + all_ns.max(1) / 2) / all_ns.max(1));
        }
        report += &line;
        report.push('\n');
    }
    std::fs::write(format!("process-{index}-report.txt"), &report).unwrap();
    print!("{report}");
}

fn checked(command: &mut Command) {
    eprintln!("driver: {command:?}");
    assert!(command.status().expect("run a diagnostic command").success(), "diagnostic command succeeds");
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() == 3 && args[1] == "child" {
        return child(args[2].parse().expect("a process index"));
    }
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let out = std::env::current_dir().expect("the runner's output directory");
    let bench = root.join("bench-hashes");
    assert!(bench.join(".git").exists(), "the runner keeps a benchmark checkout");
    checked(Command::new("git").arg("-C").arg(&bench).args(["fetch", "--quiet", "origin"]));
    checked(Command::new("git").arg("-C").arg(&bench).args(["checkout", "--quiet", "--detach", BENCH_COMMIT]));
    let python = "/opt/homebrew/bin/pypy3";
    let built = Command::new(python).arg(root.join("tools/perf_regress.py")).arg("--root").arg(root)
        .args(["build", "--side", "bench", "--commit", FORK_COMMIT]).stderr(Stdio::inherit()).output().expect("build the benchmark");
    assert!(built.status.success(), "the benchmark builds");
    let exe = PathBuf::from(String::from_utf8(built.stdout).expect("a UTF-8 path").trim());
    let me = std::env::current_exe().expect("this probe's executable");
    for index in 0..PROCESSES {
        checked(Command::new(&me).args(["child", &index.to_string()]).current_dir(&out));
        let folder = out.join(format!("bench-{index}"));
        std::fs::create_dir(&folder).expect("a fresh folder");
        checked(Command::new(&exe).current_dir(&folder).args(["--contenders", "blake3-servil-st,sha256-ring",
            "--points", "64 B,1 KiB,4 KiB,16 KiB,64 KiB,1", "--rounds", "48", "--trace-clocks"]).arg(folder.join("trace.csv")));
    }
}
