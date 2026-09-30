//! probe/caller-relevance, factors: which state, left before a 128 MiB
//! read sweep, reaches the call after it? In the benchmark, appending one
//! line to a file before each sample's gap doubled servil's cold 4 KiB
//! call (bench-hashes NOTES, "Cold calls: the harness doubles them").
//!
//! Every condition changes one thing from the base: nothing before the
//! gap, then clocks::measure_after_gaps_prepared's gap (read 128 MiB at
//! 64-byte steps, register work to 1 ms), then the producer's copy and
//! the call (servil `hash`, 64 B, 4 KiB, 16 KiB), each timed by clocks.
//! What runs before the gap: getpid; a write to /dev/null; open and close
//! /dev/null; append a line to a file (open, write, close); a fresh 1 MiB
//! heap block written page by page (page faults); a small String. The
//! gap: writing 128 MiB instead of reading; reading 32 or 512 MiB; no
//! sweep (register work alone), also after the append. Each sample's gap
//! duration is recorded (the sweep may outlast 1 ms).
//!
//! Round two (job 793) dissects "open-close": a path lookup alone (stat),
//! an fd alone (fstat, dup and close), a regular file, a write to a held
//! regular file, a yield, 10 ms of register work between the open-close
//! and the sweep, a 512 MiB sweep after it, and the hash's code warmed at
//! the gap's end (a call on another buffer of the same length).
//!
//! Round three (job 794): code or its translation? After the sweep, read
//! one byte of each 16 KiB page of this executable's text as data ("code
//! pages": its page-table entries and TLB entries warm, its instruction
//! lines still cold), or every 64-byte line of it ("code lines": lines in
//! the unified caches too); and 10 ms of register work before the sweep
//! without the open-close, to tell time from the open.
//!
//! Round four (job 795): does the thread change cores? Each call is
//! measured alone (four a sample, each after its own gap), with the CPU
//! the thread ran on at the gap's start, at its end, and at the
//! producer's copy just before the call (pthread_cpu_number_np on macOS,
//! sched_getcpu on Linux); "sleep 1 ms" sleeps before the sweep.
//!
//! Round five (job 796): the core's instruction cache. "icache
//! invalidated" invalidates the instruction-cache lines of this
//! executable's text before the sweep (macOS sys_icache_invalidate,
//! Linux __clear_cache: no file, no syscall), with and without the sweep.
//!
//! The driver runs three probe processes (the third at user-interactive
//! QoS) between runs of the benchmark with and without its shared copies.
use std::cell::Cell;
use std::hint::black_box;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

const CONDITIONS: [&str; 6] = ["base", "open-close", "icache invalidated", "no sweep", "open-close, no sweep", "icache invalidated, no sweep"];
const LENGTHS: [usize; 3] = [64, 4096, 16384];
const ROUNDS: usize = 48;
const CALLS: u64 = 4;
const BENCH_COMMIT: &str = "1f666f952e10";
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

/// This executable's text segment, as a slice: Mach-O's __TEXT from the
/// file's load commands plus the slide; Linux's executable mapping that
/// holds servil's `hash`.
fn text() -> &'static [u8] {
    let hash = blake3_servil::hash as fn(&[u8]) -> blake3_servil::Hash as usize;
    #[cfg(target_vendor = "apple")]
    {
        unsafe extern "C" { static _mh_execute_header: u8; }
        let file = std::fs::read(std::env::current_exe().unwrap()).unwrap();
        let word = |at: usize| u32::from_le_bytes(file[at..at + 4].try_into().unwrap()) as usize;
        let long = |at: usize| u64::from_le_bytes(file[at..at + 8].try_into().unwrap()) as usize;
        assert_eq!(word(0), 0xfeedfacf, "a 64-bit Mach-O executable");
        let (mut at, commands) = (32, word(16));
        for _ in 0..commands {
            if word(at) == 0x19 && &file[at + 8..at + 14] == b"__TEXT" && file[at + 14] == 0 {
                let (vmaddr, vmsize) = (long(at + 24), long(at + 32));
                let start = &raw const _mh_execute_header as usize;
                assert!(start <= hash && hash < start + vmsize, "hash lies in __TEXT");
                let _ = vmaddr;
                // Sound: __TEXT is mapped readable for its whole vmsize.
                return unsafe { std::slice::from_raw_parts(start as *const u8, vmsize) };
            }
            at += word(at + 4);
        }
        panic!("no __TEXT segment");
    }
    #[cfg(not(target_vendor = "apple"))]
    {
        for line in std::fs::read_to_string("/proc/self/maps").unwrap().lines() {
            let mut fields = line.split_whitespace();
            let (range, perms) = (fields.next().unwrap(), fields.next().unwrap());
            let (a, b) = range.split_once('-').unwrap();
            let (a, b) = (usize::from_str_radix(a, 16).unwrap(), usize::from_str_radix(b, 16).unwrap());
            if perms.starts_with("r-x") && a <= hash && hash < b {
                // Sound: the mapping is readable for its whole length.
                return unsafe { std::slice::from_raw_parts(a as *const u8, b - a) };
            }
        }
        panic!("no executable mapping holds hash");
    }
}

/// The CPU the calling thread runs on now.
fn cpu() -> usize {
    #[cfg(target_vendor = "apple")]
    {
        unsafe extern "C" { fn pthread_cpu_number_np(cpu: *mut usize) -> i32; }
        let mut n = 0usize;
        // Sound: `n` is writable.
        assert_eq!(unsafe { pthread_cpu_number_np(&mut n) }, 0, "pthread_cpu_number_np");
        n
    }
    #[cfg(not(target_vendor = "apple"))]
    {
        unsafe extern "C" { fn sched_getcpu() -> i32; }
        // Sound: a plain query.
        usize::try_from(unsafe { sched_getcpu() }).expect("sched_getcpu")
    }
}

/// Invalidate the instruction-cache lines of `code`.
fn invalidate_icache(code: &[u8]) {
    #[cfg(target_vendor = "apple")]
    {
        unsafe extern "C" { fn sys_icache_invalidate(start: *mut std::ffi::c_void, len: usize); }
        // Sound: invalidating instruction-cache lines changes no memory.
        unsafe { sys_icache_invalidate(code.as_ptr() as *mut _, code.len()) };
    }
    #[cfg(not(target_vendor = "apple"))]
    {
        unsafe extern "C" { fn __clear_cache(start: *mut std::ffi::c_void, end: *mut std::ffi::c_void); }
        let range = code.as_ptr_range();
        // Sound: cleaning and invalidating cache lines changes no memory.
        unsafe { __clear_cache(range.start as *mut _, range.end as *mut _) };
    }
}

fn read_sweep(work: &[u8]) {
    read_sweep_step(work, 64);
}

fn read_sweep_step(work: &[u8], step: usize) {
    let mut sum = 0u64;
    for &byte in black_box(work).iter().step_by(step) {
        sum = sum.wrapping_add(u64::from(byte));
    }
    black_box(sum);
}

fn child(index: usize) {
    if std::env::var_os("PROBE_QOS").is_some() {
        clocks::set_qos(clocks::USER_INTERACTIVE);
    }
    blake3_servil::initialize();
    let mut work: Vec<u8> = (0..512 * 1024 * 1024usize).map(|i| (i / 64) as u8).collect();
    let source: Vec<u8> = (0..65536usize).map(|i| (i / 8) as u8).collect();
    let mut produced = vec![0u8; 65536];
    let mut devnull = std::fs::OpenOptions::new().write(true).open("/dev/null").unwrap();
    std::fs::write("regular.txt", b"a regular file\n").unwrap();
    let mut held = std::fs::OpenOptions::new().create(true).append(true).open("held.txt").unwrap();
    let spare: Vec<u8> = (0..65536usize).map(|i| (i / 16) as u8).collect();
    let code = text();
    eprintln!("probe: text {:#x}, {} KiB", code.as_ptr() as usize, code.len() / 1024);
    let gap_ns = Cell::new(0u64);
    let mut samples: Vec<Vec<clocks::PreparedBatch>> = (0..CONDITIONS.len() * LENGTHS.len()).map(|_| Vec::new()).collect();
    let mut raw = String::from("process;round;condition;length;calls;started_ns;wall_ns;p_cycles;p_instructions;p_time_ns;e_cycles;e_instructions;e_time_ns;prep_wall_ns;gap_ns\n");
    let n = samples.len();
    let mut calls_raw = String::from("process;round;condition;length;cpu_gap_start;cpu_gap_end;cpu_prepare;wall_ns;cycles\n");
    for round in 0..ROUNDS {
        for k in 0..n {
            let slot = (k + round * 5) % n;
            let (c, len) = (slot / LENGTHS.len(), LENGTHS[slot % LENGTHS.len()]);
            let condition = CONDITIONS[c];
            gap_ns.set(0);
            let before = |_: &mut std::fs::File, _: &mut std::fs::File| {
                if condition.starts_with("open-close") { drop(black_box(std::fs::File::open("/dev/null").unwrap())); }
                if condition.starts_with("icache invalidated") { invalidate_icache(code); }
                if condition.ends_with("10 ms") { clocks::busy_work(10_000_000); }
            };
            let sweep: &dyn Fn(&mut [u8]) = &|w: &mut [u8]| {
                if !condition.ends_with("no sweep") { read_sweep(&w[..128 << 20]); }
                if condition.ends_with("code pages") { read_sweep_step(code, 16384); }
                if condition.ends_with("code lines") { read_sweep_step(code, 64); }
            };
            let warm = condition.ends_with("warm code");
            let prep_cpu = Cell::new(0usize);
            let prepare = |buffer: &mut [u8]| { prep_cpu.set(cpu()); buffer.copy_from_slice(black_box(&source[..len])); };
            let call = |buffer: &[u8]| { black_box(blake3_servil::hash(black_box(buffer))); };
            let work_ref = &mut work;
            let mut m: Option<clocks::PreparedBatch> = None;
            for _ in 0..CALLS {
                let (start_cpu, end_cpu) = (Cell::new(0usize), Cell::new(0usize));
                let one = clocks::measure_after(1, || {
                    start_cpu.set(cpu());
                    before(&mut devnull, &mut held);
                    let started = clocks::now();
                    sweep(work_ref);
                    if warm { black_box(blake3_servil::hash(black_box(&spare[..len]))); }
                    clocks::busy_work(1_000_000u64.saturating_sub(clocks::since_ns(started)));
                    gap_ns.set(gap_ns.get() + clocks::since_ns(started));
                    end_cpu.set(cpu());
                }, &mut produced[..len], &prepare, &call);
                let c1 = one.calls.counts.unwrap_or_default();
                calls_raw += &format!("{index};{round};{condition};{len};{};{};{};{};{}\n", start_cpu.get(), end_cpu.get(), prep_cpu.get(),
                    one.calls.wall_ns, c1.p.cycles + c1.e.cycles);
                m = Some(match m {
                    None => one,
                    Some(sum) => {
                        let add = |a: clocks::Batch, b: clocks::Batch| clocks::Batch { calls: a.calls + b.calls, wall_ns: a.wall_ns + b.wall_ns,
                            counts: a.counts.zip(b.counts).map(|(x, y)| x.plus(y)), started_ns: a.started_ns };
                        clocks::PreparedBatch { calls: add(sum.calls, one.calls), preparation: add(sum.preparation, one.preparation) }
                    }
                });
            }
            let m = m.unwrap();
            let clocks::Counts { p, e } = m.calls.counts.unwrap_or_default();
            raw += &format!("{index};{round};{condition};{len};{};{};{};{};{};{};{};{};{};{};{}\n", m.calls.calls,
                m.calls.started_ns, m.calls.wall_ns, p.cycles, p.instructions, p.time_ns, e.cycles, e.instructions, e.time_ns,
                m.preparation.wall_ns, gap_ns.get());
            samples[slot].push(m);
        }
    }
    std::fs::write(format!("process-{index}.csv"), raw).unwrap();
    std::fs::write(format!("calls-{index}.csv"), calls_raw).unwrap();
    let mut report = format!("process {index}; qos {}; load: {}\n", std::env::var_os("PROBE_QOS").is_some(),
        clocks::load::describe(&clocks::load::windows()));
    for (slot, batches) in samples.iter().enumerate() {
        let (c, len) = (slot / LENGTHS.len(), LENGTHS[slot % LENGTHS.len()]);
        let wall: Vec<u128> = batches.iter().map(|b| clocks::speeds::per_unit(b.calls.wall_ns, b.calls.calls)).collect();
        let cycles = if batches.iter().all(|b| b.calls.counts.is_some_and(|x| x.p.cycles + x.e.cycles > 0)) {
            show(&batches.iter().map(|b| { let x = b.calls.counts.unwrap(); clocks::speeds::per_unit(x.p.cycles + x.e.cycles, b.calls.calls) }).collect::<Vec<_>>())
        } else { "not counted on this platform".into() };
        report += &format!("{len} B, {}: ns/call {}; cycles/call {cycles}\n", CONDITIONS[c], show(&wall));
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
    let built = Command::new("/opt/homebrew/bin/pypy3").arg(root.join("tools/perf_regress.py")).arg("--root").arg(root)
        .args(["build", "--side", "bench", "--commit", FORK_COMMIT]).stderr(Stdio::inherit()).output().expect("build the benchmark");
    assert!(built.status.success(), "the benchmark builds");
    let exe = PathBuf::from(String::from_utf8(built.stdout).expect("a UTF-8 path").trim());
    let me = std::env::current_exe().expect("this probe's executable");
    let bench_run = |name: &str, no_duo: bool| {
        let folder = out.join(name);
        std::fs::create_dir(&folder).expect("a fresh folder");
        let mut command = Command::new(&exe);
        command.current_dir(&folder).args(["--contenders", "blake3-servil-st,sha256-ring",
            "--points", "64 B,4 KiB,16 KiB", "--rounds", "48", "--trace-clocks"]).arg(folder.join("trace.csv"));
        if no_duo { command.env("HB_NO_DUO", "1"); }
        checked(&mut command);
    };
    let probe = |index: usize, qos: bool| {
        let folder = out.join(format!("probe-{index}"));
        std::fs::create_dir(&folder).expect("a fresh folder");
        let mut command = Command::new(&me);
        command.args(["child", &index.to_string()]).current_dir(&folder);
        if qos { command.env("PROBE_QOS", "1"); }
        checked(&mut command);
    };
    probe(0, false);
    bench_run("bench", false);
    probe(1, false);
    bench_run("bench-noduo", true);
    probe(2, true);
}
