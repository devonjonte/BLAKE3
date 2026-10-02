//! b3sum-bench: how long b3sum takes to hash files, from its start to its
//! exit, as the person who runs it waits. Builds of b3sum, and its ways of
//! reading files, side by side; README.md says how to run it and read it.
//!
//! Every clock and count comes from the fork's `clocks` crate: each run
//! through `clocks::child::run`, each cell's summary and every comparison
//! through `clocks::speeds`, other programs' load through `clocks::load`.

use std::collections::BTreeMap;
use std::fs::File;
use std::io::{Read, Write};
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

use clocks::speeds;

/// The samples file's format; a reader accepts this one alone.
const FORMAT: &str = "b3sum-bench samples v1";
/// Where the files' bytes come from: SplitMix64 from this seed, each
/// file's stream seeded by its length and index (README.md).
const SEED: u64 = 0x6233_7375_6d62_656e; // "b3sumben"

const KIB: u64 = 1024;
const MIB: u64 = 1024 * KIB;
const GIB: u64 = 1024 * MIB;

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    match args.first().map(String::as_str) {
        Some("compare") => compare(&args[1..]),
        Some("--help" | "-h") | None => print!("{}", USAGE),
        _ => measure(&args),
    }
}

const USAGE: &str = "\
b3sum-bench: how long b3sum takes to hash files, start to exit

  b3sum-bench [OPTIONS] NAME=COMMAND...
      Measure each COMMAND (a b3sum and its flags, separated by spaces; the
      files are appended) on every input, in rounds, the order rotated.
      Example: b3sum-bench fork=./b3sum fork-read=\"./b3sum --no-mmap\"

      --quick        fewer and smaller inputs, 5 rounds (a check, not a record)
      --rounds N     N rounds (default 15)
      --files DIR    where the input files live (default: b3sum-bench-files);
                     made once and kept; choose the storage you care about
      --out DIR      where the report and samples go (default: b3sum-bench-results)

  b3sum-bench compare OLD.tsv... -- NEW.tsv...
      Compare runs' samples files cell by cell, speed with speed.
";

// ---------- Inputs ----------

/// One input: the files one b3sum run hashes, all its arguments.
struct Input {
    label: String,
    files: Vec<PathBuf>,
    bytes: u64,
}

/// The inputs: single files from a page to a gigabyte (b3sum maps files of
/// 16 KiB and more; the fork's pool takes 1 MiB and more), and a tree of
/// small files, as `b3sum $(find src -type f)` hashes one.
fn inputs(dir: &Path, quick: bool) -> Vec<Input> {
    let sizes: &[u64] = if quick { &[4 * KIB, MIB, 16 * MIB] } else { &[4 * KIB, 64 * KIB, MIB, 16 * MIB, 256 * MIB, GIB] };
    let (tree_files, tree_len) = if quick { (100, 16 * KIB) } else { (1000, 16 * KIB) };
    std::fs::create_dir_all(dir).unwrap_or_else(|e| panic!("cannot make {}: {e}", dir.display()));
    let mut inputs: Vec<Input> = sizes
        .iter()
        .map(|&len| {
            let path = dir.join(format!("file-{len}"));
            ensure_file(&path, len, 0);
            Input { label: size_label(len), files: vec![path], bytes: len }
        })
        .collect();
    let tree = dir.join(format!("tree-{tree_files}x{tree_len}"));
    std::fs::create_dir_all(&tree).unwrap();
    let files: Vec<PathBuf> = (0..tree_files)
        .map(|i| {
            let path = tree.join(format!("{i:04}"));
            ensure_file(&path, tree_len, i + 1);
            path
        })
        .collect();
    inputs.push(Input { label: format!("{tree_files} x {}", size_label(tree_len)), files, bytes: tree_files * tree_len });
    inputs
}

fn size_label(len: u64) -> String {
    match len {
        l if l >= GIB && l % GIB == 0 => format!("{} GiB", l / GIB),
        l if l >= MIB && l % MIB == 0 => format!("{} MiB", l / MIB),
        l if l % KIB == 0 => format!("{} KiB", l / KIB),
        l => format!("{l} B"),
    }
}

/// SplitMix64: the files' bytes, a stream per (length, index).
fn splitmix(state: &mut u64) -> u64 {
    *state = state.wrapping_add(0x9e37_79b9_7f4a_7c15);
    let mut z = *state;
    z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
    z ^ (z >> 31)
}

/// Make `path` hold `len` bytes of its stream, unless it holds them: a file
/// of the right length whose first eight bytes match is kept (the bytes
/// cannot change a hash's speed; regenerating a gigabyte each run would
/// only cost time). Written files are synced, so a later eviction finds
/// them clean.
fn ensure_file(path: &Path, len: u64, index: u64) {
    let mut state = SEED ^ len.rotate_left(17) ^ index;
    let first = splitmix(&mut state.clone()).to_le_bytes();
    if let Ok(mut file) = File::open(path) {
        let mut head = [0u8; 8];
        if file.metadata().map(|m| m.len()).ok() == Some(len) && (len < 8 || (file.read_exact(&mut head).is_ok() && head == first)) {
            return;
        }
    }
    let mut file = File::create(path).unwrap_or_else(|e| panic!("cannot write {}: {e}", path.display()));
    let mut buffer = vec![0u8; MIB as usize];
    let mut left = len;
    while left > 0 {
        let take = left.min(MIB) as usize;
        for word in buffer[..take.next_multiple_of(8)].chunks_exact_mut(8) {
            word.copy_from_slice(&splitmix(&mut state).to_le_bytes());
        }
        file.write_all(&buffer[..take]).unwrap();
        left -= take as u64;
    }
    file.sync_all().unwrap();
}

// ---------- The page cache ----------

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
enum Cache {
    /// The files in the page cache: read moments before.
    Warm,
    /// The files out of the page cache: evicted before each run.
    Cold,
}

impl Cache {
    fn name(self) -> &'static str {
        match self {
            Cache::Warm => "warm",
            Cache::Cold => "cold",
        }
    }
    fn parse(name: &str) -> Cache {
        match name {
            "warm" => Cache::Warm,
            "cold" => Cache::Cold,
            other => panic!("unknown cache state {other:?}"),
        }
    }
    fn heading(self) -> &'static str {
        match self {
            Cache::Warm => "Files in the page cache (warm: read moments before)",
            Cache::Cold => "Files read from storage (cold: evicted from the page cache before each run)",
        }
    }
}

/// Read every file once, untimed, so the page cache holds it.
fn warm(files: &[PathBuf], buffer: &mut [u8]) {
    for path in files {
        let mut file = File::open(path).unwrap();
        while file.read(buffer).unwrap() > 0 {}
    }
}

/// Drop the files' pages from the page cache, without root, where the
/// operating system offers a way: Linux `posix_fadvise(DONTNEED)` (the
/// files are clean, synced when made); macOS `msync(MS_INVALIDATE)` over
/// a mapping of each file. Whether a run then read from storage is in its
/// counts, and the report checks it.
fn evict(files: &[PathBuf]) {
    for path in files {
        imp::evict(&File::open(path).unwrap());
    }
}

#[cfg(all(unix, not(target_vendor = "apple")))]
mod imp {
    use std::os::fd::AsRawFd;

    unsafe extern "C" {
        fn posix_fadvise(fd: i32, offset: i64, len: i64, advice: i32) -> i32;
    }
    const POSIX_FADV_DONTNEED: i32 = 4;

    pub const EVICTS: bool = true;

    pub fn evict(file: &std::fs::File) {
        // Sound: a plain call on an open descriptor.
        let rc = unsafe { posix_fadvise(file.as_raw_fd(), 0, 0, POSIX_FADV_DONTNEED) };
        assert_eq!(rc, 0, "posix_fadvise(DONTNEED)");
    }

    /// The filesystem holding `dir`: the longest mount point above it in
    /// /proc/self/mounts.
    pub fn filesystem(dir: &std::path::Path) -> String {
        let mounts = std::fs::read_to_string("/proc/self/mounts").unwrap_or_default();
        let mut best = (0, "unknown".to_owned());
        for line in mounts.lines() {
            let fields: Vec<&str> = line.split(' ').collect();
            if fields.len() > 2 && dir.starts_with(fields[1]) && fields[1].len() >= best.0 {
                best = (fields[1].len(), format!("{} ({} on {})", fields[2], fields[0], fields[1]));
            }
        }
        best.1
    }
}

#[cfg(target_vendor = "apple")]
mod imp {
    use std::os::fd::AsRawFd;

    unsafe extern "C" {
        fn mmap(addr: *mut u8, len: usize, prot: i32, flags: i32, fd: i32, offset: i64) -> *mut u8;
        fn msync(addr: *mut u8, len: usize, flags: i32) -> i32;
        fn munmap(addr: *mut u8, len: usize) -> i32;
        fn statfs(path: *const i8, buf: *mut u8) -> i32;
    }
    const PROT_READ: i32 = 1;
    const MAP_SHARED: i32 = 1;
    const MS_INVALIDATE: i32 = 2;

    pub const EVICTS: bool = true;

    pub fn evict(file: &std::fs::File) {
        let len = file.metadata().unwrap().len() as usize;
        if len == 0 {
            return;
        }
        // Sound: a fresh read-only shared mapping of an open file, unmapped below.
        unsafe {
            let at = mmap(std::ptr::null_mut(), len, PROT_READ, MAP_SHARED, file.as_raw_fd(), 0);
            assert!(at as isize != -1, "mmap for eviction");
            assert_eq!(msync(at, len, MS_INVALIDATE), 0, "msync(MS_INVALIDATE)");
            assert_eq!(munmap(at, len), 0, "munmap");
        }
    }

    /// The filesystem holding `dir`: statfs's f_fstypename and f_mntonname.
    pub fn filesystem(dir: &std::path::Path) -> String {
        use std::os::unix::ffi::OsStrExt;
        let path = std::ffi::CString::new(dir.as_os_str().as_bytes()).unwrap();
        let mut buf = vec![0u8; 4096];
        // Sound: `buf` is writable and larger than a struct statfs.
        if unsafe { statfs(path.as_ptr(), buf.as_mut_ptr()) } != 0 {
            return "unknown".to_owned();
        }
        // struct statfs (64-bit inodes): f_fstypename at 72 (16 bytes), f_mntonname at 88.
        let text = |bytes: &[u8]| String::from_utf8_lossy(&bytes[..bytes.iter().position(|&b| b == 0).unwrap_or(bytes.len())]).into_owned();
        format!("{} (on {})", text(&buf[72..88]), text(&buf[88..88 + 1024]))
    }
}

#[cfg(not(unix))]
mod imp {
    pub const EVICTS: bool = false;
    pub fn evict(_: &std::fs::File) {
        unreachable!("no eviction here");
    }
    pub fn filesystem(_: &std::path::Path) -> String {
        "unknown".to_owned()
    }
}

/// Whether cold runs can be measured on this filesystem: the platform
/// evicts, and the filesystem keeps files in storage (tmpfs and ramfs keep
/// them in memory alone).
fn cold_possible(filesystem: &str) -> bool {
    imp::EVICTS && !filesystem.starts_with("tmpfs") && !filesystem.starts_with("ramfs")
}

// ---------- Contenders ----------

struct Contender {
    name: String,
    program: PathBuf,
    args: Vec<String>,
    /// The executable's BLAKE3 digest, which names the build exactly.
    digest: String,
    version: String,
}

fn contender(spec: &str) -> Contender {
    let (name, command) = spec.split_once('=').unwrap_or_else(|| panic!("a contender is NAME=COMMAND, found {spec:?}"));
    assert!(!name.is_empty() && !name.contains(['\t', ' ', '|']), "a contender's name has no spaces, tabs, or bars: {name:?}");
    let mut words = command.split_whitespace().map(str::to_owned);
    let program = PathBuf::from(words.next().unwrap_or_else(|| panic!("contender {name} names no program")));
    let program = if program.components().count() > 1 { std::fs::canonicalize(&program).unwrap_or_else(|e| panic!("{}: {e}", program.display())) } else { program };
    let bytes = std::fs::read(&program).or_else(|_| which(&program).map(std::fs::read).expect("the program is in PATH")).unwrap_or_else(|e| panic!("cannot read {}: {e}", program.display()));
    let output = Command::new(&program).arg("--version").output().unwrap_or_else(|e| panic!("cannot run {}: {e}", program.display()));
    Contender {
        name: name.to_owned(),
        program,
        args: words.collect(),
        digest: blake3_servil::hash(&bytes).to_hex().to_string(),
        version: String::from_utf8_lossy(&output.stdout).trim().to_owned(),
    }
}

/// `program` found in PATH, for a bare name.
fn which(program: &Path) -> Option<PathBuf> {
    std::env::split_paths(&std::env::var_os("PATH")?).map(|dir| dir.join(program)).find(|path| path.is_file())
}

// ---------- Samples ----------

/// One run, as the samples file holds it.
#[derive(Clone, Debug)]
struct Sample {
    contender: String,
    cache: Cache,
    input: String,
    bytes: u64,
    round: u64,
    run: clocks::child::Run,
}

fn opt(value: Option<u64>) -> String {
    value.map_or("-".to_owned(), |v| v.to_string())
}

fn sample_line(s: &Sample) -> String {
    let r = &s.run;
    let c = r.counts;
    let level = |f: fn(&clocks::Counts) -> u64| opt(c.as_ref().map(f));
    [
        s.contender.clone(), s.cache.name().to_owned(), s.input.clone(), s.bytes.to_string(), s.round.to_string(),
        r.started_ns.to_string(), r.wall_ns.to_string(), opt(r.cpu_ns), opt(r.max_rss_bytes), opt(r.storage_read_bytes), opt(r.major_faults),
        level(|c| c.p.cycles), level(|c| c.e.cycles), level(|c| c.p.instructions), level(|c| c.e.instructions), level(|c| c.p.time_ns), level(|c| c.e.time_ns),
    ]
    .join("\t")
}

const COLUMNS: &str = "contender\tcache\tinput\tbytes\tround\tstarted_ns\twall_ns\tcpu_ns\tmax_rss_bytes\tstorage_read_bytes\tmajor_faults\tp_cycles\te_cycles\tp_instructions\te_instructions\tp_time_ns\te_time_ns";

/// A samples file read back: its samples, its header lines, and whether
/// its load windows include a busy one.
struct Run {
    samples: Vec<Sample>,
    busy: bool,
}

fn read_samples(path: &str) -> Run {
    let text = std::fs::read_to_string(path).unwrap_or_else(|e| panic!("cannot read {path}: {e}"));
    let mut lines = text.lines();
    assert_eq!(lines.next(), Some(&*format!("# {FORMAT}")), "{path}: not a {FORMAT} file (read older formats with the tools of the commit that wrote them)");
    let mut samples = Vec::new();
    let mut busy = false;
    for line in lines {
        if let Some(window) = line.strip_prefix("# load\t") {
            let fields: Vec<u64> = window.split('\t').map(|f| f.parse().unwrap()).collect();
            busy |= fields[2] >= clocks::load::BUSY_MILLI_CPUS || fields[3] >= clocks::load::BUSY_MILLI_CPUS;
            continue;
        }
        if line.starts_with('#') || line == COLUMNS {
            continue;
        }
        let f: Vec<&str> = line.split('\t').collect();
        assert_eq!(f.len(), 17, "{path}: a sample line has 17 fields: {line}");
        let n = |i: usize| -> Option<u64> { (f[i] != "-").then(|| f[i].parse().unwrap()) };
        let counts = n(11).map(|_| clocks::Counts {
            p: clocks::Level { cycles: n(11).unwrap(), instructions: n(13).unwrap(), time_ns: n(15).unwrap() },
            e: clocks::Level { cycles: n(12).unwrap(), instructions: n(14).unwrap(), time_ns: n(16).unwrap() },
        });
        samples.push(Sample {
            contender: f[0].to_owned(),
            cache: Cache::parse(f[1]),
            input: f[2].to_owned(),
            bytes: n(3).unwrap(),
            round: n(4).unwrap(),
            run: clocks::child::Run {
                started_ns: n(5).unwrap(),
                wall_ns: n(6).unwrap(),
                success: true,
                cpu_ns: n(7),
                max_rss_bytes: n(8),
                storage_read_bytes: n(9),
                major_faults: n(10),
                counts,
            },
        });
    }
    Run { samples, busy }
}

// ---------- Measuring ----------

fn measure(args: &[String]) {
    let mut quick = false;
    let mut rounds = None;
    let mut files_dir = PathBuf::from("b3sum-bench-files");
    let mut out_dir = PathBuf::from("b3sum-bench-results");
    let mut specs = Vec::new();
    let mut it = args.iter();
    while let Some(arg) = it.next() {
        match arg.as_str() {
            "--quick" => quick = true,
            "--rounds" => rounds = Some(it.next().expect("--rounds N").parse::<u64>().expect("--rounds takes a whole number")),
            "--files" => files_dir = PathBuf::from(it.next().expect("--files DIR")),
            "--out" => out_dir = PathBuf::from(it.next().expect("--out DIR")),
            flag if flag.starts_with("--") => panic!("unknown option {flag}; see --help"),
            spec => specs.push(contender(spec)),
        }
    }
    assert!(!specs.is_empty(), "name at least one contender, NAME=COMMAND; see --help");
    let mut names: Vec<&str> = specs.iter().map(|c| c.name.as_str()).collect();
    names.sort_unstable();
    names.dedup();
    assert_eq!(names.len(), specs.len(), "each contender has a name of its own");
    let rounds = rounds.unwrap_or(if quick { 5 } else { 15 });
    assert!(rounds > 0, "at least one round");

    eprintln!("b3sum-bench: making the input files in {} (kept for later runs)", files_dir.display());
    let inputs = inputs(&files_dir, quick);
    let files_dir = std::fs::canonicalize(&files_dir).unwrap();
    let filesystem = imp::filesystem(&files_dir);
    let caches: Vec<Cache> = if cold_possible(&filesystem) { vec![Cache::Warm, Cache::Cold] } else { vec![Cache::Warm] };
    let machine = machine();

    let mut buffer = vec![0u8; MIB as usize];
    let run_once = |c: &Contender, input: &Input| -> clocks::child::Run {
        let mut command = Command::new(&c.program);
        command.args(&c.args).args(&input.files).stdin(Stdio::null()).stdout(Stdio::null()).stderr(Stdio::null());
        let run = clocks::child::run(&mut command);
        if !run.success {
            // Show what it said, then stop: a failing contender measures nothing.
            let _ = Command::new(&c.program).args(&c.args).args(&input.files).stdout(Stdio::null()).status();
            panic!("contender {} failed on {}", c.name, input.label);
        }
        run
    };

    // Warm-up: every contender once on every input, untimed, so the
    // executables and the files start in the page cache.
    for input in &inputs {
        warm(&input.files, &mut buffer);
        for c in &specs {
            run_once(c, input);
        }
    }
    let mut samples = Vec::new();
    let started = clocks::now();
    for round in 0..rounds {
        for &cache in &caches {
            for (i, input) in inputs.iter().enumerate() {
                if cache == Cache::Warm {
                    warm(&input.files, &mut buffer);
                }
                // The order rotates with the round and the input, so drift
                // and each run's after-effects fall on every contender.
                for k in 0..specs.len() {
                    let c = &specs[(k + round as usize + i) % specs.len()];
                    if cache == Cache::Cold {
                        evict(&input.files);
                    }
                    let run = run_once(c, input);
                    samples.push(Sample { contender: c.name.clone(), cache, input: input.label.clone(), bytes: input.bytes, round, run });
                }
            }
        }
        eprintln!("b3sum-bench: round {} of {rounds} done, {} s", round + 1, clocks::since_ns(started) / 1_000_000_000);
    }
    let windows = clocks::load::windows();

    std::fs::create_dir_all(&out_dir).unwrap();
    let mut tsv = format!("# {FORMAT}\n# machine\t{machine}\n# files\t{}\t{filesystem}\n# rounds\t{rounds}\n", files_dir.display());
    for c in &specs {
        tsv += &format!("# contender\t{}\t{} {}\tblake3 {}\t{}\n", c.name, c.program.display(), c.args.join(" "), c.digest, c.version);
    }
    for w in &windows {
        tsv += &format!("# load\t{}\t{}\t{}\t{}\n", w.start_ns, w.end_ns, w.other_milli_cpus, w.steal_milli_cpus);
    }
    tsv += COLUMNS;
    tsv += "\n";
    for s in &samples {
        tsv += &sample_line(s);
        tsv += "\n";
    }
    std::fs::write(out_dir.join("b3sum-bench.samples.tsv"), tsv).unwrap();

    let report = report(&specs, &inputs, &caches, &samples, &machine, &filesystem, &windows, quick, rounds);
    std::fs::write(out_dir.join("b3sum-bench.report.txt"), &report).unwrap();
    print!("{report}");
    eprintln!("b3sum-bench: report and samples in {}", out_dir.display());
}

/// One line about the machine: CPU, CPU count, memory, OS.
fn machine() -> String {
    let command = |program: &str, args: &[&str]| -> String {
        Command::new(program).args(args).output().ok().map(|o| String::from_utf8_lossy(&o.stdout).trim().to_owned()).unwrap_or_default()
    };
    let cpus = std::thread::available_parallelism().map_or(0, |n| n.get());
    let (cpu, memory, os) = if cfg!(target_vendor = "apple") {
        let bytes: u64 = command("sysctl", &["-n", "hw.memsize"]).parse().unwrap_or(0);
        (command("sysctl", &["-n", "machdep.cpu.brand_string"]), bytes, format!("macOS {}", command("sw_vers", &["-productVersion"])))
    } else if cfg!(target_os = "linux") {
        let info = std::fs::read_to_string("/proc/cpuinfo").unwrap_or_default();
        let cpu = info.lines().find(|l| l.starts_with("model name")).and_then(|l| l.split(':').nth(1)).map(|s| s.trim().to_owned()).unwrap_or_else(|| std::env::consts::ARCH.to_owned());
        let mem = std::fs::read_to_string("/proc/meminfo").unwrap_or_default();
        let kib: u64 = mem.lines().next().and_then(|l| l.split_whitespace().nth(1)).and_then(|v| v.parse().ok()).unwrap_or(0);
        (cpu, kib * 1024, format!("Linux {}", std::fs::read_to_string("/proc/sys/kernel/osrelease").unwrap_or_default().trim()))
    } else {
        (std::env::consts::ARCH.to_owned(), 0, std::env::consts::OS.to_owned())
    };
    format!("{cpu}, {cpus} CPUs, {} GiB, {os}", (memory + GIB / 2) / GIB)
}

// ---------- Summaries ----------

/// A cell's wall times as ns per input byte (Q64.64), sorted.
fn per_byte(samples: &[&Sample]) -> Vec<u128> {
    let mut v: Vec<u128> = samples.iter().map(|s| speeds::per_unit(s.run.wall_ns, s.bytes)).collect();
    v.sort_unstable();
    v
}

/// A per-byte value back as nanoseconds for `bytes` bytes, rounded.
fn ns_for(per_byte: u128, bytes: u64) -> u128 {
    (per_byte * u128::from(bytes) + (1 << 63)) >> 64
}

/// `value` over `scale` with three significant digits: (digits, decimals).
fn sig3(value: u128, scale: u128) -> String {
    let mut decimals = 0u32;
    while decimals < 6 && value * 10u128.pow(decimals) < 100 * scale {
        decimals += 1;
    }
    let scaled = (value * 10u128.pow(decimals) + scale / 2) / scale;
    let p = 10u128.pow(decimals);
    if decimals == 0 { scaled.to_string() } else { format!("{}.{:0w$}", scaled / p, scaled % p, w = decimals as usize) }
}

/// Nanoseconds for people: "812 µs", "1.23 ms", "2.05 s".
fn time(ns: u128) -> String {
    match ns {
        n if n < 1_000 => format!("{n} ns"),
        n if n < 1_000_000 => format!("{} µs", sig3(n, 1_000)),
        n if n < 1_000_000_000 => format!("{} ms", sig3(n, 1_000_000)),
        n => format!("{} s", sig3(n, 1_000_000_000)),
    }
}

/// Bytes over nanoseconds as GB/s, three significant digits.
fn rate(bytes: u64, ns: u128) -> String {
    format!("{} GB/s", sig3(u128::from(bytes), ns.max(1)))
}

fn median_u64(mut v: Vec<u64>) -> Option<u64> {
    if v.is_empty() {
        return None;
    }
    v.sort_unstable();
    let n = v.len();
    Some(if n % 2 == 1 { v[n / 2] } else { (v[n / 2 - 1] + v[n / 2]).div_ceil(2) })
}

/// A cell's time per run: one speed, or two with their shares.
fn cell_time(sorted: &[u128], bytes: u64) -> String {
    let found = speeds::speeds(sorted);
    let one = |s: &speeds::Speed| {
        let ns = ns_for(s.median, bytes);
        if bytes >= MIB { format!("{} {}", time(ns), rate(bytes, ns)) } else { time(ns) }
    };
    match found.as_slice() {
        [only] => one(only),
        [fast, slow] => {
            let total = fast.count + slow.count;
            format!("{} {}% | {} {}%", one(fast), (fast.count * 100 + total / 2) / total, one(slow), (slow.count * 100 + total / 2) / total)
        }
        _ => unreachable!("one or two speeds"),
    }
}

/// Permille as "x0.42" (three significant digits at most).
fn times(permille: u64) -> String {
    format!("x{}", sig3(u128::from(permille), 1000))
}

#[allow(clippy::too_many_arguments)]
fn report(
    specs: &[Contender],
    inputs: &[Input],
    caches: &[Cache],
    samples: &[Sample],
    machine: &str,
    filesystem: &str,
    windows: &[clocks::load::Window],
    quick: bool,
    rounds: u64,
) -> String {
    let mut out = String::new();
    out += "b3sum-bench: how long b3sum takes to hash files, from its start to its exit\n\n";
    out += &format!("machine:   {machine}\nfiles on:  {filesystem}\n");
    out += &format!("load:      {}\n", clocks::load::describe(windows));
    let counted = samples.iter().any(|s| s.run.counts.is_some());
    out += &format!("cycles:    {}\n", if counted { "counted per core kind (in the samples file)" } else { "not counted on this platform (wall and CPU time only)" });
    out += &format!("runs:      {rounds} of each contender on each input{}\n", if quick { " (--quick: a check, not a record)" } else { "" });
    if !caches.contains(&Cache::Cold) {
        out += "cold:      not measured: this platform or filesystem cannot evict one file from the page cache\n";
    }
    out += "\ncontenders:\n";
    for c in specs {
        out += &format!("  {:<14} {} {}   ({}, blake3 {})\n", c.name, c.program.display(), c.args.join(" "), c.version, &c.digest[..16]);
    }
    let cell = |c: &str, cache: Cache, input: &str| -> Vec<&Sample> {
        samples.iter().filter(|s| s.contender == c && s.cache == cache && s.input == input).collect()
    };
    let base = &specs[0].name;
    for &cache in caches {
        out += &format!("\n{}\ntime per run, lower is better; xN: time against {base}'s\n", cache.heading());
        let mut rows: Vec<Vec<String>> = vec![std::iter::once("input".to_owned()).chain(specs.iter().map(|c| c.name.clone())).collect()];
        for input in inputs {
            let base_sorted = per_byte(&cell(base, cache, &input.label));
            let mut row = vec![input.label.clone()];
            for c in specs {
                let sorted = per_byte(&cell(&c.name, cache, &input.label));
                let mut text = cell_time(&sorted, input.bytes);
                if &c.name != base {
                    text += &format!(" {}", times(speeds::compare(&base_sorted, &sorted).fast_permille));
                }
                row.push(text);
            }
            rows.push(row);
        }
        out += &table(&rows);
        // What each run cost the machine: CPUs kept busy and memory.
        out += "\nCPUs busy (CPU time over wall time) and peak memory, medians\n";
        let mut rows: Vec<Vec<String>> = vec![std::iter::once("input".to_owned()).chain(specs.iter().map(|c| c.name.clone())).collect()];
        for input in inputs {
            let mut row = vec![input.label.clone()];
            for c in specs {
                let runs = cell(&c.name, cache, &input.label);
                let busy = median_u64(runs.iter().filter_map(|s| s.run.cpu_ns.map(|cpu| (cpu * 100 + s.run.wall_ns / 2) / s.run.wall_ns)).collect());
                let rss = median_u64(runs.iter().filter_map(|s| s.run.max_rss_bytes).collect());
                row.push(match (busy, rss) {
                    (Some(b), Some(m)) => format!("{}.{:02} CPUs, {} MiB", b / 100, b % 100, (m + MIB / 2) / MIB),
                    _ => "not counted here".to_owned(),
                });
            }
            rows.push(row);
        }
        out += &table(&rows);
        if cache == Cache::Cold {
            // Generated from the counts: each cold cell's reads from storage.
            let mut warm_cells = Vec::new();
            for input in inputs {
                for c in specs {
                    let read = median_u64(cell(&c.name, cache, &input.label).iter().filter_map(|s| s.run.storage_read_bytes).collect());
                    if let Some(read) = read {
                        if read * 2 < input.bytes {
                            warm_cells.push(format!("{} on {} read {} of {} from storage", c.name, input.label, size_label_approx(read), size_label(input.bytes)));
                        }
                    }
                }
            }
            if warm_cells.is_empty() {
                out += "\nEvery cold run read its files from storage (by the counts).\n";
            } else {
                out += &format!("\nNot cold: the page cache still served these runs (median reads): {}.\n", warm_cells.join("; "));
            }
        }
    }
    out
}

fn size_label_approx(bytes: u64) -> String {
    if bytes >= MIB { format!("{} MiB", (bytes + MIB / 2) / MIB) } else { format!("{} KiB", (bytes + KIB / 2) / KIB) }
}

/// Columns padded to their widest cell.
fn table(rows: &[Vec<String>]) -> String {
    let widths: Vec<usize> = (0..rows[0].len()).map(|i| rows.iter().map(|r| r[i].chars().count()).max().unwrap()).collect();
    let mut out = String::new();
    for row in rows {
        let cells: Vec<String> = row.iter().zip(&widths).map(|(cell, &w)| format!("{cell}{}", " ".repeat(w - cell.chars().count()))).collect();
        out += cells.join("   ").trim_end();
        out += "\n";
    }
    out
}

// ---------- Comparing runs ----------

fn compare(args: &[String]) {
    let split = args.iter().position(|a| a == "--").expect("compare OLD.tsv... -- NEW.tsv...");
    let (old, new) = (&args[..split], &args[split + 1..]);
    assert!(!old.is_empty() && !new.is_empty(), "compare OLD.tsv... -- NEW.tsv...");
    let side = |paths: &[String]| -> (BTreeMap<(String, Cache, String), (u64, Vec<u128>)>, bool) {
        let mut cells: BTreeMap<(String, Cache, String), (u64, Vec<u128>)> = BTreeMap::new();
        let mut busy = false;
        for path in paths {
            let run = read_samples(path);
            busy |= run.busy;
            for s in run.samples {
                let entry = cells.entry((s.contender.clone(), s.cache, s.input.clone())).or_insert((s.bytes, Vec::new()));
                entry.1.push(speeds::per_unit(s.run.wall_ns, s.bytes));
            }
        }
        for (_, v) in cells.values_mut() {
            v.sort_unstable();
        }
        (cells, busy)
    };
    let ((old, old_busy), (new, new_busy)) = (side(old), side(new));
    if old_busy || new_busy {
        println!("busy: other programs kept a CPU or more busy during a run on the {} side; these numbers are no evidence of speed", if old_busy { "old" } else { "new" });
    }
    for (key, (bytes, old_sorted)) in &old {
        let Some((_, new_sorted)) = new.get(key) else { continue };
        let c = speeds::compare(old_sorted, new_sorted);
        let side_text = |list: &[speeds::Speed]| -> String {
            let total: usize = list.iter().map(|s| s.count).sum();
            list.iter().map(|s| if list.len() > 1 { format!("{} ({}%)", time(ns_for(s.median, *bytes)), (s.count * 100 + total / 2) / total) } else { time(ns_for(s.median, *bytes)) }).collect::<Vec<_>>().join(" | ")
        };
        println!(
            "{}|{}|{}: {} -> {}  [fast {}, slow {}, slow share {}% -> {}%]",
            key.0, key.1.name(), key.2, side_text(&c.old), side_text(&c.new), times(c.fast_permille), times(c.slow_permille),
            (c.old_slow_share_permille + 5) / 10, (c.new_slow_share_permille + 5) / 10
        );
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn people_read_three_digits() {
        assert_eq!(time(812), "812 ns");
        assert_eq!(time(1_234_567), "1.23 ms");
        assert_eq!(time(45_600), "45.6 µs");
        assert_eq!(time(2_050_000_000), "2.05 s");
        assert_eq!(rate(GIB, 100_000_000), "10.7 GB/s");
        assert_eq!(times(420), "x0.420");
        assert_eq!(times(1500), "x1.50");
    }

    /// The files' bytes come from SplitMix64: its published first outputs
    /// from state 0 (Vigna's splitmix64.c), so the recipe in README.md
    /// reproduces them anywhere.
    #[test]
    fn the_generator_is_splitmix64() {
        let mut state = 0;
        let first: Vec<u64> = (0..3).map(|_| splitmix(&mut state)).collect();
        assert_eq!(first, [0xe220_a839_7b1d_cdaf, 0x6e78_9e6a_a1b9_65f4, 0x06c4_5d18_8009_454f]);
    }

    #[test]
    fn a_samples_line_reads_back() {
        let s = Sample {
            contender: "a".into(),
            cache: Cache::Cold,
            input: "1 MiB".into(),
            bytes: MIB,
            round: 3,
            run: clocks::child::Run { started_ns: 5, wall_ns: 9, success: true, cpu_ns: Some(7), max_rss_bytes: None, storage_read_bytes: Some(4), major_faults: Some(1), counts: None },
        };
        let dir = std::env::temp_dir().join(format!("b3sum-bench-test-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let path = dir.join("s.tsv");
        std::fs::write(&path, format!("# {FORMAT}\n# load\t0\t1\t5\t0\n{COLUMNS}\n{}\n", sample_line(&s))).unwrap();
        let back = read_samples(path.to_str().unwrap());
        assert!(!back.busy);
        assert_eq!(sample_line(&back.samples[0]), sample_line(&s));
        std::fs::remove_dir_all(dir).unwrap();
    }
}
