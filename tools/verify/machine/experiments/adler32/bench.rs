//! Native, seed-one Adler-32 comparisons. All engines use the same indirect
//! two-argument adapter boundary, return u32, and consume each result.
//! Shared clocks owns timing, load and comparison; no timing is done by tests.
use std::{collections::BTreeMap, hint::black_box, os::raw::c_ulong};

unsafe extern "C" {
    fn b3l_adler32(input: *const u8, n: u64) -> u64;
    fn adler32_z(seed: c_ulong, input: *const u8, n: usize) -> c_ulong;
    fn zng_adler32_z(seed: u32, input: *const u8, n: usize) -> u32;
    fn libdeflate_adler32(seed: u32, input: *const u8, n: usize) -> u32;
}
type Engine = unsafe fn(*const u8, usize) -> u32;
#[inline(never)]
unsafe fn ode(p: *const u8, n: usize) -> u32 {
    b3l_adler32(p, n as u64) as u32
}
#[inline(never)]
unsafe fn zlib(p: *const u8, n: usize) -> u32 {
    adler32_z(1, p, n) as u32
}
#[inline(never)]
unsafe fn zlib_ng(p: *const u8, n: usize) -> u32 {
    zng_adler32_z(1, p, n)
}
#[inline(never)]
unsafe fn libdeflate(p: *const u8, n: usize) -> u32 {
    libdeflate_adler32(1, p, n)
}
#[cfg(feature = "probe")]
mod probes {
    unsafe extern "C" {
        fn isal_adler32(seed: u32, input: *const u8, n: u64) -> u32;
        fn probe512(p: *const u8, n: usize) -> u32;
        fn probe512_one(p: *const u8, n: usize) -> u32;
        fn probe256(p: *const u8, n: usize) -> u32;
        fn probe256_one(p: *const u8, n: usize) -> u32;
    }
    #[inline(never)]
    pub unsafe fn isal(p: *const u8, n: usize) -> u32 {
        isal_adler32(1, p, n as u64)
    }
    #[inline(never)]
    pub unsafe fn wide512(p: *const u8, n: usize) -> u32 {
        probe512(p, n)
    }
    #[inline(never)]
    pub unsafe fn wide512_one(p: *const u8, n: usize) -> u32 {
        probe512_one(p, n)
    }
    #[inline(never)]
    pub unsafe fn wide256(p: *const u8, n: usize) -> u32 {
        probe256(p, n)
    }
    #[inline(never)]
    pub unsafe fn wide256_one(p: *const u8, n: usize) -> u32 {
        probe256_one(p, n)
    }
}
const ENGINES: &[(&str, Engine)] = &[
    ("ode", ode),
    ("zlib", zlib),
    ("zlib-ng", zlib_ng),
    ("libdeflate", libdeflate),
    #[cfg(feature = "probe")]
    ("isa-l", probes::isal),
    #[cfg(feature = "probe")]
    ("probe512", probes::wide512),
    #[cfg(feature = "probe")]
    ("probe512-one", probes::wide512_one),
    #[cfg(feature = "probe")]
    ("probe256", probes::wide256),
    #[cfg(feature = "probe")]
    ("probe256-one", probes::wide256_one),
];
const FORMAT: &str = "# ode-adler-samples-v3";
const LENGTHS: [usize; 10] = [0, 1, 16, 64, 256, 1024, 4096, 5552, 65536, 1048576];
const EXPECTED_TEXT: &[u8] = include_bytes!(concat!(env!("CARGO_MANIFEST_DIR"), "/text.bin"));

fn cells(probe: bool) -> Vec<(u8, usize, usize)> {
    (0..4)
        .flat_map(|p| LENGTHS.into_iter().flat_map(move |n| [0, 1].map(|o| (p, n, o))))
        .filter(|&(p, n, _)| !probe || (p == 3 && ![1024, 5552].contains(&n)))
        .collect()
}

fn engine(name: &str) -> Engine {
    ENGINES.iter().find(|e| e.0 == name).expect("declared engine").1
}
fn checksum(f: Engine, input: &[u8]) -> u32 {
    // Caller provides a readable slice. The proved Ode body and the three
    // libraries all start at Adler state 1; no null-buffer reset shortcut.
    unsafe { f(input.as_ptr(), input.len()) }
}

fn validate() {
    #[cfg(feature = "probe")]
    assert!(
        std::is_x86_feature_detected!("avx512bw")
            && std::is_x86_feature_detected!("avx512vl")
            && std::is_x86_feature_detected!("avx512vnni")
            && std::is_x86_feature_detected!("avx512dq"),
        "unverified probes require AVX-512 BW/VL/VNNI/DQ (or an explicitly configured emulator)"
    );
    let actual = unsafe { std::slice::from_raw_parts(b3l_adler32 as *const u8, EXPECTED_TEXT.len()) };
    assert_eq!(actual, EXPECTED_TEXT, "linked Ode function differs from the proved observed bytes");
    for &(name, f) in ENGINES {
        for (input, want) in [(b"".as_slice(), 1), (b"a".as_slice(), 0x00620062), (b"Wikipedia".as_slice(), 0x11e60398), (b"123456789".as_slice(), 0x091e01de)]
        {
            assert_eq!(checksum(f, input), want, "{name}");
        }
        for n in [
            0, 1, 2, 16, 31, 32, 63, 64, 127, 128, 255, 256, 257, 1024, 4096, 5551, 5552, 5553, 16383, 16384, 16385, 32768, 65520, 65521, 65522, 65536, 1048576,
        ] {
            for pattern in 0..4 {
                for offset in [0, 1] {
                    let (storage, start) = input(pattern, n, offset);
                    let bytes = &storage[start..start + n];
                    assert_eq!(checksum(f, bytes), reference(bytes), "{name}, pattern {pattern}, length {n}, offset {offset}");
                }
            }
        }
    }
    guard_pages(ENGINES);
}

fn guard_pages(engines: &[(&str, Engine)]) {
    unsafe extern "C" {
        fn mmap(p: *mut u8, n: usize, prot: i32, flags: i32, fd: i32, off: i64) -> *mut u8;
        fn mprotect(p: *mut u8, n: usize, prot: i32) -> i32;
        fn munmap(p: *mut u8, n: usize) -> i32;
        fn sysconf(name: i32) -> i64;
    }
    // Linux's anonymous mapping, with read-only input against both guard edges.
    // Borrowed slices live only while their pages are readable.
    unsafe {
        let page = sysconf(30) as usize;
        assert!(page.is_power_of_two());
        for n in [0, 1, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256, 257, 4095, 4096, 4097, 16383, 16384, 16385] {
            let span = (n / page + 1) * page;
            let total = span + 2 * page;
            let map = mmap(std::ptr::null_mut(), total, 0, 0x22, -1, 0);
            assert_ne!(map as usize, usize::MAX);
            let data = map.add(page);
            for edge in [0, span - n] {
                let p = data.add(edge);
                for pattern in 0..4 {
                    assert_eq!(mprotect(data, span, 3), 0);
                    let (storage, start) = input(pattern, n, 0);
                    std::ptr::copy_nonoverlapping(storage.as_ptr().add(start), p, n);
                    let want = reference(&storage[start..start + n]);
                    assert_eq!(mprotect(data, span, 1), 0);
                    for &(name, f) in engines {
                        assert_eq!(f(p, n), want, "guard: {name}, {n} bytes, edge {edge}, pattern {pattern}");
                    }
                }
            }
            assert_eq!(munmap(map, total), 0);
        }
    }
}

unsafe fn deliberate_overread(p: *const u8, n: usize) -> u32 {
    std::ptr::read_volatile(p.add(n));
    1
}

fn reference(input: &[u8]) -> u32 {
    let (mut a, mut b) = (1u64, 0u64);
    for byte in input {
        a = (a + u64::from(*byte)) % 65521;
        b = (b + a) % 65521;
    }
    ((b << 16) | a) as u32
}

fn input(pattern: u8, n: usize, offset: usize) -> (Vec<u8>, usize) {
    assert!(pattern < 4 && offset < 2);
    let mut v = vec![0; n + 64];
    let start = (64 - v.as_ptr() as usize % 64) % 64 + offset;
    let mut random = 0x8d12_e371_5a26_4bc9u64;
    for (i, b) in v[start..start + n].iter_mut().enumerate() {
        random ^= random << 13;
        random ^= random >> 7;
        random ^= random << 17;
        *b = match pattern {
            0 => 0,
            1 => 255,
            2 => i as u8,
            3 => random as u8,
            _ => unreachable!(),
        };
    }
    (v, start)
}

// A debugger can stop here after dispatch is initialized, outside measurement.
#[no_mangle]
#[inline(never)]
pub extern "C" fn adler_validation_done() {
    black_box(0u8);
}

fn collect(name: &str, probe: bool) -> i32 {
    validate();
    let f = black_box(engine(name));
    clocks::load::quiet_for(3).expect("collect needs a quiet measurement machine");
    println!("{FORMAT}\n# engine: {name}\n# workload: {}", if probe { "probe" } else { "full" });
    if name.starts_with("probe") {
        println!("# engine proof: UNVERIFIED native C algorithm probe, not an Ode implementation");
    }
    println!("# scope: warmed seed-one native calls; indirect adapter boundary; includes result consumption; buffers 64-byte aligned or offset by 1");
    println!("# Ode address: {:p}; padding: {}", b3l_adler32 as *const (), env!("ODE_PADDING"));
    for &(n, f) in ENGINES {
        println!("# adapter: {n} {:p}", f as *const ());
    }
    println!("# rustc: {}\n# clocks: bench-hashes 5f99f456951ab36f7201decd8aa5e0249ec67bd1; {}", env!("ODE_RUSTC"), clocks::WALL_CLOCK);
    println!("# report: {}", include_str!(concat!(env!("CARGO_MANIFEST_DIR"), "/report.json")).replace('\n', " "));
    println!("pattern\tbytes\toffset\tsample\tcalls\twall_ns\tcpu_ns\tp_cycles\tp_instructions\tp_time_ns\te_cycles\te_instructions\te_time_ns\tstarted_ns");
    let mut all = vec![];
    for (pattern, len, offset) in cells(probe) {
        let (storage, start) = input(pattern, len, offset);
        let input = &storage[start..start + len];
        assert_eq!(input.as_ptr() as usize % 64, offset);
        let samples = clocks::measure(12, if probe { 10_000_000 } else { 5_000_000 }, || {
            black_box(checksum(f, black_box(input)));
        });
        let mean = clocks::summary::mean(samples.iter().map(|s| (s.wall_ns, s.calls)));
        eprintln!("{name}, pattern {pattern}, {len} bytes, offset {offset}: {} ns/call (run mean)", decimal(mean));
        for (i, s) in samples.into_iter().enumerate() {
            let c = s
                .counts
                .map(|c| format!("{}\t{}\t{}\t{}\t{}\t{}", c.p.cycles, c.p.instructions, c.p.time_ns, c.e.cycles, c.e.instructions, c.e.time_ns))
                .unwrap_or_else(|| "-\t-\t-\t-\t-\t-".into());
            println!(
                "{pattern}\t{len}\t{offset}\t{i}\t{}\t{}\t{}\t{c}\t{}",
                s.calls,
                s.wall_ns,
                s.cpu_ns.map_or_else(|| "-".into(), |n| n.to_string()),
                s.started_ns
            );
            all.push(s);
        }
    }
    let windows = clocks::load::windows();
    for w in &windows {
        println!("# window\t{}\t{}\t{}\t{}", w.start_ns, w.end_ns, w.other_milli_cpus, w.steal_milli_cpus);
    }
    let quiet = clocks::load::MEASURED && !windows.is_empty() && windows.iter().all(|w| !w.busy());
    println!("# load: {}", clocks::load::describe(&windows));
    println!("# counts: {}", if all.iter().all(|s| s.counts.is_some()) { "available" } else { "absent for some or all samples; no complete cycle evidence" });
    println!("# accepted: {}", if quiet { "quiet" } else { "busy-or-unobserved" });
    if quiet {
        0
    } else {
        2
    }
}

type Cell = (u8, usize, usize);
fn read(path: &str) -> (String, BTreeMap<Cell, u128>) {
    read_text(&std::fs::read_to_string(path).expect("samples exist"))
}
fn read_text(text: &str) -> (String, BTreeMap<Cell, u128>) {
    assert_eq!(text.lines().next(), Some(FORMAT), "samples format");
    assert!(text.lines().any(|l| l == "# accepted: quiet"), "comparison abstains on busy or unobserved load");
    let names: Vec<_> = text.lines().filter_map(|l| l.strip_prefix("# engine: ")).collect();
    assert_eq!(names.len(), 1);
    engine(names[0]);
    let mut cells: BTreeMap<Cell, Vec<(u64, u64)>> = BTreeMap::new();
    for l in text.lines().filter(|l| !l.starts_with('#') && !l.starts_with("pattern") && !l.is_empty()) {
        let p: Vec<_> = l.split('\t').collect();
        assert_eq!(p.len(), 14);
        let key = (p[0].parse().unwrap(), p[1].parse().unwrap(), p[2].parse().unwrap());
        let sample: usize = p[3].parse().unwrap();
        let v = cells.entry(key).or_default();
        assert_eq!(sample, v.len(), "samples appear once in order");
        v.push((p[5].parse().unwrap(), p[4].parse().unwrap()));
    }
    let modes: Vec<_> = text.lines().filter_map(|l| l.strip_prefix("# workload: ")).collect();
    assert_eq!(modes.len(), 1, "one declared workload");
    let probe = match modes[0] {
        "full" => false,
        "probe" => true,
        _ => panic!("declared workload"),
    };
    assert!(cells.keys().copied().eq(self::cells(probe)), "exactly the declared workload cells");
    (
        names[0].into(),
        cells
            .into_iter()
            .map(|(k, v)| {
                assert_eq!(v.len(), 12);
                (k, clocks::summary::mean(v))
            })
            .collect(),
    )
}

fn hundredths(v: u128) -> String {
    format!("{}.{:02}", v / 100, v % 100)
}
fn decimal(value: u128) -> String {
    hundredths((value * 100 + (1u128 << 63)) >> 64)
}
fn gbps(bytes: usize, time: u128) -> String {
    if bytes == 0 {
        "-".into()
    } else {
        hundredths((((bytes as u128 * 100) << 64) + time / 2) / time)
    }
}
fn median(v: &mut [u128]) -> u128 {
    v.sort_unstable();
    let n = v.len();
    if n % 2 == 1 {
        v[n / 2]
    } else {
        v[n / 2 - 1] + (v[n / 2] - v[n / 2 - 1]) / 2
    }
}
fn compare(paths: &[String]) {
    assert!(paths.len() >= 6 && paths.len() % 2 == 0, "at least three corresponding OLD NEW pairs");
    let mut pairs: BTreeMap<Cell, Vec<(u128, u128)>> = BTreeMap::new();
    let mut names = None;
    for p in paths.chunks_exact(2) {
        let (old_name, old) = read(&p[0]);
        let (new_name, new) = read(&p[1]);
        let pair = (old_name, new_name);
        if let Some(ref n) = names {
            assert_eq!(n, &pair, "same engines across pairs");
        } else {
            names = Some(pair);
        }
        assert!(old.keys().eq(new.keys()));
        for (cell, before) in old {
            pairs.entry(cell).or_default().push((before, new[&cell]));
        }
    }
    let cells: Vec<_> = pairs.values().cloned().collect();
    let judgments = clocks::summary::discoveries(&cells, 50, 30);
    let (old, new) = names.unwrap();
    println!("# paired {old} versus {new}; {} pairs; medians of per-run means; clocks 5% FDR, 3% margin; new/old ratio", paths.len() / 2);
    println!("pattern\tbytes\toffset\told_ns\tnew_ns\told_GB_s\tnew_GB_s\tnew_old_permille\tmedian_old_new_milli\tpair_old_new_min_milli\tpair_old_new_max_milli\tverdict");
    for ((cell, v), j) in pairs.iter().zip(judgments) {
        let before = median(&mut v.iter().map(|p| p.0).collect::<Vec<_>>());
        let after = median(&mut v.iter().map(|p| p.1).collect::<Vec<_>>());
        // bytes / nanoseconds is decimal GB/s. Retain fixed point until display.
        let ratios: Vec<_> = v.iter().map(|&(a, b)| clocks::summary::ratio_permille(a, b)).collect();
        println!(
            "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{:?}",
            cell.0,
            cell.1,
            cell.2,
            decimal(before),
            decimal(after),
            gbps(cell.1, before),
            gbps(cell.1, after),
            j.ratio_permille,
            clocks::summary::ratio_permille(before, after),
            ratios.iter().min().unwrap(),
            ratios.iter().max().unwrap(),
            j.verdict
        );
    }
}
fn main() {
    let args: Vec<_> = std::env::args().skip(1).collect();
    match args.first().map(String::as_str) {
        Some("--validate") if args.len() == 1 => {
            validate();
            adler_validation_done();
            println!("{} engines agree; linked Ode bytes checked; no timing performed", ENGINES.len());
        }
        Some("--overread-control") if args.len() == 1 => guard_pages(&[("deliberate one-byte overread", deliberate_overread)]),
        Some("--collect") if args.len() == 2 => std::process::exit(collect(&args[1], false)),
        Some("--probe") if args.len() == 2 => std::process::exit(collect(&args[1], true)),
        Some("--compare") => compare(&args[1..]),
        _ => panic!("usage: --validate | --collect ENGINE | --probe ENGINE | --compare OLD NEW [OLD NEW ...]"),
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn linked_bytes_and_examples() {
        super::validate();
    }
    fn fixture(ns: u64) -> String {
        fixture_mode(ns, false)
    }
    fn fixture_mode(ns: u64, probe: bool) -> String {
        let mut s = format!("{}\n# engine: ode\n# workload: {}\n", super::FORMAT, if probe { "probe" } else { "full" });
        for (p, n, o) in super::cells(probe) {
            for i in 0..12 {
                s.push_str(&format!("{p}\t{n}\t{o}\t{i}\t1\t{ns}\t-\t-\t-\t-\t-\t-\t-\t0\n"));
            }
        }
        s + "# accepted: quiet\n"
    }
    #[test]
    fn probe_contract() {
        let (_, rows) = super::read_text(&fixture_mode(100, true));
        assert_eq!(
            rows.keys().copied().collect::<Vec<_>>(),
            [0, 1, 16, 64, 256, 4096, 65536, 1048576].into_iter().flat_map(|n| [(3, n, 0), (3, n, 1)]).collect::<Vec<_>>()
        );
        assert_eq!(super::cells(false).len(), 80);
    }
    #[test]
    #[should_panic(expected = "exactly the declared workload cells")]
    fn mislabeled_workload_is_refused() {
        super::read_text(&fixture(100).replace("workload: full", "workload: probe"));
    }
    #[test]
    fn raw_reader_and_shared_judge_controls() {
        use clocks::summary::{discoveries, Verdict};
        let (_, old) = super::read_text(&fixture(100));
        let (_, new) = super::read_text(&fixture(120));
        assert!(old.values().all(|&m| m == 100u128 << 64));
        let same: Vec<_> = old.values().map(|&v| vec![(v, v); 4]).collect();
        assert!(discoveries(&same, 50, 30).iter().all(|j| j.verdict == Verdict::Level));
        let slower: Vec<_> = old.iter().map(|(k, &v)| vec![(v, new[k]); 4]).collect();
        assert!(discoveries(&slower, 50, 30).iter().all(|j| j.verdict == Verdict::Slower && j.ratio_permille == 1200));
    }
    #[test]
    #[should_panic(expected = "comparison abstains")]
    fn busy_samples_require_abstention() {
        super::read_text(&fixture(100).replace("accepted: quiet", "accepted: busy"));
    }
    #[test]
    #[should_panic(expected = "samples appear once")]
    fn duplicates_are_refused() {
        super::read_text(&fixture(100).replace("0\t0\t0\t1\t1\t", "0\t0\t0\t0\t1\t"));
    }
    #[test]
    #[should_panic(expected = "samples format")]
    fn another_format_is_refused() {
        super::read_text(&fixture(100).replace(super::FORMAT, "# old-format"));
    }
    #[test]
    fn alignments_and_patterns() {
        for p in 0..4 {
            for n in [0, 1, 4096] {
                let (a, i) = super::input(p, n, 0);
                let (b, j) = super::input(p, n, 1);
                assert_eq!((a.as_ptr() as usize + i) % 64, 0);
                assert_eq!((b.as_ptr() as usize + j) % 64, 1);
                assert_eq!(&a[i..i + n], &b[j..j + n]);
            }
        }
        assert_eq!(super::median(&mut [4, 1, 3, 2]), 2);
        assert_eq!(super::decimal(123u128 << 64), "123.00");
        assert_eq!(super::gbps(4096, 1000u128 << 64), "4.10");
        assert_eq!(super::gbps(0, 1000u128 << 64), "-");
    }
}
