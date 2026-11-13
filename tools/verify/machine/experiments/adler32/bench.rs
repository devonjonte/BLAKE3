//! A first workload adapter for Ode's observer: warm Adler-32 calls on public
//! bytes. Raw samples, clocks' mean and paired comparison; no new timing rule.
use std::{collections::BTreeMap, hint::black_box};

unsafe extern "C" {
    fn b3l_adler32(input: *const u8, n: u64) -> u64;
}

const FORMAT: &str = "# ode-adler-samples-v1";
const LENGTHS: [usize; 8] = [0, 1, 16, 64, 256, 1024, 4096, 65536];
const EXPECTED_TEXT: &[u8] = include_bytes!(concat!(env!("CARGO_MANIFEST_DIR"), "/text.bin"));

fn checksum(bytes: &[u8]) -> u64 {
    // Sound under this experiment's tested caller contract: n readable bytes;
    // the assembly is a leaf and its linked bytes are checked before use.
    // Tests give evidence for its implementation; there is no correctness proof.
    unsafe { b3l_adler32(bytes.as_ptr(), bytes.len() as u64) }
}

fn validate() {
    // This adapter admits only a leaf whose code needs no relocation. A changed
    // assembler input or unexpected linked code fails before any call or timing.
    let actual = unsafe { std::slice::from_raw_parts(b3l_adler32 as *const u8, EXPECTED_TEXT.len()) };
    assert_eq!(actual, EXPECTED_TEXT, "linked function differs from the observed bytes");
    for (input, want) in [(b"".as_slice(), 1), (b"a".as_slice(), 0x00620062), (b"Wikipedia".as_slice(), 0x11e60398), (b"123456789".as_slice(), 0x091e01de)] {
        assert_eq!(checksum(input), want);
    }
    for n in [0, 1, 2, 16, 64, 5551, 5552, 5553, 65521, 65536] {
        for pattern in 0..3 {
            let input = input(pattern, n);
            assert_eq!(checksum(&input), reference(&input));
        }
    }
}

fn reference(input: &[u8]) -> u64 {
    let (mut a, mut b) = (1u64, 0u64);
    for byte in input {
        a = (a + u64::from(*byte)) % 65521;
        b = (b + a) % 65521;
    }
    (b << 16) | a
}

fn input(pattern: u8, n: usize) -> Vec<u8> {
    (0..n)
        .map(|i| match pattern {
            0 => 0,
            1 => 255,
            2 => i as u8,
            _ => panic!("unknown pattern"),
        })
        .collect()
}

fn collect() -> i32 {
    validate();
    clocks::load::quiet_for(3).expect("collect needs a quiet measurement machine");
    println!("{FORMAT}");
    println!("# scope: warmed back-to-back FFI calls; public input; includes result consumption; no speed claim from one run");
    println!("# code address: {:p}; padding: {}", b3l_adler32 as *const (), env!("ODE_PADDING"));
    println!("# rustc: {}", env!("ODE_RUSTC"));
    println!("# clocks: bench-hashes 5f99f456951ab36f7201decd8aa5e0249ec67bd1; {}", clocks::WALL_CLOCK);
    println!("# report: {}", include_str!(concat!(env!("CARGO_MANIFEST_DIR"), "/report.json")).replace('\n', " "));
    println!("pattern\tbytes\tsample\tcalls\twall_ns\tcpu_ns\tp_cycles\tp_instructions\tp_time_ns\te_cycles\te_instructions\te_time_ns\tstarted_ns");
    let mut all = vec![];
    for pattern in 0..3 {
        for len in LENGTHS {
            let input = input(pattern, len);
            let samples = clocks::measure(12, 5_000_000, || {
                black_box(checksum(black_box(&input)));
            });
            let mean = clocks::summary::mean(samples.iter().map(|s| (s.wall_ns, s.calls)));
            let hundredths = ((mean * 100) + (1u128 << 63)) >> 64;
            eprintln!("pattern {pattern}, {len} bytes: {}.{:02} ns/call (run mean)", hundredths / 100, hundredths % 100);
            for (i, s) in samples.into_iter().enumerate() {
                let c = s
                    .counts
                    .map(|c| format!("{}\t{}\t{}\t{}\t{}\t{}", c.p.cycles, c.p.instructions, c.p.time_ns, c.e.cycles, c.e.instructions, c.e.time_ns))
                    .unwrap_or_else(|| "-\t-\t-\t-\t-\t-".into());
                println!(
                    "{pattern}\t{len}\t{i}\t{}\t{}\t{}\t{c}\t{}",
                    s.calls,
                    s.wall_ns,
                    s.cpu_ns.map_or_else(|| "-".into(), |n| n.to_string()),
                    s.started_ns
                );
                all.push(s);
            }
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

type Cell = (u8, usize);
fn read(path: &str) -> BTreeMap<Cell, u128> {
    let text = std::fs::read_to_string(path).expect("samples exist");
    read_text(&text)
}

fn read_text(text: &str) -> BTreeMap<Cell, u128> {
    assert_eq!(text.lines().next(), Some(FORMAT), "samples format");
    assert!(text.lines().any(|l| l == "# accepted: quiet"), "comparison abstains on busy or unobserved load");
    let mut cells: BTreeMap<Cell, Vec<(u64, u64)>> = BTreeMap::new();
    for l in text.lines().filter(|l| !l.starts_with('#') && !l.starts_with("pattern") && !l.is_empty()) {
        let p: Vec<_> = l.split('\t').collect();
        assert_eq!(p.len(), 13);
        let key = (p[0].parse().unwrap(), p[1].parse().unwrap());
        let sample: usize = p[2].parse().unwrap();
        let v = cells.entry(key).or_default();
        assert_eq!(sample, v.len(), "samples appear once in order");
        v.push((p[4].parse().unwrap(), p[3].parse().unwrap()));
    }
    let expected: Vec<_> = (0..3).flat_map(|pattern| LENGTHS.map(|len| (pattern, len))).collect();
    assert!(cells.keys().copied().eq(expected), "exactly the declared workload cells");
    cells
        .into_iter()
        .map(|(k, v)| {
            assert_eq!(v.len(), 12);
            (k, clocks::summary::mean(v))
        })
        .collect()
}

fn compare(paths: &[String]) {
    assert!(paths.len() >= 6 && paths.len() % 2 == 0, "at least three corresponding OLD NEW pairs");
    let mut pairs: BTreeMap<Cell, Vec<(u128, u128)>> = BTreeMap::new();
    for p in paths.chunks_exact(2) {
        let old = read(&p[0]);
        let new = read(&p[1]);
        assert!(old.keys().eq(new.keys()));
        for (cell, before) in old {
            pairs.entry(cell).or_default().push((before, new[&cell]));
        }
    }
    let cells: Vec<_> = pairs.values().cloned().collect();
    // Existing bench-hashes comparison, unchanged: 5% FDR, 3% margin.
    let judgments = clocks::summary::discoveries(&cells, 50, 30);
    println!("Exploratory paired comparison; {} pairs, explicit link paddings; clocks' existing rule", paths.len() / 2);
    for ((cell, _), j) in pairs.iter().zip(judgments) {
        println!("pattern {}, {} bytes: {:?}, new/old {} permille", cell.0, cell.1, j.verdict, j.ratio_permille);
    }
    println!("Raw counts and speed states remain in the samples. This pilot establishes no release or reliability claim.");
}

fn main() {
    let args: Vec<_> = std::env::args().skip(1).collect();
    match args.first().map(String::as_str) {
        Some("--validate") if args.len() == 1 => {
            validate();
            println!("linked bytes and checksum examples agree; no timing performed");
        }
        Some("--collect") if args.len() == 1 => std::process::exit(collect()),
        Some("--compare") => compare(&args[1..]),
        _ => panic!("usage: --validate | --collect | --compare OLD NEW [OLD NEW ...]"),
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn linked_bytes_and_examples() {
        super::validate();
    }

    fn fixture(ns: u64) -> String {
        let mut s = format!("{}\n", super::FORMAT);
        for p in 0..3 {
            for n in super::LENGTHS {
                for i in 0..12 {
                    s.push_str(&format!("{p}\t{n}\t{i}\t1\t{ns}\t-\t-\t-\t-\t-\t-\t-\t0\n"));
                }
            }
        }
        s + "# accepted: quiet\n"
    }

    #[test]
    fn raw_reader_and_shared_judge_controls() {
        use clocks::summary::{discoveries, Verdict};
        let old = super::read_text(&fixture(100));
        assert!(old.values().all(|&m| m == 100u128 << 64));
        let new = super::read_text(&fixture(120));
        let same: Vec<_> = old.values().map(|&v| vec![(v, v); 4]).collect();
        assert!(discoveries(&same, 50, 30).iter().all(|j| j.verdict == Verdict::Level));
        let slower: Vec<_> = old.iter().map(|(k, &v)| vec![(v, new[k]); 4]).collect();
        assert!(discoveries(&slower, 50, 30).iter().all(|j| j.verdict == Verdict::Slower && j.ratio_permille == 1200));
    }

    #[test]
    #[should_panic(expected = "comparison abstains")]
    fn busy_samples_require_abstention() {
        super::read_text(&fixture(100).replace("accepted: quiet", "accepted: busy-or-unobserved"));
    }

    #[test]
    #[should_panic(expected = "samples appear once")]
    fn duplicate_samples_are_refused() {
        super::read_text(&fixture(100).replace("0\t0\t1\t1\t", "0\t0\t0\t1\t"));
    }

    #[test]
    #[should_panic(expected = "samples format")]
    fn another_format_is_refused() {
        super::read_text(&fixture(100).replace(super::FORMAT, "# another-version"));
    }
}
