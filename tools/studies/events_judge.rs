//! The judge for events_sampler's runs: which cells (shape x event)
//! changed, by the servil projects' one rule, `clocks::summary::discoveries`
//! (a paired t-test per cell over pairs of runs, false discovery rate 5%
//! over all cells, a 3% margin). Arguments: the runs' TSV files, in pairs,
//! OLD NEW OLD NEW ...; every run's digest line must agree. A cell whose
//! mean is zero in any run (an event that never fired) is listed as such
//! and left unjudged. Per cell: the event per message on each side (the
//! mean of its pairs' run means, 3 decimals), the ratio new over old in
//! permille, and the verdict.
use clocks::summary::{discoveries, mean, Verdict};
use std::collections::BTreeMap;

fn main() {
    let files: Vec<String> = std::env::args().skip(1).collect();
    assert!(files.len() >= 6 && files.len() % 2 == 0, "pairs of files, OLD NEW ..., at least 3 pairs");
    // (shape, event) -> run index -> samples (count, units).
    let mut cells: BTreeMap<(String, String), Vec<Vec<(u64, u64)>>> = BTreeMap::new();
    let mut digests = Vec::new();
    for (run, file) in files.iter().enumerate() {
        let text = std::fs::read_to_string(file).unwrap_or_else(|e| panic!("{file}: {e}"));
        for line in text.lines() {
            let f: Vec<&str> = line.split('\t').collect();
            match f[0] {
                "sample" => {
                    let runs = cells.entry((f[1].to_owned(), f[2].to_owned())).or_insert_with(|| vec![Vec::new(); files.len()]);
                    runs[run].push((f[3].parse().unwrap(), f[4].parse().unwrap()));
                }
                "digest" => digests.push(f[1].to_owned()),
                _ => {}
            }
        }
    }
    assert_eq!(digests.len(), files.len(), "one digest a run");
    assert!(digests.iter().all(|d| *d == digests[0]), "every run produced the same hashes");
    let pairs = files.len() / 2;
    let mut judged = Vec::new();
    let mut zero = Vec::new();
    for ((shape, event), runs) in &cells {
        assert!(runs.iter().all(|r| !r.is_empty()), "{shape}/{event}: a sample in every run");
        let means: Vec<u128> = runs.iter().map(|r| mean(r.iter().copied())).collect();
        if means.iter().any(|&m| m == 0) {
            zero.push((shape, event));
            continue;
        }
        let pair_means: Vec<(u128, u128)> = (0..pairs).map(|p| (means[2 * p], means[2 * p + 1])).collect();
        judged.push(((shape, event), pair_means));
    }
    let verdicts = discoveries(&judged.iter().map(|(_, p)| p.clone()).collect::<Vec<_>>(), 50, 30);
    let show = |v: u128| {
        let whole = v >> 64;
        let thousandths = ((v & (u128::MAX >> 64)) * 1000) >> 64;
        format!("{whole}.{thousandths:03}")
    };
    println!("{pairs} pairs of runs; per message (per sample for nothing): old, new, new/old permille, verdict");
    println!("{:<18} {:<40} {:>14} {:>14} {:>8} {}", "shape", "event", "old", "new", "ratio", "verdict");
    for (((shape, event), pair_means), j) in judged.iter().zip(&verdicts) {
        let side = |k: usize| show(pair_means.iter().map(|p| if k == 0 { p.0 } else { p.1 }).sum::<u128>() / pairs as u128);
        let verdict = match j.verdict {
            Verdict::Slower => "MORE",
            Verdict::Faster => "FEWER",
            Verdict::Level => "level",
        };
        println!("{shape:<18} {event:<40} {:>14} {:>14} {:>8} {verdict}", side(0), side(1), j.ratio_permille);
    }
    for (shape, event) in zero {
        println!("{shape:<18} {event:<40} {:>14} {:>14} {:>8} zero in some run; unjudged", "", "", "");
    }
}
