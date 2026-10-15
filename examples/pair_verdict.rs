//! Paired verdicts from bench-hashes samples files (format v4):
//! `pair_verdict MARGIN_PERMILLE OLD.tsv... -- NEW.tsv...` pairs the i-th
//! old run with the i-th new run, takes each cell's run mean
//! (clocks::summary::mean over its ns/units samples), and prints per cell
//! the median new/old ratio, how many pairs were faster, and the verdict
//! (clocks::summary::verdict).
use std::collections::BTreeMap;

fn means(path: &str) -> BTreeMap<String, u128> {
    let text = std::fs::read_to_string(path).unwrap();
    assert!(text.starts_with("# bench-hashes samples v4"), "{path}: samples v4");
    let mut cells = BTreeMap::new();
    for line in text.lines().filter(|l| !l.starts_with('#')).skip(1) {
        let f: Vec<&str> = line.split('\t').collect();
        let samples = f[5].split(',').map(|s| { let (n, u) = s.split_once('/').unwrap(); (n.parse::<u64>().unwrap(), u.parse::<u64>().unwrap()) });
        cells.insert(format!("{}|{}|{}|{}", f[0], f[1], f[2], f[3]), clocks::summary::mean(samples));
    }
    cells
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let margin: u64 = args[0].parse().unwrap();
    let split = args.iter().position(|a| a == "--").unwrap();
    let (old, new) = (&args[1..split], &args[split + 1..]);
    assert_eq!(old.len(), new.len(), "one new run per old run");
    let mut ratios: BTreeMap<String, Vec<u64>> = BTreeMap::new();
    for (o, n) in old.iter().zip(new) {
        let (o, n) = (means(o), means(n));
        for (key, m) in &o { ratios.entry(key.clone()).or_default().push(clocks::summary::ratio_permille(n[key], *m)); }
    }
    for (key, r) in &ratios {
        let faster = r.iter().filter(|&&x| x < 1000).count();
        println!("{key}: median x{:.3}, faster in {faster} of {}, {:?}", clocks::summary::median_permille(r) as f64 / 1000.0, r.len(), clocks::summary::verdict(r, margin));
    }
}
