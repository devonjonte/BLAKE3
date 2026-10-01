//! The one way every measurement summarises and compares its samples, in
//! the fork, bench-hashes, and every probe; Python tools reach it through
//! `bench-hashes compare`.
//!
//! **Many cells run at two speeds.** Two copies of an SME2 kernel run at
//! full speed on two P-clusters and at about half on one; a queue's
//! handovers run at one speed or another by the threads' placement; a
//! call after a pause meets a fast or a slow clock; a VM's host moves it
//! between core kinds. A single median of such a cell lands on either
//! speed by chance, and a comparison of two medians then reports a change
//! that is only a different share of the two speeds: that sent us on
//! goose chases and misjudged optimisations. So every summary here is a
//! list of speeds, and every comparison compares speed with speed and
//! share with share.
//!
//! **The rule** (bench-hashes' since September 25, 2026; its NOTES, "Two
//! speeds"): sort the samples; a cell has two speeds when two neighbours
//! in sorted order are [`GAP_PERMILLE`] of the median or more apart, with
//! [`MIN_SHARE_PERMILLE`] of the samples or more on each side, and the
//! slower side's median is [`RATIO_PERMILLE`] of the faster's or more; the
//! widest such gap splits them. The 1.25x floor: on the VM the machine's
//! own noise puts a tenth to a third of many cells' samples 10-14% slow
//! for every contender alike; SME2 unit sharing splits 1.7-2.0x.
//!
//! **Values** are nanoseconds per unit in fixed point, 64 integer and 64
//! fractional bits (Q64.64, as bench-hashes' `Fixed`), from [`per_unit`]:
//! integers throughout, rounded once where a person reads them.

/// Neighbouring sorted samples this far apart, in permille of the median,
/// may split a cell into two speeds.
pub const GAP_PERMILLE: u64 = 40;
/// The share of the samples each speed holds at least, in permille.
pub const MIN_SHARE_PERMILLE: usize = 100;
/// The slower speed's median over the faster's, in permille, at least.
pub const RATIO_PERMILLE: u64 = 1250;
/// A sample of `ns` nanoseconds over `units` units, as nanoseconds per unit
/// in Q64.64, rounded to the nearest representable value. Requires
/// `units > 0` and `ns < 2^40` (18 minutes).
pub fn per_unit(ns: u64, units: u64) -> u128 {
    assert!(units > 0, "a sample covers some units");
    assert!(ns < 1 << 40, "a sample of {ns} ns exceeds 2^40 ns (18 minutes)");
    ((u128::from(ns) << 64) + u128::from(units) / 2) / u128::from(units)
}

/// The median of a sorted, non-empty slice: the middle value, or the
/// midpoint of the two middle values.
pub fn median_of_sorted(sorted: &[u128]) -> u128 {
    assert!(!sorted.is_empty(), "a median needs a sample");
    debug_assert!(sorted.windows(2).all(|pair| pair[0] <= pair[1]), "sorted");
    let middle = sorted.len() / 2;
    if sorted.len() % 2 == 0 {
        sorted[middle - 1].midpoint(sorted[middle])
    } else {
        sorted[middle]
    }
}

/// One speed a cell ran at: its samples' median, and how many samples it
/// holds.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Speed {
    pub median: u128,
    pub count: usize,
}

/// Where the rule splits a sorted, non-empty slice into two speeds: the
/// index of the first slow sample, or `None` for one speed.
pub fn split(sorted: &[u128]) -> Option<usize> {
    let n = sorted.len();
    assert!(n > 0, "a split needs a sample");
    let median = median_of_sorted(sorted);
    let min_side = (n * MIN_SHARE_PERMILLE).div_ceil(1000).max(1);
    let mut best: Option<(usize, u128)> = None;
    for at in min_side..=n.saturating_sub(min_side) {
        if at == 0 || at == n {
            continue;
        }
        let gap = sorted[at] - sorted[at - 1];
        if gap * 1000 >= median * u128::from(GAP_PERMILLE) && best.is_none_or(|(_, widest)| gap > widest) {
            best = Some((at, gap));
        }
    }
    let (at, _) = best?;
    let (fast, slow) = (median_of_sorted(&sorted[..at]), median_of_sorted(&sorted[at..]));
    // The ratio rounded to permille, as every report prints it.
    (ratio_permille(slow, fast) >= RATIO_PERMILLE).then_some(at)
}

/// A sorted, non-empty slice's speeds, faster first: one, or two.
pub fn speeds(sorted: &[u128]) -> Vec<Speed> {
    let speed = |part: &[u128]| Speed { median: median_of_sorted(part), count: part.len() };
    match split(sorted) {
        Some(at) => vec![speed(&sorted[..at]), speed(&sorted[at..])],
        None => vec![speed(sorted)],
    }
}

/// `a / b` in permille, rounded. Requires `b > 0`.
pub fn ratio_permille(a: u128, b: u128) -> u64 {
    assert!(b > 0, "a ratio needs a divisor");
    u64::try_from((a * 1000 + b / 2) / b).expect("a ratio fits in u64")
}

/// Two sets of samples of one cell compared, speed with speed: what an A/B
/// of a cell that may run at two speeds says.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Comparison {
    /// Each side's speeds, faster first.
    pub old: Vec<Speed>,
    pub new: Vec<Speed>,
    /// New over old, in permille, of the fast speeds' medians and of the
    /// slow speeds' (a side with one speed: that speed is both).
    pub fast_permille: u64,
    pub slow_permille: u64,
    /// The slow speed's share of each side's samples, in permille (0 for a
    /// side with one speed).
    pub old_slow_share_permille: u64,
    pub new_slow_share_permille: u64,
}

impl Comparison {
    /// Whether either side ran at two speeds.
    pub fn two_speeds(&self) -> bool {
        self.old.len() > 1 || self.new.len() > 1
    }
}

/// Compare two sorted, non-empty slices of one cell's samples.
pub fn compare(old: &[u128], new: &[u128]) -> Comparison {
    let (old, new) = (speeds(old), speeds(new));
    let share = |speeds: &[Speed]| -> u64 {
        if speeds.len() < 2 {
            return 0;
        }
        let total: usize = speeds.iter().map(|speed| speed.count).sum();
        ((speeds[1].count * 1000 + total / 2) / total) as u64
    };
    Comparison {
        fast_permille: ratio_permille(new[0].median, old[0].median),
        slow_permille: ratio_permille(new.last().unwrap().median, old.last().unwrap().median),
        old_slow_share_permille: share(&old),
        new_slow_share_permille: share(&new),
        old,
        new,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The rule's vectors: each line a set of samples as ns/units and the
    /// split the rule gives, built so the answer is plain by construction.
    #[test]
    fn vectors() {
        let text = include_str!("../speeds_vectors.txt");
        let mut checked = 0;
        for line in text.lines().filter(|line| !line.starts_with('#') && !line.trim().is_empty()) {
            let (samples, expected) = line.split_once(" -> ").expect("samples -> split");
            let mut values: Vec<u128> = samples
                .split(',')
                .map(|sample| {
                    let (ns, units) = sample.trim().split_once('/').expect("ns/units");
                    per_unit(ns.parse().unwrap(), units.parse().unwrap())
                })
                .collect();
            values.sort_unstable();
            let expected = match expected.trim() {
                "none" => None,
                at => Some(at.parse::<usize>().unwrap()),
            };
            assert_eq!(split(&values), expected, "{line}");
            checked += 1;
        }
        assert!(checked >= 8, "the vectors file holds its cases");
    }

    #[test]
    fn compare_reports_a_share_moved_between_speeds() {
        // Old: 8 fast (100) and 2 slow (200); new: 3 fast and 7 slow. Both
        // speeds' medians unchanged; the slow share went 20% -> 70%.
        let mk = |fast: usize, slow: usize| {
            let mut v: Vec<u128> = std::iter::repeat_n(per_unit(100, 1), fast).chain(std::iter::repeat_n(per_unit(200, 1), slow)).collect();
            v.sort_unstable();
            v
        };
        let c = compare(&mk(8, 2), &mk(3, 7));
        assert_eq!((c.fast_permille, c.slow_permille), (1000, 1000));
        assert_eq!((c.old_slow_share_permille, c.new_slow_share_permille), (200, 700));
        assert!(c.two_speeds());
    }
}
