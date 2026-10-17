//! The one way every measurement summarises and compares its samples, in
//! the fork, bench-hashes, and every probe.
//!
//! **A run's cost** for a cell is its mean: the total timed nanoseconds of
//! its samples over the total work they did ([`mean`]). That is what a
//! caller pays on average, it moves continuously when a cell spends more or
//! less of its time at a slower speed, and it takes no cut-offs.
//!
//! **Comparing two programs** takes pairs of runs, one of each, back to back
//! and in alternating order, so that drift between the runs falls on both
//! sides alike. Each pair gives one ratio per cell, new mean over old
//! ([`ratio_permille`]). Most of a measurement's uncertainty lies between
//! runs (where the program's code landed, where its threads were placed),
//! which no figure from inside one run can see; the pairs see it. A cell is
//! slower ([`verdict`]) when the median of its ratios exceeds 1 plus the
//! margin and an exact sign test says the new side was slower in more pairs
//! than chance would give, at one-sided p <= 5% ([`least_count`]): one
//! assumption alone, that a pair is as likely to come out either way when
//! nothing changed.
//!
//! **Before changing these rules**, read bench-hashes' `COMPARISONS.md`:
//! each choice's evidence, what it gives up, the alternatives already set
//! aside, and why the rules kept changing. In particular, [`verdict`] suits
//! a check of a few cells (the regression check's): over a comparison's
//! 700 cells it flags a dozen cells of unchanged code, and judging many
//! cells at once needs their false discovery rate controlled (bench-hashes
//! #11 with this fork's #44, adopted October 16, 2026).
//!
//! **Values** are nanoseconds per unit in fixed point, 64 integer and 64
//! fractional bits (Q64.64, as bench-hashes' `Fixed`); ratios in permille;
//! integers throughout, rounded once where a person reads them.

/// The mean of samples given as (timed ns, units of work): total ns over
/// total units, in Q64.64 ns per unit, rounded to the nearest. Requires some
/// units, and a total under 2^64 ns.
pub fn mean(samples: impl IntoIterator<Item = (u64, u64)>) -> u128 {
    let (ns, units) = samples.into_iter().fold((0u128, 0u128), |(ns, units), (n, u)| (ns + u128::from(n), units + u128::from(u)));
    assert!(units > 0, "a mean needs some work done");
    assert!(ns < 1 << 64, "a run's samples total under 2^64 ns");
    ((ns << 64) + units / 2) / units
}

/// `new / old` in permille, rounded. Requires `old > 0`.
pub fn ratio_permille(new: u128, old: u128) -> u64 {
    assert!(old > 0, "a ratio needs a divisor");
    let (new, old) = (new >> 8, old >> 8); // headroom for the factor of 1000
    assert!(old > 0, "a ratio needs a divisor above 2^-56 ns per unit");
    u64::try_from((new * 1000 + old / 2) / old).expect("a ratio fits in u64")
}

/// The median of permille ratios (for an even count, the mean of the two
/// middle ones, rounded up). Requires some.
pub fn median_permille(ratios: &[u64]) -> u64 {
    assert!(!ratios.is_empty(), "a median needs a value");
    let mut sorted = ratios.to_vec();
    sorted.sort_unstable();
    let n = sorted.len();
    if n % 2 == 1 {
        sorted[n / 2]
    } else {
        (sorted[n / 2 - 1] + sorted[n / 2]).div_ceil(2)
    }
}

/// The least number of `pairs` that must agree for the sign test to call a
/// change at one-sided p <= 5%: the least k with P(X >= k) <= 1/20 for X
/// binomial(pairs, 1/2). `pairs + 1` (never) when even all of them cannot.
/// Requires `pairs` from 1 to 64.
pub fn least_count(pairs: usize) -> usize {
    assert!((1..=64).contains(&pairs), "a sign test over 1 to 64 pairs");
    let mut choose = vec![1u128; pairs + 1]; // C(pairs, j)
    for j in 1..=pairs {
        choose[j] = choose[j - 1] * (pairs - j + 1) as u128 / j as u128;
    }
    let total = 1u128 << pairs;
    (0..=pairs + 1).find(|&k| k <= pairs && choose[k..].iter().sum::<u128>() * 20 <= total).unwrap_or(pairs + 1)
}

/// What the pairs say of one cell.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Verdict {
    Slower,
    Faster,
    Level,
}

/// The ratios the pairs leave plausible for the cell's median ratio (new
/// over old, permille): the sign test's interval, the [`least_count`]-th
/// ratio from each end, about 90% two-sided (each side one-sided p <= 5%).
/// A median ratio outside it is one the sign test rejects. `None` when the
/// pairs are too few for the test to reject anything.
pub fn interval_permille(ratios: &[u64]) -> Option<(u64, u64)> {
    let n = ratios.len();
    let k = least_count(n);
    if k > n {
        return None;
    }
    let mut sorted = ratios.to_vec();
    sorted.sort_unstable();
    Some((sorted[n - k], sorted[k - 1]))
}

/// A cell's verdict from its pairs' ratios (new over old, permille): slower
/// when the median exceeds 1000 + `margin_permille` and the whole
/// [`interval_permille`] lies above 1000 (at least [`least_count`] pairs
/// slower); faster alike, below.
pub fn verdict(ratios: &[u64], margin_permille: u64) -> Verdict {
    let median = median_permille(ratios);
    match interval_permille(ratios) {
        Some((low, _)) if median > 1000 + margin_permille && low > 1000 => Verdict::Slower,
        Some((_, high)) if median + margin_permille < 1000 && high < 1000 => Verdict::Faster,
        _ => Verdict::Level,
    }
}

/// Which cells of a comparison changed, every cell judged at once: for each
/// cell, its pairs' means (old, new; fixed point, as [`mean`] gives them),
/// a paired t-test on log(new / old); the cells whose p-values pass the
/// Benjamini-Hochberg procedure at a false discovery rate of `q_permille`
/// over all the cells; and of those, the ones whose geometric mean ratio
/// lies beyond `margin_permille` slower or faster. The rest are level.
///
/// Why (bench-hashes audit/variance-on-unchanged-code.md, i7-12700K):
/// unchanged code read faster or slower in 15-27 of 700 cells under a
/// sign test per cell (5 pairs): cold calls vary in cycles with each
/// run's address layout and each binary's link layout, and 700 tests at
/// a few percent each add up. This rule found none in the same data, and
/// the code's changes when every pair ran fresh layouts. Statistics need
/// floating point here; inputs and verdicts stay exact.
///
/// Requires at least 3 pairs per cell, every cell the same count, and
/// every mean positive.
pub fn discoveries(cells: &[Vec<(u128, u128)>], q_permille: u64, margin_permille: u64) -> Vec<Verdict> {
    let pairs = cells.first().map_or(0, Vec::len);
    assert!(pairs >= 3 && cells.iter().all(|c| c.len() == pairs), "every cell has the same count of pairs, at least 3");
    // (p-value, geometric mean ratio) per cell.
    let tested: Vec<(f64, f64)> = cells
        .iter()
        .map(|c| {
            let d: Vec<f64> = c
                .iter()
                .map(|&(old, new)| {
                    assert!(old > 0 && new > 0, "means are positive");
                    (new as f64).ln() - (old as f64).ln()
                })
                .collect();
            let n = d.len() as f64;
            let mu = d.iter().sum::<f64>() / n;
            let var = d.iter().map(|x| (x - mu) * (x - mu)).sum::<f64>() / (n - 1.0);
            let p = if var == 0.0 {
                if mu == 0.0 {
                    1.0
                } else {
                    0.0
                }
            } else {
                t_two_sided(mu / (var / n).sqrt(), n - 1.0)
            };
            (p, mu.exp())
        })
        .collect();
    // Benjamini-Hochberg: the largest rank k with p_(k) <= q k / m.
    let m = cells.len();
    let mut order: Vec<usize> = (0..m).collect();
    order.sort_by(|&a, &b| tested[a].0.total_cmp(&tested[b].0));
    let q = q_permille as f64 / 1000.0;
    let passed = (1..=m).rev().find(|&k| tested[order[k - 1]].0 <= q * k as f64 / m as f64).unwrap_or(0);
    let mut verdicts = vec![Verdict::Level; m];
    let margin = margin_permille as f64 / 1000.0;
    for &i in &order[..passed] {
        let ratio = tested[i].1;
        if ratio > 1.0 + margin {
            verdicts[i] = Verdict::Slower;
        } else if ratio < 1.0 - margin {
            verdicts[i] = Verdict::Faster;
        }
    }
    verdicts
}

/// Student's t two-sided p-value: P(|T| >= |t|) with `df` degrees of
/// freedom, the regularized incomplete beta I(df / (df + t^2); df / 2, 1/2).
fn t_two_sided(t: f64, df: f64) -> f64 {
    incomplete_beta(df / 2.0, 0.5, df / (df + t * t))
}

/// The regularized incomplete beta I_x(a, b), by its continued fraction
/// (Numerical Recipes, betai and betacf).
fn incomplete_beta(a: f64, b: f64, x: f64) -> f64 {
    if x <= 0.0 {
        return 0.0;
    }
    if x >= 1.0 {
        return 1.0;
    }
    let front = (ln_gamma(a + b) - ln_gamma(a) - ln_gamma(b) + a * x.ln() + b * (1.0 - x).ln()).exp();
    if x < (a + 1.0) / (a + b + 2.0) {
        front * beta_fraction(a, b, x) / a
    } else {
        1.0 - front * beta_fraction(b, a, 1.0 - x) / b
    }
}

fn beta_fraction(a: f64, b: f64, x: f64) -> f64 {
    let tiny = 1e-300;
    let (qab, qap, qam) = (a + b, a + 1.0, a - 1.0);
    let mut c = 1.0;
    let mut d = 1.0 - qab * x / qap;
    d = 1.0 / if d.abs() < tiny { tiny } else { d };
    let mut h = d;
    for m in 1..300 {
        let m = m as f64;
        let m2 = 2.0 * m;
        for aa in [m * (b - m) * x / ((qam + m2) * (a + m2)), -(a + m) * (qab + m) * x / ((a + m2) * (qap + m2))] {
            d = 1.0 + aa * d;
            d = 1.0 / if d.abs() < tiny { tiny } else { d };
            c = 1.0 + aa / c;
            c = if c.abs() < tiny { tiny } else { c };
            h *= d * c;
        }
        if (d * c - 1.0).abs() < 1e-15 {
            break;
        }
    }
    h
}

/// ln Gamma(x) for x > 0 (Lanczos, g = 7, 9 terms).
fn ln_gamma(x: f64) -> f64 {
    const G: [f64; 9] = [
        0.999_999_999_999_809_9,
        676.520_368_121_885_1,
        -1_259.139_216_722_402_8,
        771.323_428_777_653_1,
        -176.615_029_162_140_6,
        12.507_343_278_686_905,
        -0.138_571_095_265_720_12,
        9.984_369_578_019_572e-6,
        1.505_632_735_149_311_6e-7,
    ];
    if x < 0.5 {
        return (core::f64::consts::PI / (core::f64::consts::PI * x).sin()).ln() - ln_gamma(1.0 - x);
    }
    let x = x - 1.0;
    let mut a = G[0];
    let t = x + 7.5;
    for (i, g) in G.iter().enumerate().skip(1) {
        a += g / (x + i as f64);
    }
    0.5 * (2.0 * core::f64::consts::PI).ln() + (x + 0.5) * t.ln() - t + a.ln()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_mean_is_total_time_over_total_work() {
        // 3 ns over 2 units and 7 ns over 2 units: 10 ns over 4, 2.5 ns a unit.
        assert_eq!(mean([(3, 2), (7, 2)]), 5 << 63);
        assert_eq!(ratio_permille(mean([(110, 100)]), mean([(100, 100)])), 1100);
    }

    /// The sign test's thresholds, by hand from the binomial: 6 pairs need
    /// all 6 (1/64 = 1.6%; 5 or more is 7/64 = 10.9%); 8 need 7 (9/256 =
    /// 3.5%; 6 or more, 37/256 = 14.5%); 10 need 9 (11/1024 = 1.1%; 8 or
    /// more, 56/1024 = 5.5%); 4 never suffice (1/16 = 6.25%).
    #[test]
    fn the_sign_tests_thresholds() {
        assert_eq!(least_count(4), 5);
        assert_eq!(least_count(6), 6);
        assert_eq!(least_count(8), 7);
        assert_eq!(least_count(10), 9);
    }

    #[test]
    fn verdicts() {
        // Seven of eight pairs slower, the median 5% up: slower at 3%.
        let ratios = [1050, 1060, 1040, 1055, 1048, 990, 1052, 1070];
        assert_eq!(median_permille(&ratios), 1051);
        assert_eq!(verdict(&ratios, 30), Verdict::Slower);
        // The same at a 10% margin: level.
        assert_eq!(verdict(&ratios, 100), Verdict::Level);
        // A median beyond the margin from two wild pairs, but only six of
        // eight above 1: level (the sign test).
        let wild = [1200, 1300, 1040, 1035, 1045, 1033, 970, 980];
        assert_eq!(verdict(&wild, 30), Verdict::Level);
        assert_eq!(verdict(&[940, 950, 960, 955, 945, 1010, 950, 948], 30), Verdict::Faster);
    }

    /// The interval is the sign test inverted: over every set of up to 9
    /// pairs from a few ratios, the verdict through it equals the counts'.
    #[test]
    fn the_interval_is_the_sign_test() {
        let values = [940u64, 990, 1000, 1010, 1060];
        for n in 1..=9usize {
            for code in 0..values.len().pow(n as u32) {
                let ratios: Vec<u64> = (0..n).map(|i| values[code / values.len().pow(i as u32) % values.len()]).collect();
                let k = least_count(n);
                let median = median_permille(&ratios);
                let counted = if median > 1030 && ratios.iter().filter(|&&r| r > 1000).count() >= k {
                    Verdict::Slower
                } else if median + 30 < 1000 && ratios.iter().filter(|&&r| r < 1000).count() >= k {
                    Verdict::Faster
                } else {
                    Verdict::Level
                };
                assert_eq!(verdict(&ratios, 30), counted, "{ratios:?}");
            }
        }
        assert_eq!(interval_permille(&[1010, 1020, 1030, 1040, 1050, 1060, 1070, 1080]), Some((1020, 1070)));
        assert_eq!(interval_permille(&[1000; 4]), None);
    }

    /// Student's t at its tables' points: t = 2.776 with 4 degrees of
    /// freedom is p = 0.05 two-sided; 2.228 with 10, 0.05; 3.169 with 10,
    /// 0.01; t = 0, p = 1.
    #[test]
    fn t_p_values_match_the_tables() {
        for (t, df, p) in [(2.776, 4.0, 0.05), (2.228, 10.0, 0.05), (3.169, 10.0, 0.01), (0.0, 4.0, 1.0)] {
            assert!((t_two_sided(t, df) - p).abs() < 2e-4, "t {t} df {df}: {}", t_two_sided(t, df));
        }
    }

    /// Three cells of five pairs: one 10% slower in every pair, one whose
    /// pairs scatter 3% each way, one 1% faster in every pair (its
    /// p-value passes, but it lies within a 3% margin). The slower cell is
    /// still found among 1000 unchanged ones; at q = 0 nothing is.
    #[test]
    fn discoveries_judge_every_cell_at_once() {
        let pairs = |ratios: &[u128]| ratios.iter().map(|&r| (1000u128 << 63, r << 63)).collect::<Vec<_>>();
        let cells = vec![pairs(&[1100, 1102, 1098, 1101, 1099]), pairs(&[1030, 970, 1025, 975, 1000]), pairs(&[990, 991, 989, 990, 990])];
        assert_eq!(discoveries(&cells, 50, 30), [Verdict::Slower, Verdict::Level, Verdict::Level]);
        let mut many = vec![pairs(&[1030, 970, 1025, 975, 1000]); 1000];
        many.push(pairs(&[1100, 1102, 1098, 1101, 1099]));
        assert_eq!(discoveries(&many, 50, 30).iter().filter(|&&v| v != Verdict::Level).count(), 1);
        assert!(discoveries(&many, 0, 30).iter().all(|&v| v == Verdict::Level));
    }
}
