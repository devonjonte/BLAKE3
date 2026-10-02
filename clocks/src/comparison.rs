//! Caller-cost comparison for the experimental fixed-block regression gate.
//! Each run contributes its raw total time/work. Each independent ABBA block
//! contributes one ratio; the fixed-budget interval targets their mean ratio.
//! Statistical scope: 16 independent approximately normal block ratios,
//! df15 t interval, critical9/2, at most84 simultaneous two-sided intervals.
//! Its model-based Bonferroni family-error bound is about3.56%. Live controls
//! establish empirical scope. Integer arithmetic rounds bounds outward.

pub const BLOCKS: usize = 16;
pub const MAX_CELLS: usize = 84;
pub const SCALE: u128 = 1_000_000;

#[derive(Clone, Copy, Debug, Default)]
pub struct Work {
    pub ns: u128,
    pub units: u128,
}
impl Work {
    pub fn add(&mut self, ns: u64, units: u64) {
        assert!(ns > 0 && units > 0, "a measured batch has positive time and work");
        self.ns = self.ns.checked_add(u128::from(ns)).expect("time total fits u128");
        self.units = self.units.checked_add(u128::from(units)).expect("work total fits u128");
    }
    pub fn plus(self, other: Self) -> Self {
        Self { ns: self.ns.checked_add(other.ns).unwrap(), units: self.units.checked_add(other.units).unwrap() }
    }
    /// The caller's mean time/unit in Q64.64, rounded at its last bit.
    pub fn mean_fixed(self) -> u128 {
        assert!(self.ns > 0 && self.units > 0);
        let (mut whole, mut remainder) = (self.ns / self.units, self.ns % self.units);
        for bits in [24,24,16] {
            let step=remainder.checked_shl(bits).unwrap();
            whole=(whole<<bits)|(step/self.units);remainder=step%self.units;
        }
        whole + u128::from(remainder >= self.units.div_ceil(2))
    }
    /// Display raw total time/work after one decimal rounding.
    pub fn format_mean(self, factor:u64) -> String {
        assert!(self.ns > 0 && self.units > 0);
        let numerator=self.ns.checked_mul(u128::from(factor)).unwrap();
        let mut decimals=3u32;
        while decimals<6 && numerator.checked_mul(10u128.pow(decimals-2)).unwrap()<self.units {decimals+=1;}
        let scale=10u128.pow(decimals);
        let value=numerator.checked_mul(scale).unwrap();
        let rounded=value/self.units + u128::from(value%self.units>=self.units.div_ceil(2));
        format!("{}.{:0width$}",rounded/scale,rounded%scale,width=decimals as usize)
    }
}

fn gcd(mut a: u128, mut b: u128) -> u128 {
    while b > 0 { (a, b) = (b, a % b); }
    a
}
/// One ABBA block's new/old ratio in ppm. Cancel common factors before
/// multiplication, and round to nearest ppm. Raw ns/work totals stay retained.
pub fn ratio(old: Work, new: Work) -> u64 {
    assert!(old.ns > 0 && old.units > 0 && new.ns > 0 && new.units > 0);
    let mut numerator = [new.ns, old.units, SCALE];
    let mut denominator = [new.units, old.ns];
    for a in &mut numerator {
        for b in &mut denominator { let common = gcd(*a, *b); *a /= common; *b /= common; }
    }
    let n = numerator.into_iter().try_fold(1u128, |a, b| a.checked_mul(b)).expect("ratio numerator fits u128");
    let d = denominator.into_iter().try_fold(1u128, |a, b| a.checked_mul(b)).expect("ratio denominator fits u128");
    u64::try_from(n / d + u128::from(n % d >= d.div_ceil(2))).expect("ratio fits u64")
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Interval {
    pub estimate: u64,
    pub low: u64,
    pub high: u64,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Decision { Faster, Within, Slower, Inconclusive }
impl Interval {
    pub fn decision(self, tolerance_ppm: u64) -> Decision {
        assert!(tolerance_ppm < SCALE as u64);
        let lower = SCALE as u64 - tolerance_ppm;
        let upper = SCALE as u64 + tolerance_ppm;
        if self.low > upper { Decision::Slower }
        else if self.high < lower { Decision::Faster }
        else if self.low >= lower && self.high <= upper { Decision::Within }
        else { Decision::Inconclusive }
    }
}
/// Exact floor(sqrt(value)), avoiding overflow even at u128::MAX.
fn sqrt(value: u128) -> u128 {
    if value < 2 { return value; }
    let mut x = 1u128 << (128 - value.leading_zeros()).div_ceil(2);
    loop {
        let next = (x + value / x) / 2;
        if next >= x { return x; }
        x = next;
    }
}
/// Fixed-budget Student-t interval of the mean block ratio. Fractional
/// endpoints and radius round outward; 1ppm covers block-ratio rounding.
pub fn interval(values: &[u64]) -> Interval {
    assert_eq!(values.len(), BLOCKS, "the declared budget is16 independent blocks");
    let n = BLOCKS as u128;
    let sum: u128 = values.iter().map(|&x| u128::from(x)).sum();
    let squares: u128 = values.iter().map(|&x| u128::from(x).checked_mul(u128::from(x)).unwrap()).try_fold(0u128, |a, b| a.checked_add(b)).expect("squares fit u128");
    let centered = n.checked_mul(squares).unwrap() - sum.checked_mul(sum).unwrap();
    // SE(mean)^2 = (n*sum(x²)-sum(x)²)/(n²*(n-1)); t²=81/4.
    let r2 = centered.checked_mul(81).unwrap().div_ceil(4 * n * n * (n - 1));
    let root = sqrt(r2);
    let radius = root + u128::from(root * root < r2) + 1;
    Interval {
        estimate: u64::try_from((sum + n / 2) / n).unwrap(),
        low: u64::try_from((sum / n).saturating_sub(radius)).unwrap(),
        high: u64::try_from(sum.div_ceil(n).checked_add(radius).unwrap()).unwrap(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn raw_work_weighting_preserves_caller_cost() {
        let mut old = Work::default(); old.add(100, 10); old.add(900, 90);
        let mut new = Work::default(); new.add(120, 10); new.add(1080, 90);
        assert_eq!(ratio(old, new), 1_200_000);
        // Unequal work: totals100ns/10ops against1000ns/100ops are equal.
        assert_eq!(ratio(Work { ns:100,units:10 }, Work { ns:1000,units:100 }), 1_000_000);
    }
    #[test]
    fn every_mode_contributes_continuously() {
        // Fast1ns/slow2ns, 51/49 against49/51 operations:149->151.
        assert_eq!(ratio(Work { ns:149,units:100 },Work { ns:151,units:100 }),1_013_423);
        assert_eq!(interval(&[1_013_423;16]).decision(30_000),Decision::Within);
    }
    #[test]
    fn independently_fixed_interval_anchors() {
        for (r, expected) in [(1_000_000,Decision::Within),(1_060_000,Decision::Slower),(1_120_000,Decision::Slower),(940_000,Decision::Faster),(1_030_000,Decision::Inconclusive)] {
            let i=interval(&[r;16]);assert_eq!(i,Interval {estimate:r,low:r-1,high:r+1});assert_eq!(i.decision(30_000),expected);
        }
        // Alternating ±10000 around1000000: SE=sqrt(100000000/15),
        // 4.5*SE=11618.950...; ceil + rounding1 =>11620.
        let x:Vec<_>=(0..16).map(|i|if i%2==0 {990_000}else {1_010_000}).collect();
        assert_eq!(interval(&x),Interval {estimate:1_000_000,low:988_380,high:1_011_620});
        let variable:Vec<_>=(0..16).map(|i|if i%2==0 {800_000}else {1_300_000}).collect();
        assert_eq!(interval(&variable).decision(30_000),Decision::Inconclusive);
    }
    #[test]
    fn square_root_boundaries() {
        for (a,b) in [(0,0),(1,1),(2,1),(4,2),(15,3),(16,4),(u128::MAX,u64::MAX as u128)] {assert_eq!(sqrt(a),b);}
    }
    #[test]
    #[should_panic(expected="declared budget")]
    fn requires_declared_budget() { interval(&[1_000_000;15]); }
}
