//! The CPU's energy (RAPL), for a measurement's energy beside its wall
//! time: the whole package's and its cores' joules since an arbitrary
//! start, through perf's `power` PMU (Linux x86-64; the counters
//! `/sys/class/powercap` shows, readable where perf is, for instance at
//! perf_event_paranoid 0). Package-wide: other programs' work counts too,
//! so energy describes a run only on an otherwise quiet machine (the load
//! clocks::load records says whether it was). Where the PMU is absent or
//! the kernel refuses, there is none ([`read`] returns `None`).

/// Energy so far, in microjoules: the CPU package's, and its cores' (a
/// part of the package's).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Energy {
    pub package_uj: u64,
    pub cores_uj: u64,
}

impl Energy {
    /// The energy used since `earlier`, an earlier read.
    pub fn since(self, earlier: Energy) -> Energy {
        Energy { package_uj: self.package_uj - earlier.package_uj, cores_uj: self.cores_uj - earlier.cores_uj }
    }

    /// Average power over `ns` nanoseconds, in milliwatts (package, cores).
    /// Requires `ns > 0`.
    pub fn milliwatts(self, ns: u64) -> (u64, u64) {
        assert!(ns > 0, "power needs some time");
        let mw = |uj: u64| (u128::from(uj) * 1_000_000 / u128::from(ns)) as u64;
        (mw(self.package_uj), mw(self.cores_uj))
    }
}

/// The energy so far, or `None` where it cannot be read here.
pub fn read() -> Option<Energy> {
    imp::read()
}

#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
mod imp {
    use super::Energy;
    use crate::linux_counts::{perf_open, read_fd, Attr};
    use std::os::fd::{AsRawFd, OwnedFd};
    use std::sync::OnceLock;

    /// One RAPL counter: its descriptor, and its unit as an exact decimal
    /// (count times `mantissa` times 10^`exponent` joules).
    struct Counter {
        fd: OwnedFd,
        mantissa: u128,
        exponent: i32,
    }

    /// "2.3283064365386962890625e-10" as (23283064365386962890625, -32):
    /// the scale perf gives, exactly. Requires decimal digits, one point at
    /// most, and an optional exponent.
    pub(super) fn parse_scale(text: &str) -> (u128, i32) {
        let (digits, exponent) = text.trim().split_once(['e', 'E']).map_or((text.trim(), 0), |(d, e)| (d, e.parse::<i32>().expect("a scale's exponent")));
        let (whole, fraction) = digits.split_once('.').unwrap_or((digits, ""));
        let mantissa = format!("{whole}{fraction}").parse::<u128>().expect("a scale's digits");
        (mantissa, exponent - fraction.len() as i32)
    }

    impl Counter {
        fn open(pmu: u32, cpu: i32, name: &str) -> Option<Counter> {
            let dir = "/sys/bus/event_source/devices/power/events";
            let event = std::fs::read_to_string(format!("{dir}/{name}")).ok()?;
            let config = u64::from_str_radix(event.trim().strip_prefix("event=0x")?, 16).ok()?;
            let (mantissa, exponent) = parse_scale(&std::fs::read_to_string(format!("{dir}/{name}.scale")).ok()?);
            let a = Attr {
                kind: pmu,
                size: std::mem::size_of::<Attr>() as u32,
                config,
                sample_period: 0,
                sample_type: 0,
                read_format: 0,
                flags: 0,
                reserved: [0; 2],
            };
            // pid -1 on one CPU: the whole package's counter.
            let fd = perf_open(&a, -1, cpu, -1)?;
            Some(Counter { fd, mantissa, exponent })
        }

        fn microjoules(&self) -> u64 {
            let mut count = 0u64;
            // Sound: `count` is writable for its size.
            let n = unsafe { read_fd(self.fd.as_raw_fd(), (&mut count as *mut u64).cast(), 8) };
            assert_eq!(n, 8, "a RAPL counter read gives its count");
            let scaled = u128::from(count) * self.mantissa;
            let exponent = self.exponent + 6;
            let uj = if exponent >= 0 { scaled * 10u128.pow(exponent as u32) } else { scaled / 10u128.pow((-exponent) as u32) };
            u64::try_from(uj).expect("microjoules fit in 64 bits")
        }
    }

    pub fn read() -> Option<Energy> {
        static COUNTERS: OnceLock<Option<[Counter; 2]>> = OnceLock::new();
        let [package, cores] = COUNTERS
            .get_or_init(|| {
                let dir = "/sys/bus/event_source/devices/power";
                let pmu = std::fs::read_to_string(format!("{dir}/type")).ok()?.trim().parse().ok()?;
                let cpu = std::fs::read_to_string(format!("{dir}/cpumask")).ok()?.trim().split([',', '-']).next()?.parse().ok()?;
                Some([Counter::open(pmu, cpu, "energy-pkg")?, Counter::open(pmu, cpu, "energy-cores")?])
            })
            .as_ref()?;
        Some(Energy { package_uj: package.microjoules(), cores_uj: cores.microjoules() })
    }
}

#[cfg(not(all(target_os = "linux", target_arch = "x86_64")))]
mod imp {
    pub fn read() -> Option<super::Energy> {
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    #[test]
    fn scales_parse_exactly() {
        assert_eq!(imp::parse_scale("2.3283064365386962890625e-10\n"), (23283064365386962890625, -32));
        assert_eq!(imp::parse_scale("1.52587890625e-5"), (152587890625, -16));
        assert_eq!(imp::parse_scale("1"), (1, 0));
    }

    #[test]
    fn power_from_energy_and_time() {
        let e = Energy { package_uj: 30_000_000, cores_uj: 20_000_000 }.since(Energy::default());
        assert_eq!(e.milliwatts(1_000_000_000), (30_000, 20_000));
    }

    /// Where perf allows it: a second of busy work reads between 1 and 500
    /// W for the package, the cores a part of it.
    #[test]
    #[ignore = "needs perf's power PMU readable here"]
    fn a_second_of_work_reads_plausible_power() {
        let before = read().expect("RAPL readable here");
        let started = crate::now();
        crate::busy_work(1_000_000_000);
        let e = read().unwrap().since(before);
        let (pkg, cores) = e.milliwatts(crate::since_ns(started));
        println!("package {pkg} mW, cores {cores} mW");
        assert!((1_000..500_000).contains(&pkg) && cores <= pkg);
    }
}
