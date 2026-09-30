//! The one place the servil fork and bench-hashes read clocks. Every
//! measurement reads two things through it (AGENTS.md, "Measuring"):
//!
//! - **Wall time**, what a caller waits for: the platform's hardware
//!   counter through `std::time::Instant` ([`now`], [`since_ns`]):
//!   `CLOCK_UPTIME_RAW` on Darwin, `CLOCK_MONOTONIC` on Linux,
//!   `QueryPerformanceCounter` on Windows. A counter read can only
//!   over-count, when the thread is interrupted, which a median absorbs.
//! - **The thread's counts per core kind** ([`Counts`]): cycles,
//!   instructions, and time on performance and efficiency cores, from
//!   Apple's `thread_selfcounts(THSC_TIME_CPI_PER_PERF_LEVEL)`. Cycles
//!   over time is the clock the thread ran at, lower where the core waited
//!   on the SME unit; the split says which kind of core ran it. Other
//!   platforms give none ([`Counts::read`] returns `None`), and results
//!   say so.
//!
//! Thread CPU time (`CLOCK_THREAD_CPUTIME_ID`) is left out: at 1 ms samples
//! it agrees with the counter and adds an accounting layer to reason about;
//! once suspected of inventing speed, it was cleared by experiment, and the
//! moving variable was the core's frequency, which only cycles show
//! (github.com/johnservil/measure-clocks3, CPU-TIME-CLOCKS-AND-FREQUENCY.md).
//!
//! Read wall time alone inside a timed interval and the counts outside it:
//! a counts read is a system call.
//!
//! **Resolution.** The wall clock steps in ticks of the platform's counter:
//! 24 MHz, 41.67 ns, on an Apple M4 Max (every Darwin wall clock and the
//! CPU-time clocks alike; `CLOCK_REALTIME` and `CLOCK_MONOTONIC` in whole
//! microseconds: measure-clocks3, results of December 7, 2025) and in the
//! Linux VM (`arch_timer` at 24 MHz). A reading is a whole number of
//! ticks. So an interval of a few ticks is measured in one of two ways:
//! as a batch of calls long enough that a tick is a small share of it
//! ([`measure`]), or, where every call must be timed alone (a call after
//! a gap), as the sum of many such readings, each starting at a phase
//! against the ticks that nothing correlates with the call
//! ([`measure_after_gaps`]): the sum's rounding averages out. A median or
//! a minimum of single short readings keeps the rounding; take neither.

use std::time::Instant;

pub mod speeds;

/// The wall clock, as reports name it.
#[cfg(target_vendor = "apple")]
pub const WALL_CLOCK: &str = "std::time::Instant → CLOCK_UPTIME_RAW (mach_absolute_time; stops during sleep, no NTP slew)";
#[cfg(all(unix, not(target_vendor = "apple")))]
pub const WALL_CLOCK: &str = "std::time::Instant → CLOCK_MONOTONIC (stops during suspend, NTP slew only)";
#[cfg(windows)]
pub const WALL_CLOCK: &str = "std::time::Instant → QueryPerformanceCounter";
#[cfg(not(any(unix, windows)))]
pub const WALL_CLOCK: &str = "std::time::Instant";

/// A point on the wall clock. Only differences are meaningful.
#[inline(always)]
pub fn now() -> Instant {
    Instant::now()
}

/// Nanoseconds of wall time since `start`.
#[inline(always)]
pub fn since_ns(start: Instant) -> u64 {
    u64::try_from(start.elapsed().as_nanos()).expect("an interval lasts well under 584 years")
}

/// One core kind's share of a thread's counts.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Level {
    pub cycles: u64,
    pub instructions: u64,
    pub time_ns: u64,
}

/// A thread's counts so far, on performance cores (`p`) and efficiency
/// cores (`e`); the difference of two reads covers what ran between them.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Counts {
    pub p: Level,
    pub e: Level,
}

impl Counts {
    /// The calling thread's counts, or `None` where the platform gives none.
    pub fn read() -> Option<Counts> {
        imp::read()
    }

    /// The counts accumulated since `earlier`, a read on the same thread.
    pub fn since(self, earlier: Counts) -> Counts {
        let level = |now: Level, then: Level| Level {
            cycles: now.cycles - then.cycles,
            instructions: now.instructions - then.instructions,
            time_ns: now.time_ns - then.time_ns,
        };
        Counts { p: level(self.p, earlier.p), e: level(self.e, earlier.e) }
    }

    /// These counts and `other`'s together.
    pub fn plus(self, other: Counts) -> Counts {
        let level = |a: Level, b: Level| Level { cycles: a.cycles + b.cycles, instructions: a.instructions + b.instructions, time_ns: a.time_ns + b.time_ns };
        Counts { p: level(self.p, other.p), e: level(self.e, other.e) }
    }

    /// Cycles per microsecond of the thread's time on cores, rounded: the
    /// clock it ran at in MHz (lower where it waited on the SME unit).
    /// Requires some time counted.
    pub fn mhz(&self) -> u64 {
        let ns = self.p.time_ns + self.e.time_ns;
        assert!(ns > 0, "a clock rate needs some time counted");
        ((self.p.cycles + self.e.cycles) * 1000 + ns / 2) / ns
    }

    /// The efficiency cores' share of the thread's time, in percent, rounded.
    /// Requires some time counted.
    pub fn e_percent(&self) -> u64 {
        let ns = self.p.time_ns + self.e.time_ns;
        assert!(ns > 0, "a share needs some time counted");
        (self.e.time_ns * 100 + ns / 2) / ns
    }
}

/// One batch of [`measure`]: `calls` calls in `wall_ns`, with the counts
/// the thread accumulated around it.
#[derive(Clone, Copy, Debug)]
pub struct Batch {
    pub calls: u64,
    pub wall_ns: u64,
    pub counts: Option<Counts>,
}

impl Batch {
    /// "12.3 ns/call, 4390 MHz P" (or "12.3 ns/call, no cycle counts").
    pub fn show(&self) -> String {
        let tenths = (self.wall_ns * 10 + self.calls / 2) / self.calls;
        let rate = match self.counts {
            Some(c) if c.p.time_ns + c.e.time_ns > 0 => {
                let kind = match c.e_percent() {
                    0..=4 => "P".to_owned(),
                    96.. => "E".to_owned(),
                    e => format!("{e}% E"),
                };
                format!("{} MHz {kind}", c.mhz())
            }
            _ => "no cycle counts".to_owned(),
        };
        format!("{}.{} ns/call, {rate}", tenths / 10, tenths % 10)
    }
}

/// `batches` batches of `f`, each about `batch_ns` long (sized by a first,
/// untimed run of that length), in the order taken; wall time inside each
/// batch, the counts around it.
pub fn measure(batches: usize, batch_ns: u64, mut f: impl FnMut()) -> Vec<Batch> {
    assert!(batches > 0 && batch_ns > 0, "a measurement takes at least one batch of some length");
    let started = now();
    let mut calls = 0u64;
    while since_ns(started) < batch_ns {
        f();
        calls += 1;
    }
    (0..batches)
        .map(|_| {
            let before = Counts::read();
            let t = now();
            for _ in 0..calls {
                f();
            }
            let wall_ns = since_ns(t);
            let counts = before.zip(Counts::read()).map(|(before, after)| after.since(before));
            Batch { calls, wall_ns, counts }
        })
        .collect()
}

/// `calls` calls of `f`, each after the calling thread has spent `gap_ns`
/// on other work of its own ([`busy_work`]: integer arithmetic in
/// registers), as a program that hashes now and then between other work
/// calls: the pool's workers have fallen asleep, the caller's core stays
/// busy (Zooko, September 28, 2026: a busy gap for steadier results; an
/// idle core between calls is left unmeasured). One [`Batch`]: the wall
/// time inside each call, summed (see "Resolution" above for why a sum),
/// and the counts around each call alone, summed (their reads outside the
/// timed interval).
pub fn measure_after_gaps(calls: u64, gap_ns: u64, mut f: impl FnMut()) -> Batch {
    assert!(calls > 0, "a measurement takes at least one call");
    let mut wall_ns = 0;
    let mut counts: Option<Counts> = Some(Counts::default());
    for _ in 0..calls {
        busy_work(gap_ns);
        let before = Counts::read();
        let t = now();
        f();
        wall_ns += since_ns(t);
        let call = before.zip(Counts::read()).map(|(before, after)| after.since(before));
        counts = counts.zip(call).map(|(sum, call)| sum.plus(call));
    }
    Batch { calls, wall_ns, counts }
}

/// A measurement with the producer's preparation timed separately.
/// `calls` contains only the hashing calls; `preparation` contains only
/// the writes that produce their input. The gap belongs to neither.
#[derive(Clone, Copy, Debug)]
pub struct PreparedBatch {
    pub calls: Batch,
    pub preparation: Batch,
}

/// Like [`measure_after_gaps`], with a memory-working gap and a producer
/// that writes the input before each call. The caller owns `work` and
/// `input`, keeps them across samples, and chooses `work` larger than the
/// caches whose previous contents the experiment should displace.
///
/// Each gap walks all of `work` at 64-byte intervals, then spends any
/// remaining `gap_ns` on integer work. A complete walk is the minimum:
/// on a machine where it takes longer, the gap lasts longer. Preparation
/// follows the gap, then the call. Both record wall time and thread counts
/// separately, with counts read outside their wall intervals. Requires
/// at least one call and a nonempty work buffer.
pub fn measure_after_gaps_prepared<T: ?Sized>(
    calls: u64,
    gap_ns: u64,
    work: &[u8],
    input: &mut T,
    mut prepare: impl FnMut(&mut T),
    mut f: impl FnMut(&T),
) -> PreparedBatch {
    assert!(calls > 0, "a measurement takes at least one call");
    assert!(!work.is_empty(), "a memory-working gap needs a nonempty work buffer");
    let empty = || Batch { calls, wall_ns: 0, counts: Some(Counts::default()) };
    let mut measured = PreparedBatch { calls: empty(), preparation: empty() };
    for _ in 0..calls {
        let started = now();
        let mut sum = 0u64;
        for &byte in std::hint::black_box(work).iter().step_by(64) {
            sum = sum.wrapping_add(u64::from(byte));
        }
        std::hint::black_box(sum);
        busy_work(gap_ns.saturating_sub(since_ns(started)));

        let before = Counts::read();
        let t = now();
        prepare(input);
        measured.preparation.wall_ns += since_ns(t);
        let counts = before.zip(Counts::read()).map(|(before, after)| after.since(before));
        measured.preparation.counts = measured.preparation.counts.zip(counts).map(|(sum, call)| sum.plus(call));

        let before = Counts::read();
        let t = now();
        f(input);
        measured.calls.wall_ns += since_ns(t);
        let counts = before.zip(Counts::read()).map(|(before, after)| after.since(before));
        measured.calls.counts = measured.calls.counts.zip(counts).map(|(sum, call)| sum.plus(call));
    }
    measured
}

/// Keep the calling thread busy for `ns` of wall time with integer
/// arithmetic in registers (a multiply-add chain), touching no memory: the
/// program's own work between calls, which leaves the caches as the call
/// last left them.
pub fn busy_work(ns: u64) {
    let started = now();
    let mut x = 1u64;
    while since_ns(started) < ns {
        for _ in 0..256 {
            x = x.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        }
        x = std::hint::black_box(x);
    }
}

/// The CPU time this process has used, all its threads together, in
/// nanoseconds: for telling this process's share of the machine's busy
/// time from other programs' (bench-hashes' load report), never for
/// timing a measurement. Zero where the platform has no such clock.
pub fn process_cpu_ns() -> u64 {
    #[cfg(unix)]
    {
        #[repr(C)]
        struct Timespec {
            tv_sec: i64,
            tv_nsec: i64,
        }
        unsafe extern "C" {
            fn clock_gettime(clock_id: i32, tp: *mut Timespec) -> i32;
        }
        // CLOCK_PROCESS_CPUTIME_ID
        const CLOCK: i32 = if cfg!(target_vendor = "apple") { 12 } else { 2 };
        let mut ts = Timespec { tv_sec: 0, tv_nsec: 0 };
        // Sound: `ts` is writable.
        assert_eq!(unsafe { clock_gettime(CLOCK, &mut ts) }, 0, "clock_gettime(CLOCK_PROCESS_CPUTIME_ID)");
        ts.tv_sec as u64 * 1_000_000_000 + ts.tv_nsec as u64
    }
    #[cfg(not(unix))]
    {
        0
    }
}

/// The energy this process has used so far, all its threads together, in
/// nanojoules, where the platform counts it (macOS: the kernel's estimate,
/// `proc_pid_rusage` RUSAGE_INFO_V6 `ri_energy_nj`; it reads sleep as
/// under 0.01 W and a scalar spin as about 3 W on an M4 Max P-core,
/// NOTES-servil.md "Energy per byte"; whether it counts the SME unit's own
/// power is unknown). None elsewhere. The kernel credits a thread's energy
/// late, at its next block or switch: read after the measured threads have
/// slept (10 ms: a 64 MiB hash then reads within 7%; read at once, a third
/// less, and scattered). Not yet validated for the benchmark's energy
/// cells (docs/api-design.md, **Q**).
pub fn process_energy_nj() -> Option<u64> {
    imp::process_energy_nj()
}

/// macOS QoS classes: user-interactive runs on P-cores, background on E-cores.
pub const USER_INTERACTIVE: u32 = 0x21;
pub const BACKGROUND: u32 = 0x09;

/// Put the calling thread in QoS class `class` (macOS; elsewhere nothing).
pub fn set_qos(class: u32) {
    imp::set_qos(class)
}

#[cfg(target_vendor = "apple")]
mod imp {
    use super::{Counts, Level};
    use std::sync::OnceLock;

    #[repr(C)]
    #[derive(Clone, Copy, Default)]
    struct ThscTimeCpi {
        instructions: u64,
        cycles: u64,
        user_time_mach: u64,
        system_time_mach: u64,
    }
    #[repr(C)]
    struct MachTimebaseInfo {
        numer: u32,
        denom: u32,
    }
    unsafe extern "C" {
        fn thread_selfcounts(kind: u32, dst: *mut std::ffi::c_void, size: usize) -> i32;
        fn mach_timebase_info(info: *mut MachTimebaseInfo) -> i32;
        fn pthread_set_qos_class_self_np(qos: u32, relpri: i32) -> i32;
    }
    const THSC_TIME_CPI_PER_PERF_LEVEL: u32 = 4;

    /// hw.nperflevels is 2 on every Apple silicon Mac: index 0 P, 1 E.
    fn levels() -> Option<[ThscTimeCpi; 2]> {
        let mut levels = [ThscTimeCpi::default(); 2];
        // Sound: `levels` is writable for the size passed.
        let rc = unsafe {
            thread_selfcounts(THSC_TIME_CPI_PER_PERF_LEVEL, levels.as_mut_ptr().cast(), std::mem::size_of_val(&levels))
        };
        (rc == 0).then_some(levels)
    }

    pub fn read() -> Option<Counts> {
        // (numer, denom) for mach ticks to ns, and whether the call works here.
        static SETUP: OnceLock<Option<(u64, u64)>> = OnceLock::new();
        let (numer, denom) = (*SETUP.get_or_init(|| {
            let mut info = MachTimebaseInfo { numer: 0, denom: 0 };
            // Sound: `info` is writable.
            let ok = unsafe { mach_timebase_info(&mut info) } == 0 && info.denom != 0 && levels().is_some();
            ok.then_some((u64::from(info.numer), u64::from(info.denom)))
        }))?;
        let levels = levels().expect("thread_selfcounts failed after succeeding once");
        let level = |l: ThscTimeCpi| Level {
            cycles: l.cycles,
            instructions: l.instructions,
            time_ns: (l.user_time_mach + l.system_time_mach) * numer / denom,
        };
        Some(Counts { p: level(levels[0]), e: level(levels[1]) })
    }

    pub fn set_qos(class: u32) {
        // Sound: a plain call on the calling thread.
        assert_eq!(unsafe { pthread_set_qos_class_self_np(class, 0) }, 0, "pthread_set_qos_class_self_np");
    }

    pub fn process_energy_nj() -> Option<u64> {
        unsafe extern "C" {
            fn proc_pid_rusage(pid: i32, flavor: i32, buffer: *mut u64) -> i32;
            fn getpid() -> i32;
        }
        // rusage_info_v6 as u64 words (<sys/resource.h>): ri_uuid (2),
        // ri_user_time at 2, ..., ri_energy_nj at 42 (room to spare).
        const RUSAGE_INFO_V6: i32 = 6;
        let mut words = [0u64; 128];
        // Sound: `words` is writable and longer than rusage_info_v6.
        (unsafe { proc_pid_rusage(getpid(), RUSAGE_INFO_V6, words.as_mut_ptr()) } == 0).then_some(words[42])
    }
}

#[cfg(not(target_vendor = "apple"))]
mod imp {
    pub fn read() -> Option<super::Counts> {
        None
    }

    pub fn set_qos(_class: u32) {}

    pub fn process_energy_nj() -> Option<u64> {
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_measurement_counts_its_calls_and_time() {
        let batches = measure(3, 100_000, || {
            std::hint::black_box((0..100u64).sum::<u64>());
        });
        assert_eq!(batches.len(), 3);
        for b in &batches {
            assert!(b.calls > 0 && b.wall_ns > 0, "{b:?}");
            assert!(b.show().contains("ns/call"));
        }
    }

    #[test]
    fn calls_after_gaps_sum_their_own_time_alone() {
        let mut calls = 0;
        let b = measure_after_gaps(5, 1_000_000, || {
            calls += 1;
            std::hint::black_box((0..100u64).sum::<u64>());
        });
        assert_eq!((calls, b.calls), (5, 5));
        assert!(b.wall_ns > 0 && b.wall_ns < 5_000_000, "the sleeps stay out of the sum: {b:?}");
    }

    #[test]
    fn counts_subtract_and_rate() {
        let later = Counts { p: Level { cycles: 4_400, instructions: 9_000, time_ns: 1_000 }, e: Level::default() };
        let d = later.since(Counts::default());
        assert_eq!((d.mhz(), d.e_percent()), (4_400, 0));
    }
    #[test]
    fn prepared_calls_follow_their_writes_and_exclude_gaps() {
        let mut input = 0;
        let mut observed = Vec::new();
        let started = now();
        let measured = measure_after_gaps_prepared(3, 1_000_000, &[7; 128], &mut input,
            |input| { *input += 1; busy_work(100_000); },
            |input| { observed.push(*input); busy_work(50_000); });
        assert_eq!(observed, [1, 2, 3]);
        assert_eq!(measured.calls.calls, 3);
        assert_eq!(measured.preparation.calls, 3);
        assert!(measured.calls.wall_ns >= 150_000);
        assert!(measured.preparation.wall_ns >= 300_000);
        assert!(since_ns(started) >= 3_000_000 + measured.calls.wall_ns + measured.preparation.wall_ns);
    }

    #[test]
    #[should_panic(expected = "nonempty work buffer")]
    fn prepared_calls_require_work() {
        measure_after_gaps_prepared(1, 0, &[], &mut (), |_| {}, |_| {});
    }

}
