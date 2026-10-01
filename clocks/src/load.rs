//! Other programs' load on the machine while this process measures,
//! recorded by every measurement in this crate, with nothing to call.
//!
//! **What it counts.** The OS counts the CPU time every CPU spent busy;
//! this process counts its own (every thread). Their difference over a
//! stretch of wall time is how many CPUs other programs kept busy, in
//! milli-CPUs (1000: one CPU busy throughout). On Linux the OS also
//! counts steal time, which a hypervisor took from a VM's CPUs for other
//! work on the host, load a guest sees no other way.
//!
//! **When it reads.** A reading costs system calls, which take far longer
//! than a short timed call, so it never happens inside a timed interval
//! or per call. Each measurement in this crate calls [`tick`] outside its
//! timed intervals, between batches and before each gap; a tick reads
//! the machine only once a window of [`WINDOW_NS`] has passed since the
//! last reading, and otherwise costs one wall-clock read and one atomic
//! load. Measured in the Linux VM (`reading_cost` below, September 30,
//! 2026): a reading 8.6 us, a tick between readings 18 ns. A program
//! that times with [`crate::now`] directly calls [`tick`] itself, between
//! samples.
//!
//! **Placing samples in windows.** Every [`crate::Batch`] records when it
//! started, as [`now_ns`] (nanoseconds since this process's first
//! measurement), on the same scale as each [`Window`]'s bounds.
//!
//! **Resolution.** Both OSes count machine CPU time in ticks of 10 ms per
//! CPU. A window's reading therefore carries an error of up to a tick per
//! CPU: at most 0.16 CPUs over a 1 s window on 16 CPUs, well under
//! [`BUSY_MILLI_CPUS`].
//!
//! A window whose other load or steal reaches [`BUSY_MILLI_CPUS`] is
//! busy: when one closes, this module says so on stderr, so every probe
//! and benchmark shows it with no code of its own; [`windows`] gives
//! every window for reports and samples files.

use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Mutex, OnceLock};
use std::time::Instant;

/// A window's least length: a reading ends it once this much wall time
/// has passed since the one before.
pub const WINDOW_NS: u64 = 1_000_000_000;
/// Other programs (or a hypervisor) keeping a whole CPU busy make a
/// window busy: a core taken from the shared scenario and from the
/// multithreaded contenders, which use every CPU. An M4 Max running a
/// Linux VM beside the benchmark keeps 0.40-0.56 CPUs busy, with results
/// level with a quieter run's (bench-hashes NOTES).
pub const BUSY_MILLI_CPUS: u64 = 1000;

/// One stretch of wall time and the load other programs put on the
/// machine in it. Bounds are [`now_ns`] values.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Window {
    pub start_ns: u64,
    pub end_ns: u64,
    /// CPUs other programs kept busy, in milli-CPUs.
    pub other_milli_cpus: u64,
    /// CPUs a hypervisor withheld, in milli-CPUs (0 where none is counted).
    pub steal_milli_cpus: u64,
}

impl Window {
    /// Whether other programs or a hypervisor took a CPU or more.
    pub fn busy(&self) -> bool {
        self.other_milli_cpus.max(self.steal_milli_cpus) >= BUSY_MILLI_CPUS
    }

    /// Whether the window holds the instant `at_ns` (a [`now_ns`] value).
    pub fn holds(&self, at_ns: u64) -> bool {
        self.start_ns <= at_ns && at_ns < self.end_ns
    }
}

/// Nanoseconds of wall time since this process's first measurement (its
/// first call of this function, [`tick`], or a measurement in this crate).
pub fn now_ns() -> u64 {
    static ORIGIN: OnceLock<Instant> = OnceLock::new();
    crate::since_ns(*ORIGIN.get_or_init(Instant::now))
}

/// A machine reading: when, the machine's CPU times, this process's.
#[derive(Clone, Copy)]
struct Reading {
    at_ns: u64,
    machine: imp::CpuTimes,
    own_ns: u64,
}

impl Reading {
    fn take() -> Option<Reading> {
        let at_ns = now_ns();
        let machine = imp::read()?;
        Some(Reading { at_ns, machine, own_ns: crate::process_cpu_ns() })
    }
}

/// The window between two readings.
fn between(from: Reading, to: Reading) -> Window {
    assert!(to.at_ns > from.at_ns, "a window lasts some time");
    let (busy_ns, steal_ns) = imp::busy_and_steal_ns(from.machine, to.machine);
    let milli = |ns: u64| u64::try_from(u128::from(ns) * 1000 / u128::from(to.at_ns - from.at_ns)).expect("load fits in u64");
    // Tick rounding can put the machine's busy time a little under this
    // process's own; that reads as none.
    Window {
        start_ns: from.at_ns,
        end_ns: to.at_ns,
        other_milli_cpus: milli(busy_ns.saturating_sub(to.own_ns - from.own_ns)),
        steal_milli_cpus: milli(steal_ns),
    }
}

struct State {
    last: Option<Reading>,
    // The baseline of the last closed window, retained to observe a short
    // final tail over a sufficiently long interval rather than a tiny one.
    previous: Option<Reading>,
    windows: Vec<Window>,
}

static STATE: Mutex<State> = Mutex::new(State { last: None, previous: None, windows: Vec::new() });
/// The [`now_ns`] at which the next tick reads the machine; u64::MAX where
/// the platform gives no CPU times.
static DUE_NS: AtomicU64 = AtomicU64::new(0);

/// Close the running window if `least_ns` have passed since the last
/// reading (take the first reading when there is none).
fn close(state: &mut State, least_ns: u64, finish: bool) {
    let Some(reading) = Reading::take() else {
        DUE_NS.store(u64::MAX, Ordering::Relaxed);
        return;
    };
    if record(state, reading, least_ns, finish) {
        DUE_NS.store(reading.at_ns + WINDOW_NS, Ordering::Relaxed);
    }
}

/// Record an observation; return whether it advanced the baseline. This
/// isolated state transition also accepts fixed OS-counter fixtures in tests.
fn record(state: &mut State, reading: Reading, least_ns: u64, finish: bool) -> bool {
    if let Some(last) = state.last {
        assert!(reading.at_ns >= last.at_ns, "load readings move forward");
    }
    let window = match state.last {
        Some(last) if reading.at_ns - last.at_ns < least_ns => {
            if !finish {
                return false;
            }
            let Some(previous) = state.previous else { return false };
            let last_window = state.windows.last_mut().expect("a previous reading belongs to a closed window");
            if last_window.busy() {
                // Averaging a quiet tail into a busy observation could
                // erase it. Retain that finding; the run is already busy.
                return false;
            }
            let window = between(previous, reading);
            *last_window = window;
            // Seal this window after one extension. Frequent snapshots
            // must not keep widening its average and hide later bursts.
            state.previous = None;
            Some(window)
        }
        Some(last) => {
            let window = between(last, reading);
            state.previous = Some(last);
            state.windows.push(window);
            Some(window)
        }
        None => None,
    };
    if let Some(window) = window {
        if window.busy() {
            eprintln!("clocks: {}; measurements in that time may read slower than this machine runs", describe_window(&window));
        }
    }
    state.last = Some(reading);
    true
}

/// Read the machine once a window has passed since the last reading;
/// otherwise nothing. Call it outside timed intervals: every measurement
/// in this crate does. Another thread's tick in progress makes this one
/// return at once.
pub fn tick() {
    if now_ns() < DUE_NS.load(Ordering::Relaxed) {
        return;
    }
    if let Ok(mut state) = STATE.try_lock() {
        close(&mut state, WINDOW_NS, false);
    }
}

/// Every window so far, in order. A final interval of half a window or
/// more closes normally. A shorter tail extends the last quiet window
/// once from its original counter baseline, preserving the minimum duration.
/// Later work starts a new interval; repeated snapshots cannot keep widening
/// an old average. A busy last window stays intact: averaging it with a quiet tail must
/// not erase a busy finding. Empty when counters are unavailable or the
/// process has not yet supplied half a window of observation.
pub fn windows() -> Vec<Window> {
    let mut state = STATE.lock().expect("load state lock");
    if DUE_NS.load(Ordering::Relaxed) != u64::MAX {
        close(&mut state, WINDOW_NS / 2, true);
    }
    state.windows.clone()
}

/// Milli-CPUs as "1.23".
pub fn cpus(milli: u64) -> String {
    let hundredths = (milli + 5) / 10;
    format!("{}.{:02}", hundredths / 100, hundredths % 100)
}

/// Nanoseconds as seconds with one decimal: "12.3".
fn seconds(ns: u64) -> String {
    let tenths = (ns + 50_000_000) / 100_000_000;
    format!("{}.{}", tenths / 10, tenths % 10)
}

/// "other programs kept 1.40 CPUs busy from 12.0 s to 13.0 s" (with the
/// hypervisor's share where it took any).
pub fn describe_window(window: &Window) -> String {
    let mut line = format!("other programs kept {} CPUs busy from {} s to {} s",
        cpus(window.other_milli_cpus), seconds(window.start_ns), seconds(window.end_ns));
    if window.steal_milli_cpus > 0 {
        line += &format!(", the hypervisor withheld {} CPUs", cpus(window.steal_milli_cpus));
    }
    line
}

/// One line for readers about `windows`: "quiet: other programs kept 0.02
/// CPUs busy on average, 0.10 in the busiest second", or "busy: ..., busy
/// in 2 of 40 windows (12.0-13.0 s, 20.1-21.1 s)". Empty windows report
/// no observation: the process may be too short or counters unavailable.
pub fn describe(windows: &[Window]) -> String {
    let Some(first) = windows.first() else { return "not measured: no load window (too short or counters unavailable)".to_owned() };
    let span = windows.last().unwrap().end_ns - first.start_ns;
    let weighted = |pick: fn(&Window) -> u64| {
        let sum: u128 = windows.iter().map(|w| u128::from(pick(w)) * u128::from(w.end_ns - w.start_ns)).sum();
        u64::try_from((sum + u128::from(span) / 2) / u128::from(span)).expect("load fits in u64")
    };
    let busy: Vec<&Window> = windows.iter().filter(|w| w.busy()).collect();
    let mut line = format!("{}: other programs kept {} CPUs busy on average, {} in the busiest window",
        if busy.is_empty() { "quiet" } else { "busy" },
        cpus(weighted(|w| w.other_milli_cpus)),
        cpus(windows.iter().map(|w| w.other_milli_cpus).max().unwrap()));
    let steal = windows.iter().map(|w| w.steal_milli_cpus).max().unwrap();
    if steal > 0 {
        line += &format!("; the hypervisor withheld {} CPUs on average, {} at most", cpus(weighted(|w| w.steal_milli_cpus)), cpus(steal));
    }
    if !busy.is_empty() {
        let list: Vec<String> = busy.iter().map(|w| format!("{}-{} s", seconds(w.start_ns), seconds(w.end_ns))).collect();
        line += &format!("; busy in {} of {} windows ({})", busy.len(), windows.len(), list.join(", "));
    }
    line
}

#[cfg(target_os = "linux")]
mod imp {
    /// Machine CPU times since boot in ticks, all CPUs summed: busy (not
    /// idle, not waiting on I/O) and stolen by a hypervisor.
    #[derive(Clone, Copy)]
    pub struct CpuTimes {
        pub(super) busy: u64,
        pub(super) steal: u64,
    }

    fn ticks_per_second() -> u64 {
        unsafe extern "C" {
            fn sysconf(name: i32) -> i64;
        }
        const SC_CLK_TCK: i32 = 2;
        // Sound: a plain query.
        u64::try_from(unsafe { sysconf(SC_CLK_TCK) }).expect("sysconf(_SC_CLK_TCK) is positive")
    }

    pub fn read() -> Option<CpuTimes> {
        let stat = std::fs::read_to_string("/proc/stat").ok()?;
        let fields: Vec<u64> = stat.lines().next()?.strip_prefix("cpu ")?.split_whitespace()
            .map(|field| field.parse().expect("/proc/stat counts are integers")).collect();
        // user nice system idle iowait irq softirq steal (guest time is inside user).
        assert!(fields.len() >= 8, "/proc/stat's cpu line has at least eight fields");
        Some(CpuTimes { busy: fields[0] + fields[1] + fields[2] + fields[5] + fields[6], steal: fields[7] })
    }

    pub fn busy_and_steal_ns(from: CpuTimes, to: CpuTimes) -> (u64, u64) {
        let ns = |ticks: u64| ticks * 1_000_000_000 / ticks_per_second();
        (ns(to.busy - from.busy), ns(to.steal - from.steal))
    }
}

#[cfg(target_vendor = "apple")]
mod imp {
    /// host_statistics(HOST_CPU_LOAD_INFO): user, system, idle, nice ticks,
    /// all CPUs summed, each a 32-bit counter that wraps.
    #[derive(Clone, Copy)]
    pub struct CpuTimes(pub(super) [u32; 4]);

    unsafe extern "C" {
        fn mach_host_self() -> u32;
        fn host_statistics(host: u32, flavor: i32, info: *mut u32, count: *mut u32) -> i32;
        fn sysconf(name: i32) -> i64;
    }

    pub fn read() -> Option<CpuTimes> {
        const HOST_CPU_LOAD_INFO: i32 = 3;
        let mut ticks = [0u32; 4];
        let mut count = 4u32;
        // Sound: `ticks` is writable for `count` words.
        let rc = unsafe { host_statistics(mach_host_self(), HOST_CPU_LOAD_INFO, ticks.as_mut_ptr(), &mut count) };
        (rc == 0 && count == 4).then_some(CpuTimes(ticks))
    }

    pub fn busy_and_steal_ns(from: CpuTimes, to: CpuTimes) -> (u64, u64) {
        const SC_CLK_TCK: i32 = 3;
        // Sound: a plain query.
        let per_second = u64::try_from(unsafe { sysconf(SC_CLK_TCK) }).expect("sysconf(_SC_CLK_TCK) is positive");
        // Each counter wraps on its own: difference each, then sum.
        let busy: u64 = [0, 1, 3].iter().map(|&i| u64::from(to.0[i].wrapping_sub(from.0[i]))).sum();
        (busy * 1_000_000_000 / per_second, 0)
    }
}

#[cfg(not(any(target_os = "linux", target_vendor = "apple")))]
mod imp {
    #[derive(Clone, Copy)]
    pub struct CpuTimes;

    pub fn read() -> Option<CpuTimes> {
        None
    }

    pub fn busy_and_steal_ns(_: CpuTimes, _: CpuTimes) -> (u64, u64) {
        (0, 0)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn window(start_ns: u64, end_ns: u64, other_milli_cpus: u64, steal_milli_cpus: u64) -> Window {
        Window { start_ns, end_ns, other_milli_cpus, steal_milli_cpus }
    }

    #[test]
    fn busy_starts_at_one_cpu_of_other_load_or_steal() {
        assert!(!window(0, 1, 999, 999).busy());
        assert!(window(0, 1, 1000, 0).busy());
        assert!(window(0, 1, 0, 1000).busy());
    }

    #[test]
    fn a_window_holds_its_start_and_not_its_end() {
        let w = window(10, 20, 0, 0);
        assert!(w.holds(10) && w.holds(19) && !w.holds(20) && !w.holds(9));
    }

    #[test]
    fn descriptions_weigh_windows_by_length_and_name_busy_ones() {
        assert_eq!(describe(&[]), "not measured: no load window (too short or counters unavailable)");
        let quiet = [window(0, 1_000_000_000, 100, 0), window(1_000_000_000, 4_000_000_000, 500, 0)];
        assert_eq!(describe(&quiet), "quiet: other programs kept 0.40 CPUs busy on average, 0.50 in the busiest window");
        let busy = [window(0, 1_000_000_000, 1400, 0), window(1_000_000_000, 2_000_000_000, 200, 300)];
        assert_eq!(describe(&busy), "busy: other programs kept 0.80 CPUs busy on average, 1.40 in the busiest window; \
            the hypervisor withheld 0.15 CPUs on average, 0.30 at most; busy in 1 of 2 windows (0.0-1.0 s)");
    }

    #[cfg(any(target_os = "linux", target_vendor = "apple"))]
    mod final_windows {
        use super::*;

        // The supported platforms' CPU-time counters count 10 ms ticks.
        // Fixtures exercise the production counter subtraction and rule.
        fn reading(at_ns: u64, busy_ticks: u64, own_ns: u64) -> Reading {
            #[cfg(target_os = "linux")]
            let machine = imp::CpuTimes { busy: busy_ticks, steal: 0 };
            #[cfg(target_vendor = "apple")]
            let machine = imp::CpuTimes([u32::try_from(busy_ticks).unwrap(), 0, 0, 0]);
            Reading { at_ns, machine, own_ns }
        }

        fn initial() -> State {
            let mut state = State { last: None, previous: None, windows: Vec::new() };
            assert!(record(&mut state, reading(0, 0, 0), WINDOW_NS, false));
            state
        }

        #[test]
        fn a_short_process_remains_unobserved() {
            let mut state = initial();
            assert!(!record(&mut state, reading(300_000_000, 0, 0), WINDOW_NS / 2, true));
            assert!(state.windows.is_empty());
            assert_eq!(state.last.unwrap().at_ns, 0);
        }

        #[test]
        fn a_quiet_tail_uses_the_original_counter_baseline() {
            let mut state = initial();
            assert!(record(&mut state, reading(1_000_000_000, 60, 400_000_000), WINDOW_NS, false));
            assert_eq!(state.windows[0].other_milli_cpus, 200);
            assert!(record(&mut state, reading(1_200_000_000, 72, 500_000_000), WINDOW_NS / 2, true));
            assert_eq!(state.windows, vec![window(0, 1_200_000_000, 183, 0)]);
            assert!(state.previous.is_none(), "the extension consumes its original baseline");
        }

        #[test]
        fn a_busy_tail_can_make_the_extended_window_busy() {
            let mut state = initial();
            record(&mut state, reading(1_000_000_000, 20, 0), WINDOW_NS, false);
            assert!(!state.windows[0].busy());
            record(&mut state, reading(1_200_000_000, 180, 0), WINDOW_NS / 2, true);
            assert_eq!(state.windows, vec![window(0, 1_200_000_000, 1500, 0)]);
            assert!(state.windows[0].busy());
        }

        #[test]
        fn averaging_a_quiet_tail_cannot_erase_a_busy_window() {
            let mut state = initial();
            record(&mut state, reading(1_000_000_000, 110, 0), WINDOW_NS, false);
            let before = state.windows.clone();
            assert!(before[0].busy());
            let tail = reading(1_400_000_000, 110, 0);
            assert!(!between(state.previous.unwrap(), tail).busy(), "the naive merge would erase busy");
            assert!(!record(&mut state, tail, WINDOW_NS / 2, true));
            assert_eq!(state.windows, before);
            assert_eq!(state.last.unwrap().at_ns, 1_000_000_000);
        }

        #[test]
        fn earlier_busy_windows_stay_intact_when_the_last_quiet_one_extends() {
            let mut state = initial();
            record(&mut state, reading(1_000_000_000, 110, 0), WINDOW_NS, false);
            record(&mut state, reading(2_000_000_000, 130, 0), WINDOW_NS, false);
            let first = state.windows[0];
            assert!(first.busy());
            record(&mut state, reading(2_200_000_000, 135, 0), WINDOW_NS / 2, true);
            assert_eq!(state.windows[0], first);
            assert_eq!(state.windows[1], window(1_000_000_000, 2_200_000_000, 208, 0));
        }

        #[test]
        fn repeated_snapshots_and_later_ticks_keep_windows_contiguous() {
            let mut state = initial();
            record(&mut state, reading(1_000_000_000, 20, 0), WINDOW_NS, false);
            record(&mut state, reading(1_200_000_000, 24, 0), WINDOW_NS / 2, true);
            record(&mut state, reading(1_300_000_000, 26, 0), WINDOW_NS / 2, true);
            assert_eq!(state.windows.len(), 1);
            record(&mut state, reading(2_300_000_000, 46, 0), WINDOW_NS, false);
            record(&mut state, reading(2_400_000_000, 48, 0), WINDOW_NS / 2, true);
            assert_eq!(state.windows, vec![window(0, 1_200_000_000, 200, 0), window(1_200_000_000, 2_400_000_000, 200, 0)]);
        }

        #[test]
        fn frequent_snapshots_do_not_hide_a_half_second_busy_burst() {
            let mut state = initial();
            record(&mut state, reading(1_000_000_000, 0, 0), WINDOW_NS, false);
            record(&mut state, reading(1_100_000_000, 0, 0), WINDOW_NS / 2, true);
            for i in 1..=5 {
                // Two CPUs busy from 1.1 s to 1.6 s, while snapshots arrive
                // every 0.1 s. An indefinitely growing average hides it.
                record(&mut state, reading(1_100_000_000 + i * 100_000_000, i * 20, 0), WINDOW_NS / 2, true);
            }
            assert!(state.windows.iter().any(Window::busy), "the sufficiently long busy observation stays visible");
            assert_eq!(state.windows[1], window(1_100_000_000, 1_600_000_000, 2000, 0));
        }

        #[test]
        fn a_long_final_tail_closes_its_own_window() {
            let mut state = initial();
            record(&mut state, reading(1_000_000_000, 20, 0), WINDOW_NS, false);
            record(&mut state, reading(1_600_000_000, 32, 0), WINDOW_NS / 2, true);
            assert_eq!(state.windows, vec![window(0, 1_000_000_000, 200, 0), window(1_000_000_000, 1_600_000_000, 200, 0)]);
        }

        #[test]
        fn a_tick_keeps_the_existing_minimum_duration() {
            let mut state = initial();
            record(&mut state, reading(1_000_000_000, 20, 0), WINDOW_NS, false);
            let before = state.windows.clone();
            assert!(!record(&mut state, reading(1_200_000_000, 24, 0), WINDOW_NS, false));
            assert_eq!(state.windows, before);
        }
    }

    #[cfg(target_vendor = "apple")]
    #[test]
    fn apple_counters_wrap_one_by_one() {
        let from = imp::CpuTimes([u32::MAX - 9, 0, 0, 5]);
        let to = imp::CpuTimes([10, 20, 1000, 5]);
        let (busy, _) = imp::busy_and_steal_ns(from, to);
        assert_eq!(busy, 40 * 1_000_000_000 / 100);
    }

    #[cfg(any(target_os = "linux", target_vendor = "apple"))]
    #[test]
    fn ticks_close_a_window_after_a_window_of_time() {
        tick();
        let started = now_ns();
        while now_ns() - started < WINDOW_NS + WINDOW_NS / 10 {
            crate::busy_work(10_000_000);
            tick();
        }
        let windows = windows();
        assert!(!windows.is_empty(), "a window closed");
        for pair in windows.windows(2) {
            assert_eq!(pair[0].end_ns, pair[1].start_ns, "windows follow one another");
        }
        assert!(windows.iter().all(|w| w.end_ns - w.start_ns >= WINDOW_NS / 2), "each window lasts half a window or more");
    }
}

/// What a machine reading costs (`cargo test --release -- --ignored
/// --nocapture reading_cost`): measured through this crate, printed.
#[cfg(test)]
#[test]
#[ignore]
fn reading_cost() {
    for batch in crate::measure(9, 20_000_000, || { std::hint::black_box(Reading::take()); }) {
        println!("a machine reading: {}", batch.show());
    }
    for batch in crate::measure(9, 20_000_000, tick) {
        println!("a tick between readings: {}", batch.show());
    }
}
