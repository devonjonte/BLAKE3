//! Optional Linux x86 hybrid-PMU thread counts, through perf_event_open.
//! Intel's cpu_core/cpu_atom PMUs supply the P/E classification themselves.
//! Counts are user-space cycles/instructions; time is PMU running time, which
//! includes kernel work while scheduled. Their rate approximates the user
//! clock on long batches; counter-read overhead matters for short intervals.
//! No multiplex scaling or wall-time correction is performed.
use super::{Counts, Level};
use std::{ffi::{c_int, c_long, c_void}, os::fd::{AsRawFd, FromRawFd, OwnedFd}, sync::OnceLock};

#[repr(C)]
struct Attr {
    kind: u32,
    size: u32,
    config: u64,
    sample_period: u64,
    sample_type: u64,
    read_format: u64,
    flags: u64,
    reserved: [u64; 2],
}

unsafe extern "C" {
    fn syscall(number: c_long, ...) -> c_long;
    fn read(fd: c_int, buffer: *mut c_void, size: usize) -> isize;
}

fn attr(pmu: u32, event: u64, leader: bool) -> Attr {
    Attr {
        kind: 0, // PERF_TYPE_HARDWARE; PMU selection in config's upper word.
        size: std::mem::size_of::<Attr>() as u32,
        config: (u64::from(pmu) << 32) | event,
        sample_period: 0,
        sample_type: 0,
        read_format: 1 | 2 | 8, // total enabled time, running time, group.
        flags: (u64::from(leader) << 2) | (1 << 5) | (1 << 6), // pinned leader; exclude kernel/HV.
        reserved: [0; 2],
    }
}

fn open(pmu: u32, event: u64, group: c_int) -> Option<OwnedFd> {
    let a = attr(pmu, event, group == -1);
    // Sound: x86_64 Linux syscall ABI; a points to an initialized 64-byte
    // perf_event_attr v0. pid0/cpu-1 counts this calling thread, no inherit.
    let fd = unsafe { syscall(298, &a as *const Attr, 0 as c_long, -1 as c_long, c_long::from(group), 8 as c_long) }; // FD_CLOEXEC.
    if fd < 0 { return None; }
    // Sound: perf_event_open returned a fresh owned descriptor.
    Some(unsafe { OwnedFd::from_raw_fd(c_int::try_from(fd).unwrap()) })
}

struct Group {
    leader: OwnedFd,
    _instructions: OwnedFd,
}

impl Group {
    fn new(pmu: u32) -> Option<Self> {
        let leader = open(pmu, 0, -1)?; // PERF_COUNT_HW_CPU_CYCLES.
        let instructions = open(pmu, 1, leader.as_raw_fd())?;
        let result = Self { leader, _instructions: instructions };
        result.snapshot()?; // Establish the group-read contract before using it.
        Some(result)
    }

    fn snapshot(&self) -> Option<Level> {
        // PERF_FORMAT_GROUP without IDs: nr, enabled_ns, running_ns, two values
        // in insertion order. Pinned groups are never multiplex-scaled.
        let mut words = [0u64; 5];
        // Sound: words is writable for exactly the requested size.
        let n = unsafe { read(self.leader.as_raw_fd(), words.as_mut_ptr().cast(), std::mem::size_of_val(&words)) };
        if n == 0 { return None; } // A pinned group could not schedule.
        assert_eq!(n, std::mem::size_of_val(&words) as isize, "perf group read");
        assert_eq!(words[0], 2, "cycles and instructions form one group");
        Some(Level { cycles: words[3], instructions: words[4], time_ns: words[2] })
    }
}

fn groups() -> Option<[Group; 2]> {
    static PMUS: OnceLock<Option<[u32; 2]>> = OnceLock::new();
    let pmus = (*PMUS.get_or_init(|| {
        let kind = |name: &str| std::fs::read_to_string(format!("/sys/bus/event_source/devices/{name}/type")).ok()?.trim().parse::<u32>().ok();
        Some([kind("cpu_core")?, kind("cpu_atom")?])
    }))?;
    Some([Group::new(pmus[0])?, Group::new(pmus[1])?])
}

pub(super) fn counts() -> Option<Counts> {
    // File descriptors count only the thread that opened them and close when
    // that thread exits. Unsupported PMUs/permissions yield unavailable counts.
    thread_local! { static GROUPS: Option<[Group; 2]> = groups(); }
    GROUPS.with(|groups| {
        let groups = groups.as_ref()?;
        Some(Counts { p: groups[0].snapshot()?, e: groups[1].snapshot()? })
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn perf_attributes_identify_one_thread_and_group_without_scaling() {
        assert_eq!(std::mem::size_of::<Attr>(), 64);
        let a = attr(17, 1, false);
        assert_eq!(a.config, (17u64 << 32) | 1);
        assert_eq!(a.read_format, 11);
        assert_eq!(a.flags, (1 << 5) | (1 << 6));
        assert_eq!(attr(17, 0, true).flags & (1 << 2), 1 << 2);
    }

    #[test]
    #[ignore = "requires accessible Intel hybrid PMUs; run under declared affinity"]
    fn live_counts_cover_shared_clock_batches() {
        let expected = std::env::var("CLOCKS_EXPECT_KIND").expect("declare P or E for the pinned live test");
        assert!(expected == "P" || expected == "E");
        let batches = super::super::measure_calls(4, 1, || super::super::busy_work(2_000_000));
        for b in batches {
            let c = b.counts.expect("accessible hybrid PMUs");
            assert!(c.p.cycles + c.e.cycles > 0);
            assert!(c.p.instructions + c.e.instructions > 0);
            assert!(c.p.time_ns + c.e.time_ns > 0);
            assert_eq!(if expected == "P" { c.e } else { c.p }, Level::default(), "other core kind stayed inactive");
            println!("{} counts={c:?}", b.show());
        }
    }

    #[test]
    #[ignore = "diagnostic counter-read cost through shared clocks"]
    fn live_counter_read_cost() {
        let batches = super::super::measure_calls(8, 1000, || { std::hint::black_box(counts().expect("available PMUs")); });
        for b in batches { println!("{} count reads: {} wall ns", b.calls, b.wall_ns); }
    }
}
