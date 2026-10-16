//! The thread's counts per core kind on Linux x86-64 hybrid CPUs (Intel's
//! P and E cores), through `perf_event_open`: one counter group (cycles,
//! instructions) on each core kind's PMU, `cpu_core` and `cpu_atom`, which
//! count only while the thread runs on a core of their kind, so the split
//! says which kind ran it. Cycles and instructions are user space's; time
//! is the group's running time, which includes the thread's kernel time on
//! that kind, so the MHz they give reads low across system calls. Where the
//! CPU has no hybrid PMUs or the kernel refuses (perf_event_paranoid above
//! 2, a container), there are no counts.
use super::{Counts, Level};
use std::ffi::{c_int, c_long, c_void};
use std::os::fd::{AsRawFd, FromRawFd, OwnedFd};
use std::sync::OnceLock;

/// perf_event_attr, version 0 (64 bytes): the fields used, zero after.
#[repr(C)]
pub(crate) struct Attr {
    pub(crate) kind: u32,
    pub(crate) size: u32,
    pub(crate) config: u64,
    pub(crate) sample_period: u64,
    pub(crate) sample_type: u64,
    pub(crate) read_format: u64,
    pub(crate) flags: u64,
    pub(crate) reserved: [u64; 2],
}

unsafe extern "C" {
    fn syscall(number: c_long, ...) -> c_long;
    #[link_name = "read"]
    pub(crate) fn read_fd(fd: c_int, buffer: *mut c_void, size: usize) -> isize;
}

const SYS_PERF_EVENT_OPEN: c_long = 298;
const PERF_FLAG_FD_CLOEXEC: c_long = 8;

fn attr(pmu: u32, event: u64, leader: bool) -> Attr {
    Attr {
        // PERF_TYPE_HARDWARE, with the PMU in config's upper word.
        kind: 0,
        size: std::mem::size_of::<Attr>() as u32,
        config: (u64::from(pmu) << 32) | event,
        sample_period: 0,
        sample_type: 0,
        // PERF_FORMAT_TOTAL_TIME_ENABLED | _RUNNING | _GROUP.
        read_format: 1 | 2 | 8,
        // pinned (the leader: never multiplexed), exclude_kernel, exclude_hv.
        flags: (u64::from(leader) << 2) | (1 << 5) | (1 << 6),
        reserved: [0; 2],
    }
}

/// A counter of `event` on `pmu` for the calling thread, in `group` (or a
/// new group's leader, with -1).
fn open(pmu: u32, event: u64, group: c_int) -> Option<OwnedFd> {
    // pid 0 and cpu -1: the calling thread, on any CPU.
    perf_open(&attr(pmu, event, group == -1), 0, -1, group)
}

/// perf_event_open(`a`, `pid`, `cpu`, `group`), close-on-exec: the counter's
/// descriptor, or `None` where the kernel refuses.
pub(crate) fn perf_open(a: &Attr, pid: c_int, cpu: c_int, group: c_int) -> Option<OwnedFd> {
    // Sound: the x86-64 Linux system call, `a` an initialized attr of the
    // size it states.
    let fd = unsafe { syscall(SYS_PERF_EVENT_OPEN, a as *const Attr, c_long::from(pid), c_long::from(cpu), c_long::from(group), PERF_FLAG_FD_CLOEXEC) };
    // Sound: a fresh descriptor, ours alone.
    (fd >= 0).then(|| unsafe { OwnedFd::from_raw_fd(c_int::try_from(fd).unwrap()) })
}

/// One core kind's group: cycles leading, instructions.
struct Group {
    leader: OwnedFd,
    _instructions: OwnedFd,
}

impl Group {
    fn new(pmu: u32) -> Option<Group> {
        let leader = open(pmu, 0, -1)?; // PERF_COUNT_HW_CPU_CYCLES
        let instructions = open(pmu, 1, leader.as_raw_fd())?; // PERF_COUNT_HW_INSTRUCTIONS
        let group = Group { leader, _instructions: instructions };
        group.read()?;
        Some(group)
    }

    /// The group's counts so far; `None` once a pinned group could not be
    /// scheduled (its reads then return nothing).
    fn read(&self) -> Option<Level> {
        // nr, time enabled, time running, cycles, instructions.
        let mut words = [0u64; 5];
        // Sound: `words` is writable for the size passed.
        let n = unsafe { read_fd(self.leader.as_raw_fd(), words.as_mut_ptr().cast(), std::mem::size_of_val(&words)) };
        if n == 0 {
            return None;
        }
        assert_eq!(n, std::mem::size_of_val(&words) as isize, "a perf group read gives its whole record");
        assert_eq!(words[0], 2, "the group holds cycles and instructions");
        Some(Level { cycles: words[3], instructions: words[4], time_ns: words[2] })
    }
}

/// The two kinds' PMU types, where the CPU is hybrid.
fn pmus() -> Option<[u32; 2]> {
    static PMUS: OnceLock<Option<[u32; 2]>> = OnceLock::new();
    *PMUS.get_or_init(|| {
        let kind = |name: &str| std::fs::read_to_string(format!("/sys/bus/event_source/devices/{name}/type")).ok()?.trim().parse::<u32>().ok();
        Some([kind("cpu_core")?, kind("cpu_atom")?])
    })
}

pub fn read() -> Option<Counts> {
    // Opened on the thread's first read; they count that thread alone and
    // close when it exits.
    std::thread_local! {
        static GROUPS: Option<[Group; 2]> = pmus().and_then(|[p, e]| Some([Group::new(p)?, Group::new(e)?]));
    }
    GROUPS.with(|groups| {
        let [p, e] = groups.as_ref()?;
        Some(Counts { p: p.read()?, e: e.read()? })
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn an_attr_is_perf_event_attr_v0_counting_one_thread_unscaled() {
        assert_eq!(std::mem::size_of::<Attr>(), 64);
        let a = attr(8, 1, false);
        assert_eq!(a.config, (8u64 << 32) | 1);
        assert_eq!(a.read_format, 11);
        assert_eq!(a.flags, (1 << 5) | (1 << 6));
        assert_eq!(attr(8, 0, true).flags & (1 << 2), 1 << 2);
    }

    /// On a hybrid CPU with perf allowed: run with the thread pinned to one
    /// kind, CLOCKS_EXPECT_KIND=P (taskset -c 0) or E (taskset -c 16).
    #[test]
    #[ignore = "needs Intel hybrid PMUs, perf allowed, and a declared pinning"]
    fn counts_fall_on_the_kind_that_ran() {
        let expected = std::env::var("CLOCKS_EXPECT_KIND").expect("CLOCKS_EXPECT_KIND=P or E");
        for b in crate::measure(4, 2_000_000, || crate::busy_work(10_000)) {
            let c = b.counts.expect("hybrid PMUs readable here");
            let (ran, idle) = if expected == "P" { (c.p, c.e) } else { (c.e, c.p) };
            assert!(ran.cycles > 0 && ran.instructions > 0 && ran.time_ns > 0);
            assert_eq!(idle, Level::default(), "the other kind counted nothing");
            println!("{}", b.show());
        }
    }
}
