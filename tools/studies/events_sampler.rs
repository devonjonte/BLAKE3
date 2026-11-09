//! Which events move with the cycles of producing the final hashes.
//!
//! For each shape (a mode mix, a count of messages, a message length), the
//! sampler prepares K = 8 sets of hashers, feeds every set its messages in
//! 4 KiB pieces in the canonical caller order (hasher (i * 61) mod n for
//! piece i), then counts, in one bracket, the final hashes of all 8 sets:
//! a counter read, a wall read, 8 calls of `finalize_each`, a wall read, a
//! counter read. 64 samples a shape. Spreading the two reads over 8 sets
//! makes their own cost (about 2,400 cycles through this interface) a
//! small share of each sample. A "nothing" shape brackets no work, so that
//! share is on record.
//!
//! The counters are Apple's per-thread kpc counters (root): cycles,
//! instructions, and up to eight chosen events, taken in the order below
//! until the counters are full. Output is TSV on stdout: `meta` lines
//! (events configured, user), one `digest` line (the library's own hash
//! of every output, for the judge to match across runs), and `sample`
//! lines: shape, event, count, units (messages finished; 1 for nothing).
use blake3_servil::{convenience::Hasher, throughput, Mode};
use std::ffi::{c_char, c_int, c_void, CString};

const K: usize = 8;
const SAMPLES: usize = 64;
const PIECE: usize = 4096;
/// (flavor, open hashers, message length). The four shapes whose cycles
/// rose on the Mac (Mac 2062), the two whose finish wall time rose in the
/// VM, and one plain control.
const SHAPES: &[(&str, usize, usize)] = &[
    ("plain", 128, 16384),
    ("plain", 24, 32768),
    ("plain", 512, 16384),
    ("mixed", 128, 16384),
    ("mixed", 24, 32768),
    ("mixed", 8, 16384),
    ("shared", 128, 32768),
];
const WANTED: &[&str] = &[
    "FIXED_CYCLES",
    "FIXED_INSTRUCTIONS",
    "L1D_CACHE_MISS_LD",
    "L1I_CACHE_MISS_DEMAND",
    "L1D_TLB_MISS",
    "MAP_STALL",
    "LDST_UNIT_WAITING_SME_ENGINE_MEM_DATA",
    "SCHEDULE_WAITING_SME_ENGINE_REG_DATA",
    "SME_ENGINE_SM_ENABLE",
    "INTERRUPT_PENDING",
    "L1D_CACHE_MISS_ST",
];

unsafe extern "C" {
    fn dlopen(path: *const c_char, flags: c_int) -> *mut c_void;
    fn dlsym(handle: *mut c_void, name: *const c_char) -> *mut c_void;
    fn getuid() -> u32;
}

struct Kpc {
    get_thread_counters: unsafe extern "C" fn(u32, u32, *mut u64) -> c_int,
    set_counting: unsafe extern "C" fn(u32) -> c_int,
    set_thread_counting: unsafe extern "C" fn(u32) -> c_int,
    force_all: unsafe extern "C" fn(c_int) -> c_int,
    counters: u32,
    /// Each configured event's index among the counters read.
    map: Vec<usize>,
    names: Vec<&'static str>,
}

fn sym<T>(lib: *mut c_void, name: &str) -> T {
    let c = CString::new(name).unwrap();
    // Sound: the frameworks export these C functions with the declared types.
    let p = unsafe { dlsym(lib, c.as_ptr()) };
    assert!(!p.is_null(), "missing symbol {name}");
    unsafe { std::mem::transmute_copy(&p) }
}

impl Kpc {
    fn open() -> Kpc {
        assert_eq!(unsafe { getuid() }, 0, "kpc configures counters as root alone");
        let lib = |p: &str| {
            let c = CString::new(p).unwrap();
            let h = unsafe { dlopen(c.as_ptr(), 1) };
            assert!(!h.is_null(), "cannot load {p}");
            h
        };
        let kperf = lib("/System/Library/PrivateFrameworks/kperf.framework/kperf");
        let kperfdata = lib("/System/Library/PrivateFrameworks/kperfdata.framework/kperfdata");
        let force_all: unsafe extern "C" fn(c_int) -> c_int = sym(kperf, "kpc_force_all_ctrs_set");
        let set_counting: unsafe extern "C" fn(u32) -> c_int = sym(kperf, "kpc_set_counting");
        let set_thread_counting: unsafe extern "C" fn(u32) -> c_int = sym(kperf, "kpc_set_thread_counting");
        let set_config: unsafe extern "C" fn(u32, *mut u64) -> c_int = sym(kperf, "kpc_set_config");
        let counter_count: unsafe extern "C" fn(u32) -> u32 = sym(kperf, "kpc_get_counter_count");
        let get_thread_counters: unsafe extern "C" fn(u32, u32, *mut u64) -> c_int = sym(kperf, "kpc_get_thread_counters");
        let db_create: unsafe extern "C" fn(*const c_char, *mut *mut c_void) -> c_int = sym(kperfdata, "kpep_db_create");
        let db_event: unsafe extern "C" fn(*mut c_void, *const c_char, *mut *mut c_void) -> c_int = sym(kperfdata, "kpep_db_event");
        let config_create: unsafe extern "C" fn(*mut c_void, *mut *mut c_void) -> c_int = sym(kperfdata, "kpep_config_create");
        let config_force: unsafe extern "C" fn(*mut c_void) -> c_int = sym(kperfdata, "kpep_config_force_counters");
        let config_add: unsafe extern "C" fn(*mut c_void, *mut *mut c_void, u32, *mut u32) -> c_int = sym(kperfdata, "kpep_config_add_event");
        let config_kpc: unsafe extern "C" fn(*mut c_void, *mut u64, usize) -> c_int = sym(kperfdata, "kpep_config_kpc");
        let config_kpc_count: unsafe extern "C" fn(*mut c_void, *mut usize) -> c_int = sym(kperfdata, "kpep_config_kpc_count");
        let config_classes: unsafe extern "C" fn(*mut c_void, *mut u32) -> c_int = sym(kperfdata, "kpep_config_kpc_classes");
        let config_map: unsafe extern "C" fn(*mut c_void, *mut usize, usize) -> c_int = sym(kperfdata, "kpep_config_kpc_map");
        // Sound: plain calls into the frameworks with writable out-pointers.
        unsafe {
            assert_eq!(force_all(1), 0, "kpc_force_all_ctrs_set(1)");
            let mut db = std::ptr::null_mut();
            assert_eq!(db_create(std::ptr::null(), &mut db), 0, "kpep_db_create");
            let mut cfg = std::ptr::null_mut();
            assert_eq!(config_create(db, &mut cfg), 0, "kpep_config_create");
            assert_eq!(config_force(cfg), 0, "kpep_config_force_counters");
            let mut names = Vec::new();
            for &name in WANTED {
                let c = CString::new(name).unwrap();
                let mut ev = std::ptr::null_mut();
                if db_event(db, c.as_ptr(), &mut ev) != 0 {
                    println!("meta\tno event\t{name}");
                    continue;
                }
                let mut err = 0u32;
                if config_add(cfg, &mut ev, 0, &mut err) != 0 {
                    println!("meta\tnot added\t{name}\terror {err}");
                    continue;
                }
                names.push(name);
            }
            let mut classes = 0u32;
            assert_eq!(config_classes(cfg, &mut classes), 0);
            let mut regs_n = 0usize;
            assert_eq!(config_kpc_count(cfg, &mut regs_n), 0);
            let mut regs = vec![0u64; regs_n.max(1)];
            assert_eq!(config_kpc(cfg, regs.as_mut_ptr(), regs_n * 8), 0, "kpep_config_kpc");
            let mut map = vec![0usize; 32];
            assert_eq!(config_map(cfg, map.as_mut_ptr(), 32 * 8), 0, "kpep_config_kpc_map");
            map.truncate(names.len());
            assert_eq!(set_config(classes, regs.as_mut_ptr()), 0, "kpc_set_config");
            assert_eq!(set_counting(classes), 0, "kpc_set_counting");
            assert_eq!(set_thread_counting(classes), 0, "kpc_set_thread_counting");
            let counters = counter_count(classes);
            println!("meta\tevents\t{}", names.iter().zip(&map).map(|(n, i)| format!("{n}@{i}")).collect::<Vec<_>>().join(" "));
            Kpc { get_thread_counters, set_counting, set_thread_counting, force_all, counters, map, names }
        }
    }

    #[inline(always)]
    fn read(&self, into: &mut [u64; 32]) {
        // Sound: `into` holds 32 counters, at least `self.counters`.
        let r = unsafe { (self.get_thread_counters)(0, self.counters, into.as_mut_ptr()) };
        debug_assert_eq!(r, 0, "kpc_get_thread_counters");
    }

    fn close(&self) {
        unsafe {
            (self.set_thread_counting)(0);
            (self.set_counting)(0);
            (self.force_all)(0);
        }
    }
}

fn mode<'a>(i: usize, flavor: &str, keys: &'a [[u8; 32]]) -> Mode<'a> {
    match flavor {
        "plain" => Mode::Plain,
        "shared" => Mode::Keyed(&keys[0]),
        "mixed" => match i % 3 {
            0 => Mode::Plain,
            1 => Mode::Keyed(&keys[i]),
            _ => Mode::DeriveKey("BLAKE3-Servil finish events probe"),
        },
        _ => unreachable!("a listed flavor"),
    }
}

fn main() {
    blake3_servil::initialize();
    println!("meta\tuid\t{}", unsafe { getuid() });
    println!("meta\tsets\t{K}\tsamples\t{SAMPLES}\tpiece\t{PIECE}");
    let kpc = Kpc::open();
    let mut before = [0u64; 32];
    let mut after = [0u64; 32];
    let mut all_outputs = Hasher::new(Mode::Plain, None);
    let emit = |shape: &str, wall: u64, before: &[u64; 32], after: &[u64; 32], units: usize| {
        println!("sample\t{shape}\twall_ns\t{wall}\t{units}");
        for (name, &i) in kpc.names.iter().zip(&kpc.map) {
            println!("sample\t{shape}\t{name}\t{}\t{units}", after[i] - before[i]);
        }
    };
    for _ in 0..SAMPLES {
        kpc.read(&mut before);
        let t = clocks::now();
        let wall = clocks::since_ns(t);
        kpc.read(&mut after);
        emit("nothing", wall, &before, &after, 1);
    }
    for &(flavor, open, len) in SHAPES {
        let shape = format!("{flavor}_{open}x{len}");
        let keys: Vec<[u8; 32]> = (0..open)
            .map(|i| {
                let mut key: [u8; 32] = core::array::from_fn(|j| (j * 11 + 73) as u8);
                key[..8].copy_from_slice(&(i as u64).to_le_bytes());
                key
            })
            .collect();
        let which: Vec<usize> = (0..open).map(|i| (i * 61) % open).collect();
        assert_eq!(which.iter().collect::<std::collections::BTreeSet<_>>().len(), open, "61 is coprime to every listed count");
        let data: Vec<Vec<u8>> = (0..open).map(|i| (0..len).map(|j| (i * 31 + j * 17) as u8).collect()).collect();
        let mut sets: Vec<Vec<Hasher>> = (0..K).map(|_| (0..open).map(|i| Hasher::new(mode(i, flavor, &keys), None)).collect()).collect();
        let mut outs = vec![vec![[0u8; 32]; open]; K];
        let mut pieces: Vec<(usize, &[u8])> = Vec::with_capacity(open);
        for _ in 0..SAMPLES {
            for set in &mut sets {
                for from in (0..len).step_by(PIECE) {
                    pieces.clear();
                    pieces.extend(data.iter().enumerate().map(|(i, d)| (which[i], &d[from..(from + PIECE).min(len)])));
                    throughput::update_each(set, std::hint::black_box(pieces.as_slice()));
                }
            }
            kpc.read(&mut before);
            let t = clocks::now();
            for (set, out) in sets.iter_mut().zip(&mut outs) {
                throughput::finalize_each(std::hint::black_box(set), std::hint::black_box(&which), out);
            }
            let wall = clocks::since_ns(t);
            kpc.read(&mut after);
            emit(&shape, wall, &before, &after, K * open);
            assert!(outs.iter().all(|o| *o == outs[0]), "every set hashed the same messages");
        }
        all_outputs.update(outs[0].as_flattened());
    }
    kpc.close();
    let digest = all_outputs.finalize();
    println!("digest\t{}", digest.to_hex());
}
