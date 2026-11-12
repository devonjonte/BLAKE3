//! The tree of chaining values two ways, both written in Ode: the stack (`push`, `merge`; hasher.ode) and
//! the levels (`ladd`, `lroot`; levels.ode). First that the levels agree with BLAKE3, then what each
//! costs. Single executions on one machine: inventory, no speed verdict.
use blake3_servil_core::labshim as hand;
use std::time::Instant;

extern "C" {
    fn b_push(st: u64, cv: u64) -> u64;
    fn b_merge(st: u64, key: u64, flags: u64, plat: u64, target: u64) -> u64;
    fn b_hash(out: u64, input: u64, len: u64, key: u64, flags: u64, plat: u64) -> u64;
    fn l_ladd(lv: u64, key: u64, flags: u64, plat: u64, cv: u64) -> u64;
    fn l_lroot(out: u64, lv: u64, key: u64, flags: u64, plat: u64) -> u64;
    fn l_hash2(out: u64, input: u64, len: u64, key: u64, flags: u64, plat: u64) -> u64;
    /// The crate's one-block kernel, for the reference tree.
    fn blake3_servil_compress_in_place_sse41(cv: *mut u32, block: *const u8, block_len: u8, counter: u64, flags: u8);
}
type HashFn = unsafe extern "C" fn(u64, u64, u64, u64, u64, u64) -> u64;

const PARENT: u8 = 4;
const ROOT: u8 = 8;

#[repr(C, align(64))]
struct LStack {
    len: u64,
    pad: [u64; 3],
    cvs: [[u8; 32]; 55],
}

#[repr(C, align(64))]
struct Levels {
    n: u64,
    pad: [u64; 7],
    level: [[u8; 64]; 54],
}

fn rng(state: &mut u64) -> u64 {
    *state ^= *state << 13;
    *state ^= *state >> 7;
    *state ^= *state << 17;
    *state
}

fn random_cv(s: &mut u64) -> [u8; 32] {
    let mut cv = [0u8; 32];
    for chunk in cv.chunks_mut(8) {
        chunk.copy_from_slice(&rng(s).to_le_bytes());
    }
    cv
}

/// A parent node's value, by the crate's SSE4.1 kernel.
fn parent(key: &[u32; 8], flags: u8, left: &[u8; 32], right: &[u8; 32]) -> [u8; 32] {
    let mut block = [0u8; 64];
    block[..32].copy_from_slice(left);
    block[32..].copy_from_slice(right);
    let mut cv = *key;
    unsafe { blake3_servil_compress_in_place_sse41(cv.as_mut_ptr(), block.as_ptr(), 64, 0, flags) };
    let mut out = [0u8; 32];
    for (o, w) in out.chunks_mut(4).zip(cv) {
        o.copy_from_slice(&w.to_le_bytes());
    }
    out
}

/// The specification's tree over chunk values: the left subtree is the largest power of two below the count.
fn tree(key: &[u32; 8], flags: u8, cvs: &[[u8; 32]], root: bool) -> [u8; 32] {
    if cvs.len() == 1 {
        return cvs[0];
    }
    let left = 1usize << (usize::BITS - 1 - (cvs.len() - 1).leading_zeros());
    let (l, r) = (tree(key, flags, &cvs[..left], false), tree(key, flags, &cvs[left..], false));
    parent(key, flags | PARENT | if root { ROOT } else { 0 }, &l, &r)
}

/// `ladd` every value, `lroot` after each: against the specification's tree. Every count to `every`,
/// then random larger ones.
fn agree_levels(plat: u64) -> u64 {
    let mut s = 0x9E3779B97F4A7C15u64;
    let mut cases = 0;
    for (m, flags) in [0u8, 16, 64].into_iter().enumerate() {
        let key: [u32; 8] = core::array::from_fn(|_| rng(&mut s) as u32);
        let total = if m == 0 { 5000 } else { 1500 };
        let cvs: Vec<[u8; 32]> = (0..total).map(|_| random_cv(&mut s)).collect();
        let mut lv = Levels { n: 0, pad: [0; 7], level: [[0; 64]; 54] };
        for (i, cv) in cvs.iter().enumerate() {
            let n = unsafe { l_ladd(&mut lv as *mut Levels as u64, key.as_ptr() as u64, flags as u64, plat, cv.as_ptr() as u64) };
            assert_eq!(n as usize, i + 1);
            assert_eq!(lv.n as usize, i + 1);
            if i >= 1 && (i < 700 || rng(&mut s) % 16 == 0) {
                let before = lv.level;
                let mut out = [0u8; 32];
                unsafe { l_lroot(out.as_mut_ptr() as u64, &lv as *const Levels as u64, key.as_ptr() as u64, flags as u64, plat) };
                assert_eq!(out, tree(&key, flags, &cvs[..=i], true), "the root of {} values, flags {flags}", i + 1);
                assert!(before == lv.level && lv.n as usize == i + 1, "lroot leaves the levels as they are");
                cases += 1;
            }
        }
    }
    cases
}

fn agree_hash(name: &str, hash: HashFn, plat: u64) -> u64 {
    let mut s = 0xD1B54A32D192ED03u64;
    let data: Vec<u8> = (0..(1 << 20) + 77).map(|_| rng(&mut s) as u8).collect();
    let mut lens: Vec<usize> = (0..=2100).collect();
    for k in 2..70 {
        for d in [-65i64, -64, -63, -1, 0, 1, 63, 64, 65] {
            lens.push((k * 1024 + d) as usize);
        }
    }
    lens.extend([1 << 20, (1 << 20) + 1, (1 << 20) + 77, 31 * 1024, 33 * 1024 + 5]);
    let mut cases = 0;
    for (m, flags) in [0u8, 16, 64].into_iter().enumerate() {
        let key: [u32; 8] = if m == 0 { *blake3_servil_core::IV } else { core::array::from_fn(|_| rng(&mut s) as u32) };
        for &len in &lens {
            let want = blake3_servil_core::hash_serial(&data[..len], &key, flags);
            let mut out = [0u8; 32];
            unsafe { hash(out.as_mut_ptr() as u64, data.as_ptr() as u64, len as u64, key.as_ptr() as u64, flags as u64, plat) };
            assert_eq!(&out, want.as_bytes(), "{name}: the hash of {len} bytes, flags {flags}");
            cases += 1;
        }
    }
    cases
}

fn least(tries: usize, reps: u64, mut f: impl FnMut()) -> f64 {
    let mut best = f64::MAX;
    for _ in 0..tries {
        let t = Instant::now();
        for _ in 0..reps {
            f();
        }
        best = best.min(t.elapsed().as_nanos() as f64 / reps as f64);
    }
    best
}

fn main() {
    blake3_servil_core::initialize();
    let plat = hand::platform_number() as u64;
    println!("platform {plat}");
    println!("levels: ladd and lroot agree with the specification's tree on {} roots (every count from 2 to 700, others to 5000; three modes)", agree_levels(plat));
    println!("levels: the whole hash (hash2) agrees with the crate's hash_serial on {} inputs", agree_hash("levels", l_hash2 as HashFn, plat));
    println!("stack: the whole hash (hash) agrees with the crate's hash_serial on {} inputs", agree_hash("stack", b_hash as HashFn, plat));

    // The whole hash, where neither uses a kernel wider than sixteen chunks (to 32 KiB).
    let mut s = 99u64;
    let data: Vec<u8> = (0..1 << 20).map(|_| rng(&mut s) as u8).collect();
    let key = *blake3_servil_core::IV;
    for len in [2048usize, 4096, 16384, 32768] {
        let reps = (40_000_000 / (len as u64 + 200)).max(20);
        let hand = least(25, reps, || {
            std::hint::black_box(blake3_servil_core::hash_serial(std::hint::black_box(&data[..len]), &key, 0));
        });
        let mut out = [0u8; 32];
        let mut ns = vec![];
        for h in [b_hash as HashFn, l_hash2 as HashFn] {
            ns.push(least(25, reps, || {
                unsafe { h(out.as_mut_ptr() as u64, std::hint::black_box(data.as_ptr()) as u64, len as u64, key.as_ptr() as u64, 0, plat) };
                std::hint::black_box(&out);
            }));
        }
        println!("hash of {len} bytes, ns a call: the crate's hash_serial {:.1}, the stack {:.1}, the levels {:.1} ({:+.1}% of the stack)",
                 hand, ns[0], ns[1], 100.0 * (ns[1] / ns[0] - 1.0));
    }

    // The tree alone: 1024 values added, and the root. The stack: push, then merge to the count's one bits
    // (as its caller asks), 1023 parents in the adds; its root is then the one value left. The levels: ladd
    // (lazy: fewer parents in the adds), then lroot.
    let mut s = 7u64;
    let key: [u32; 8] = core::array::from_fn(|_| rng(&mut s) as u32);
    for count in [1024usize, 1000] {
        let cvs: Vec<[u8; 32]> = (0..count).map(|_| random_cv(&mut s)).collect();
        let mut st = LStack { len: 0, pad: [0; 3], cvs: [[0; 32]; 55] };
        let stack = least(25, 300, || {
            st.len = 0;
            for (i, cv) in cvs.iter().enumerate() {
                unsafe {
                    b_push(&mut st as *mut LStack as u64, cv.as_ptr() as u64);
                    b_merge(&mut st as *mut LStack as u64, key.as_ptr() as u64, 0, plat, (i as u64 + 1).count_ones() as u64);
                }
            }
            // what is left is folded from the top (the root's flags aside: the same work)
            unsafe { b_merge(&mut st as *mut LStack as u64, key.as_ptr() as u64, 0, plat, 1) };
            std::hint::black_box(&st);
        });
        let mut lv = Levels { n: 0, pad: [0; 7], level: [[0; 64]; 54] };
        let mut out = [0u8; 32];
        let levels = least(25, 300, || {
            lv.n = 0;
            for cv in &cvs {
                unsafe { l_ladd(&mut lv as *mut Levels as u64, key.as_ptr() as u64, 0, plat, cv.as_ptr() as u64) };
            }
            unsafe { l_lroot(out.as_mut_ptr() as u64, &lv as *const Levels as u64, key.as_ptr() as u64, 0, plat) };
            std::hint::black_box(&out);
        });
        let n = count as f64;
        println!("{count} values added and the root made ({} parents either way), ns a value: the stack {:.1}, the levels {:.1} ({:+.1}%)",
                 count - 1, stack / n, levels / n, 100.0 * (levels / stack - 1.0));
    }
}
