//! The same three functions, three ways: the crate's hand-written Rust (through `labshim`, added to the
//! crate for this lab), the Rust Lean printed (compiled by rustc to assembly: way A), and the assembly
//! Lean printed itself (way B). First that they agree, then what each costs. Single executions on one
//! machine: inventory, no speed verdict.
use blake3_servil_core::labshim as hand;
use std::time::Instant;

extern "C" {
    fn a_push(st: u64, cv: u64) -> u64;
    fn a_merge(st: u64, key: u64, flags: u64, plat: u64, target: u64) -> u64;
    fn a_to_hex(out: u64, hash: u64) -> u64;
    fn b_push(st: u64, cv: u64) -> u64;
    fn b_merge(st: u64, key: u64, flags: u64, plat: u64, target: u64) -> u64;
    fn b_to_hex(out: u64, hash: u64) -> u64;
    fn a_hash(out: u64, input: u64, len: u64, key: u64, flags: u64, plat: u64) -> u64;
    fn b_hash(out: u64, input: u64, len: u64, key: u64, flags: u64, plat: u64) -> u64;
}
type HashFn = unsafe extern "C" fn(u64, u64, u64, u64, u64, u64) -> u64;

#[cfg(feature = "own_kernel")]
extern "C" {
    /// The one-block kernel written in the language's machine level.
    fn b_compress_avx512(cv: *mut u32, block: *const u8, block_len: u8, counter: u64, flags: u8);
    /// The hexadecimal kernel written in the language, proved against its contract.
    fn b_hex(out: *mut u8, hash: *const u8);
    /// The crate's, written by hand in assembly.
    fn blake3_servil_compress_in_place_avx512(cv: *mut u32, block: *const u8, block_len: u8, counter: u64, flags: u8);
}

/// The kernel written in the language against the crate's: random inputs, then the time of each.
#[cfg(feature = "own_kernel")]
fn kernel(plat: u64) {
    if plat != 5 {
        println!("the kernel written in the language is for AVX-512: not run on this machine");
        return;
    }
    let mut s = 0xA076_1D64_78BD_642Fu64;
    for _ in 0..200_000 {
        let cv: [u32; 8] = core::array::from_fn(|_| rng(&mut s) as u32);
        let mut block = [0u8; 64];
        for c in block.chunks_mut(8) {
            c.copy_from_slice(&rng(&mut s).to_le_bytes());
        }
        let (len, counter, flags) = ((rng(&mut s) % 65) as u8, rng(&mut s), rng(&mut s) as u8);
        let (mut a, mut b) = (cv, cv);
        unsafe {
            blake3_servil_compress_in_place_avx512(a.as_mut_ptr(), block.as_ptr(), len, counter, flags);
            b_compress_avx512(b.as_mut_ptr(), block.as_ptr(), len, counter, flags);
        }
        assert_eq!(a, b, "the kernel written in the language against the crate's");
    }
    println!("the kernel written in the language: 200000 random compressions agree with the crate's assembly");
    let block = [7u8; 64];
    let mut cv = [1u32; 8];
    let hand = least(25, 2_000_000, || unsafe { blake3_servil_compress_in_place_avx512(cv.as_mut_ptr(), block.as_ptr(), 64, 0, 0) });
    let own = least(25, 2_000_000, || unsafe { b_compress_avx512(cv.as_mut_ptr(), block.as_ptr(), 64, 0, 0) });
    println!("one compression, ns a call (each feeding the next): the crate's assembly {hand:.2}, written in the language {own:.2}");
}

/// The proved hexadecimal kernel against the crate's `to_hex`: random hashes, then the time of each.
#[cfg(feature = "own_kernel")]
fn hex_kernel() {
    let mut s = 0x2545F4914F6CDD1Du64;
    for _ in 0..1_000_000 {
        let hash = random_cv(&mut s);
        let mut out = [0u8; 64];
        unsafe { b_hex(out.as_mut_ptr(), hash.as_ptr()) };
        assert_eq!(&out[..], blake3_servil_core::Hash::from_bytes(hash).to_hex().as_bytes(), "the hexadecimal kernel");
    }
    for b in 0..=255u8 {
        let hash = [b; 32];
        let mut out = [0u8; 64];
        unsafe { b_hex(out.as_mut_ptr(), hash.as_ptr()) };
        assert_eq!(&out[..], blake3_servil_core::Hash::from_bytes(hash).to_hex().as_bytes());
    }
    println!("the hexadecimal kernel: 1000000 random hashes and every byte value agree with the crate's to_hex");
    let hash = random_cv(&mut s);
    let h = blake3_servil_core::Hash::from_bytes(hash);
    let hand = least(25, 5_000_000, || {
        std::hint::black_box(std::hint::black_box(&h).to_hex());
    });
    let mut out = [0u8; 64];
    let own = least(25, 5_000_000, || {
        unsafe { b_hex(out.as_mut_ptr(), std::hint::black_box(hash.as_ptr())) };
        std::hint::black_box(&out);
    });
    println!("to_hex, ns a call: the crate's Rust (a table) {hand:.2}, the kernel written in the language (no table, proved) {own:.2}");
}

/// The whole hash by a Lean-written function, against the crate's `hash_serial`: every length to
/// 2100, lengths around every chunk and block boundary to 70 KiB, and a megabyte; three modes.
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

/// The stack as the Lean functions lay it out: the length, then from byte 32 the values.
#[repr(C, align(64))]
#[derive(Clone)]
struct LStack {
    len: u64,
    pad: [u64; 3],
    cvs: [[u8; 32]; 55],
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

type PushFn = unsafe extern "C" fn(u64, u64) -> u64;
type MergeFn = unsafe extern "C" fn(u64, u64, u64, u64, u64) -> u64;
type HexFn = unsafe extern "C" fn(u64, u64) -> u64;

fn agree(name: &str, push: PushFn, merge: MergeFn, to_hex: HexFn, plat: u64) -> u64 {
    let mut s = 0x9E3779B97F4A7C15u64;
    let mut cases = 0u64;
    for round in 0..20_000u64 {
        let n = 1 + (rng(&mut s) % 54) as usize;
        let target = 1 + (rng(&mut s) % n as u64) as usize;
        let key: [u32; 8] = core::array::from_fn(|_| rng(&mut s) as u32);
        let flags = [0u8, 16, 64][(round % 3) as usize];
        let mut h = hand::new_stack();
        let mut l = LStack { len: 0, pad: [0; 3], cvs: [[0; 32]; 55] };
        for _ in 0..n {
            let cv = random_cv(&mut s);
            hand::push(&mut h, cv);
            unsafe { push(&mut l as *mut LStack as u64, cv.as_ptr() as u64) };
        }
        hand::merge(&mut h, &key, flags, target);
        let len = unsafe { merge(&mut l as *mut LStack as u64, key.as_ptr() as u64, flags as u64, plat, target as u64) };
        assert_eq!(len as usize, hand::len(&h), "{name}: the length after merge");
        assert_eq!(l.len as usize, hand::len(&h), "{name}: the stored length");
        for i in 0..hand::len(&h) {
            assert_eq!(l.cvs[i], hand::get(&h, i), "{name}: value {i} after merge of {n} to {target}");
        }
        let hash = random_cv(&mut s);
        let mut out = [0u8; 64];
        let got = unsafe { to_hex(out.as_mut_ptr() as u64, hash.as_ptr() as u64) };
        assert_eq!(got, 64);
        assert_eq!(&out[..], blake3_servil_core::Hash::from_bytes(hash).to_hex().as_bytes(), "{name}: to_hex");
        cases += 1;
    }
    cases
}

/// The least of `tries` timings of `f` run `reps` times, in nanoseconds a call.
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
    for (name, p, m, x) in [("way A (Lean, Rust printed, rustc)", a_push as PushFn, a_merge as MergeFn, a_to_hex as HexFn),
                            ("way B (Lean, assembly printed)", b_push as PushFn, b_merge as MergeFn, b_to_hex as HexFn)] {
        println!("{name}: {} random cases agree with the crate's Rust (push, merge, to_hex)", agree(name, p, m, x, plat));
    }
    #[cfg(feature = "own_kernel")]
    kernel(plat);
    #[cfg(feature = "own_kernel")]
    hex_kernel();
    for (name, h) in [("way A", a_hash as HashFn), ("way B", b_hash as HashFn)] {
        println!("{name}: the whole hash agrees with the crate's hash_serial on {} inputs", agree_hash(name, h, plat));
    }
    {
        let mut s = 99u64;
        let data: Vec<u8> = (0..1 << 20).map(|_| rng(&mut s) as u8).collect();
        let key = *blake3_servil_core::IV;
        for len in [64usize, 1024, 4096, 16384, 1 << 20] {
            let reps = (40_000_000 / (len as u64 + 200)).max(20);
            let hand = least(15, reps, || {
                std::hint::black_box(blake3_servil_core::hash_serial(std::hint::black_box(&data[..len]), &key, 0));
            });
            let mut out = [0u8; 32];
            let mut ns = vec![];
            for h in [a_hash as HashFn, b_hash as HashFn] {
                ns.push(least(15, reps, || {
                    unsafe { h(out.as_mut_ptr() as u64, std::hint::black_box(data.as_ptr()) as u64, len as u64, key.as_ptr() as u64, 0, plat) };
                    std::hint::black_box(&out);
                }));
            }
            println!("hash of {len} bytes, ns a call: the crate's hash_serial {:.1}, way A {:.1} ({:+.1}%), way B {:.1} ({:+.1}%)",
                     hand, ns[0], 100.0 * (ns[0] / hand - 1.0), ns[1], 100.0 * (ns[1] / hand - 1.0));
        }
    }
    // Costs. merge: a stack of 2 merged to 1 (one parent), and of 11 merged to 1 (ten parents).
    let mut s = 7u64;
    let key: [u32; 8] = core::array::from_fn(|_| rng(&mut s) as u32);
    let cvs: Vec<[u8; 32]> = (0..11).map(|_| random_cv(&mut s)).collect();
    let hash = random_cv(&mut s);
    for depth in [2usize, 11] {
        let mut h0 = hand::new_stack();
        let mut l0 = LStack { len: 0, pad: [0; 3], cvs: [[0; 32]; 55] };
        for cv in &cvs[..depth] {
            hand::push(&mut h0, *cv);
            unsafe { b_push(&mut l0 as *mut LStack as u64, cv.as_ptr() as u64) };
        }
        let hand_ns = least(15, 200_000, || {
            let mut h = h0.clone();
            hand::merge(&mut h, &key, 0, 1);
            std::hint::black_box(&h);
        });
        let hand_clone = least(15, 200_000, || {
            let h = h0.clone();
            std::hint::black_box(&h);
        });
        let mut times = vec![];
        for m in [a_merge as MergeFn, b_merge as MergeFn] {
            let ns = least(15, 200_000, || {
                let mut l = LStack { len: depth as u64, pad: [0; 3], cvs: l0.cvs };
                unsafe { m(&mut l as *mut LStack as u64, key.as_ptr() as u64, 0, plat, 1) };
                std::hint::black_box(&l);
            });
            times.push(ns);
        }
        let l_clone = least(15, 200_000, || {
            let l = LStack { len: depth as u64, pad: [0; 3], cvs: l0.cvs };
            std::hint::black_box(&l);
        });
        println!("merge {depth} to 1, ns a call (the copy of the stack taken off): hand Rust {:.1}, way A {:.1}, way B {:.1}",
                 hand_ns - hand_clone, times[0] - l_clone, times[1] - l_clone);
    }
    let h = blake3_servil_core::Hash::from_bytes(hash);
    let hand_hex = least(15, 2_000_000, || {
        std::hint::black_box(std::hint::black_box(&h).to_hex());
    });
    let mut out = [0u8; 64];
    let mut hex = vec![];
    for x in [a_to_hex as HexFn, b_to_hex as HexFn] {
        hex.push(least(15, 2_000_000, || {
            unsafe { x(out.as_mut_ptr() as u64, std::hint::black_box(hash.as_ptr()) as u64) };
            std::hint::black_box(&out);
        }));
    }
    println!("to_hex, ns a call: hand Rust (table) {:.1}, way A {:.1}, way B {:.1}", hand_hex, hex[0], hex[1]);
    let mut l = LStack { len: 0, pad: [0; 3], cvs: [[0; 32]; 55] };
    let mut hs = hand::new_stack();
    let cv = cvs[0];
    let hand_push = least(15, 2_000_000, || {
        hand::clear(&mut hs);
        hand::push(&mut hs, std::hint::black_box(cv));
    });
    let mut pushes = vec![];
    for p in [a_push as PushFn, b_push as PushFn] {
        pushes.push(least(15, 2_000_000, || {
            l.len = 0;
            unsafe { p(&mut l as *mut LStack as u64, std::hint::black_box(cv.as_ptr()) as u64) };
        }));
    }
    println!("push, ns a call: hand Rust {:.1}, way A {:.1}, way B {:.1}", hand_push, pushes[0], pushes[1]);
}
