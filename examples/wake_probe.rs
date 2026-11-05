//! wake_probe PAUSE_US VISITS: after a pause of PAUSE_US (0: steady, calls
//! back to back; a sleep otherwise), one call on an input of each size,
//! multithreaded (the pool's workers parked by the pause) and on the
//! caller's thread alone (performance::hash); the schedule shuffled. One line a visit:
//! size_bytes api ns. The caller on CPU 2. For the crossover: below what
//! size, after a pause, is the caller alone faster than waking the pool?
use blake3_servil::performance::{hash_multithreaded, Block};
use blake3_servil::Mode;
use std::time::{Duration, Instant};

fn pin(cpu: usize) {
    unsafe extern "C" {
        fn sched_setaffinity(pid: i32, size: usize, set: *const u64) -> i32;
    }
    let mut set = [0u64; 16];
    set[cpu / 64] |= 1 << (cpu % 64);
    // Sound: `set` is a cpu_set_t of 1024 bits, the calling thread (0).
    assert_eq!(unsafe { sched_setaffinity(0, size_of_val(&set), set.as_ptr()) }, 0);
}

fn main() {
    let a: Vec<String> = std::env::args().collect();
    let (pause_us, visits): (u64, usize) = (a[1].parse().unwrap(), a[2].parse().unwrap());
    blake3_servil::initialize_multithreaded(None);
    pin(2);
    let sizes: Vec<usize> = [64, 128, 256, 512, 1024, 2048, 4096].iter().map(|k| k * 1024).collect();
    let input: Vec<Block> = (0..sizes[sizes.len() - 1] / 64).map(|i| Block([i as u8; 64])).collect();
    let apis = ["mt", "st"];
    let mut sched: Vec<(usize, usize)> =
        (0..visits).flat_map(|_| (0..sizes.len()).flat_map(|s| (0..2).map(move |p| (s, p)))).collect();
    let mut x = 0x9e3779b97f4a7c15u64;
    for i in (1..sched.len()).rev() {
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        sched.swap(i, (x % (i as u64 + 1)) as usize);
    }
    let call = |s: usize, api: usize| -> u64 {
        let blocks = &input[..sizes[s] / 64];
        let t = Instant::now();
        let out = if api == 0 {
            hash_multithreaded(Mode::Plain, blocks, sizes[s])
        } else {
            blake3_servil::performance::hash(Mode::Plain, blocks, sizes[s])
        };
        std::hint::black_box(out);
        t.elapsed().as_nanos() as u64
    };
    for s in 0..sizes.len() {
        for api in 0..2 {
            for _ in 0..5 {
                call(s, api);
            }
        }
    }
    println!("# pause_us {pause_us}");
    for &(s, api) in &sched {
        if pause_us > 0 {
            std::thread::sleep(Duration::from_micros(pause_us));
        }
        let ns = call(s, api);
        println!("{}\t{}\t{ns}", sizes[s], apis[api]);
    }
}
