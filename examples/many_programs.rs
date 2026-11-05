//! bench-hashes #116: N programs at once, each a stream of servil mt. This
//! is one program: it hashes `LEN`-byte messages through a stream for
//! `SECS` seconds and prints its gigabytes a second. A shell starts N of
//! them at once. `many_programs SECS [LEN]`.
use blake3_servil::performance::{stream, Stream};
use blake3_servil::{Hash, Mode};
use std::cell::RefCell;
use std::time::{Duration, Instant};

fn main() {
    blake3_servil::initialize_multithreaded(None);
    let secs: u64 = std::env::args().nth(1).map_or(3, |a| a.parse().unwrap());
    let len: usize = std::env::args().nth(2).map_or(64 << 10, |a| a.parse().unwrap());
    let input: Vec<u8> = (0..len).map(|i| i as u8).collect();
    let mut places: Vec<Hash> = vec![Hash::from([0u8; 32]); 1024];
    let free = RefCell::new(places.chunks_mut(1).collect::<Vec<_>>());
    let end = Instant::now() + Duration::from_secs(secs);
    let start = Instant::now();
    let count = stream(
        Mode::Plain,
        |place: &mut [Hash]| {
            std::hint::black_box(&place[0]);
            free.borrow_mut().push(place);
        },
        |s: &mut Stream<'_, _>| {
            let mut i = 0u64;
            while Instant::now() < end {
                let place = loop {
                    if let Some(p) = free.borrow_mut().pop() {
                        break p;
                    }
                    s.collect();
                };
                s.submit_with(len, |at, room| { room.copy_from_slice(&input[at..][..room.len()]); room.len() }, &mut place[0]);
                i += 1;
            }
            s.finish();
            i
        },
    );
    let dt = start.elapsed().as_secs_f64();
    println!("{:.3}", count as f64 * len as f64 / dt / 1e9);
}
