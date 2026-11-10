//! A probe for the Pipeline's design (BLAKE3 #356): what does it cost a
//! stream of short messages when each message's bytes lie in a room of its
//! own (16 KiB apart), against lying back to back as in today's ring?
//!
//! It uses today's stream and its lent call, twice: on bytes already in
//! place, and with the program copying each message into its place first,
//! as a producer fills a room. It leaves out the Pipeline's own calls and
//! its wait for a free room.
//!
//!     cargo run --release --example room_stride_probe
//!
//! Prints, for each message length, the median ns/B of each layout over
//! alternating rounds.
use blake3_servil::throughput::Block;
use blake3_servil::{Hash, Mode};
use std::time::Instant;

const ROOM: usize = 16 * 1024;
const MESSAGES: usize = 100_000;
const ROUNDS: usize = 41;

/// One stream of MESSAGES messages of `len` bytes, message i at
/// `starts[i % starts.len()]` blocks into `memory`: nanoseconds. With
/// `write`, the program first copies the message's bytes there from
/// `source`, as a producer fills a room.
///
/// Sound with `write` only because a place is written again no sooner than
/// `starts.len()` messages later, and the stream keeps at most 1,024
/// entries in flight (main() asks for more places than that).
fn round(memory: *mut Block, starts: &[usize], len: usize, digests: &mut [Hash], write: Option<&[Block]>) -> u128 {
    let blocks = len.div_ceil(64);
    let begin = Instant::now();
    blake3_servil::throughput::stream(
        Mode::Plain,
        |_done: &mut [Hash]| {},
        |s| {
            for (i, digest) in digests.iter_mut().enumerate() {
                let at = starts[i % starts.len()];
                if let Some(source) = write {
                    unsafe { core::ptr::copy_nonoverlapping(source.as_ptr(), memory.add(at), blocks) };
                }
                let message: &[Block] = unsafe { core::slice::from_raw_parts(memory.add(at), blocks) };
                s.submit(message, len, digest);
            }
            s.finish();
        },
    );
    begin.elapsed().as_nanos()
}

fn median(mut v: Vec<u128>) -> u128 {
    v.sort_unstable();
    v[v.len() / 2]
}

fn main() {
    blake3_servil::initialize_multithreaded(None);
    // 64 MiB of bytes, every block different: 4,096 rooms.
    const ROOMS: usize = 4096;
    let total_blocks = ROOMS * ROOM / 64;
    let mut memory: Vec<Block> = (0..total_blocks as u32).map(|i| Block(i.to_le_bytes().repeat(16).try_into().unwrap())).collect();
    let source: Vec<Block> = (0..64u32).map(|i| Block((i ^ 0x5a5a).to_le_bytes().repeat(16).try_into().unwrap())).collect();
    let memory_ptr = memory.as_mut_ptr();
    let mut digests = vec![Hash::from_bytes([0; 32]); MESSAGES];
    println!("{MESSAGES} messages a stream, {ROUNDS} rounds a layout, alternating; median ns/B, and against back to back");
    for write in [false, true] {
        println!("{}", if write { "the program writes each message into its place, then hands it over:" } else { "the bytes already in place:" });
        for len in [64usize, 256, 1024, 4096] {
            let blocks = len.div_ceil(64);
            // Back to back: 2 MiB of places, or 2,048 messages' worth where that is more.
            let packed_count = ((2 << 20) / 64 / blocks).max(2048);
            let packed: Vec<usize> = (0..packed_count).map(|i| i * blocks).collect();
            let rooms: Vec<usize> = (0..ROOMS).map(|i| i * ROOM / 64).collect();
            let layouts: [(&str, Vec<usize>); 2] = [("back to back", packed), ("a room each (16 KiB apart)", rooms)];
            let src = write.then_some(&source[..blocks]);
            for (name, starts) in &layouts {
                assert!(starts.len() >= 2048, "{name}: a place comes round after the stream's 1,024 entries");
                round(memory_ptr, starts, len, &mut digests, src);
                for i in [0usize, 1, 77, MESSAGES - 1] {
                    let at = starts[i % starts.len()];
                    let bytes: Vec<u8> = unsafe { core::slice::from_raw_parts(memory_ptr.add(at), blocks) }.iter().flat_map(|b| b.0).take(len).collect();
                    assert_eq!(digests[i], blake3_servil::convenience::hash(&bytes), "{name}, message {i}");
                }
            }
            let mut times: [Vec<u128>; 2] = Default::default();
            for r in 0..ROUNDS {
                for k in 0..2 {
                    let k = (k + r) % 2;
                    times[k].push(round(memory_ptr, &layouts[k].1, len, &mut digests, src));
                }
            }
            let base = median(times[0].clone());
            for (k, (name, _)) in layouts.iter().enumerate() {
                let m = median(times[k].clone());
                println!("  {len:>5} B  {name:<28} {:.4} ns/B  {:6.1} ns a message  x{:.3}", m as f64 / (MESSAGES * len) as f64, m as f64 / MESSAGES as f64, m as f64 / base as f64);
            }
        }
    }
    drop(memory);
}
