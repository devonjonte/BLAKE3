//! A probe, never to land: many messages open at once, their pieces arriving
//! interleaved (a server's uploads), fed three ways in one program:
//!
//!   each-st   `throughput::update_each`, then `finalize_each` (the bench's turn cell, single-threaded)
//!   each-mt   `throughput::update_each_multithreaded`, then `finalize_each`
//!   pipeline  `throughput::Pipeline`
//!
//! Two workloads. `short`: 1,024 open messages of 1 KiB in 256-byte pieces, a
//! turn one piece of every message (the bench's `1024 x 1 KiB` turn point).
//! `long`: 64 open messages of 1 MiB in 16 KiB pieces.
//!
//! Every arm pays one copy per arriving piece (the read from the network): the
//! `each` arms into a receive buffer that a turn's pieces fill, the Pipeline
//! arm to where its contract needs the bytes. A Pipeline takes a message in
//! whole 64 KiB Rooms, except its last commit. So for `short` the caller
//! gathers a message in a buffer of its own and copies it into a Room when
//! its last piece is in (a second copy); for `long` each open message holds
//! a Room, arrivals land in it, and it is committed when full.
//!
//! Arms run in rounds, in rotating order; a round times CYCLES whole cycles
//! (every message from first piece to digest). Prints, per arm, the fastest
//! and median round in ns per byte of wall time, and process CPU time per
//! byte. `turn_pipeline_probe [ROUNDS]`.
use blake3_servil::Mode;
use blake3_servil::convenience::Hasher;
use blake3_servil::throughput::{Event, Limits, Pipeline, ROOM_LEN, Room, block_on, finalize_each, update_each, update_each_multithreaded};
use std::hint::black_box;
use std::time::Instant;

struct Work {
    name: &'static str,
    messages: usize,
    len: usize,
    piece: usize,
    cycles: usize,
}

fn cpu_ns() -> u64 {
    let mut u: libc::rusage = unsafe { std::mem::zeroed() };
    unsafe { libc::getrusage(libc::RUSAGE_SELF, &mut u) };
    let t = |v: libc::timeval| v.tv_sec as u64 * 1_000_000_000 + v.tv_usec as u64 * 1_000;
    t(u.ru_utime) + t(u.ru_stime)
}

/// The source: message `i`'s bytes are `source[i * len..][..len]`.
fn source(w: &Work) -> Vec<u8> {
    let mut x = 0x9E37_79B9_7F4A_7C15u64;
    (0..w.messages * w.len)
        .map(|_| {
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            x as u8
        })
        .collect()
}

/// One cycle through the Hashers: a turn's pieces read into the receive
/// buffer, one call for the turn, the digests when the messages end.
fn each_cycle(w: &Work, src: &[u8], hashers: &mut [Hasher], receive: &mut [u8], which: &[usize], out: &mut [[u8; 32]], update: fn(&mut [Hasher], &[(usize, &[u8])])) {
    let turns = w.len / w.piece;
    for t in 0..turns {
        for i in 0..w.messages {
            receive[i * w.piece..][..w.piece].copy_from_slice(&black_box(src)[i * w.len + t * w.piece..][..w.piece]);
        }
        let pieces: Vec<(usize, &[u8])> = (0..w.messages).map(|i| (i, &receive[i * w.piece..][..w.piece])).collect();
        update(hashers, &pieces);
    }
    finalize_each(hashers, which, out);
    black_box(&out);
}

fn take(pipe: &mut Pipeline<usize>, out: &mut [[u8; 32]]) {
    let event = match pipe.next_event() {
        Some(e) => e,
        None => {
            block_on(pipe.ready());
            pipe.next_event().expect("ready supplies an event")
        }
    };
    let Event::Hashed { tag, hash, .. } = event else { panic!("a hash") };
    out[tag] = *hash.as_bytes();
}

/// One cycle through the Pipeline, short messages: each gathered in the
/// caller's buffer, given whole when its last piece is in.
fn pipeline_short(w: &Work, src: &[u8], pipe: &mut Pipeline<usize>, gather: &mut [u8], out: &mut [[u8; 32]]) {
    let turns = w.len / w.piece;
    let mut room: Option<Room> = None;
    let mut pending = 0;
    for t in 0..turns {
        for i in 0..w.messages {
            gather[i * w.len + t * w.piece..][..w.piece].copy_from_slice(&black_box(src)[i * w.len + t * w.piece..][..w.piece]);
            if t + 1 == turns {
                if pending == w.messages {
                    take(pipe, out);
                    pending -= 1;
                }
                let mut message = block_on(pipe.message(i, Some(w.len as u64)));
                if room.as_ref().is_none_or(|r| r.len() < w.len) {
                    drop(room.take());
                    room = Some(block_on(pipe.room()));
                }
                let r = room.as_mut().unwrap();
                r.bytes_mut()[..w.len].copy_from_slice(&gather[i * w.len..][..w.len]);
                pipe.commit(&mut message, r, w.len);
                pipe.end(message);
                pending += 1;
            }
        }
    }
    drop(room);
    for _ in 0..pending {
        take(pipe, out);
    }
    black_box(&out);
}

/// One cycle through the Pipeline, long messages: each open message holds a
/// Room, arrivals land in it, and it is committed when full.
fn pipeline_long(w: &Work, src: &[u8], pipe: &mut Pipeline<usize>, out: &mut [[u8; 32]]) {
    let turns = w.len / w.piece;
    let mut open: Vec<_> = (0..w.messages).map(|i| (block_on(pipe.message(i, Some(w.len as u64))), block_on(pipe.room()), 0usize)).collect();
    for t in 0..turns {
        for (i, (message, room, filled)) in open.iter_mut().enumerate() {
            room.bytes_mut()[*filled..][..w.piece].copy_from_slice(&black_box(src)[i * w.len + t * w.piece..][..w.piece]);
            *filled += w.piece;
            if *filled == ROOM_LEN {
                pipe.commit(message, room, ROOM_LEN);
                *filled = 0;
                if t + 1 < turns {
                    *room = block_on(pipe.room());
                }
            }
        }
    }
    for (message, room, filled) in open {
        assert_eq!(filled, 0, "the long workload's messages are whole Rooms");
        drop(room);
        pipe.end(message);
    }
    for _ in 0..w.messages {
        take(pipe, out);
    }
    black_box(&out);
}

fn main() {
    blake3_servil::initialize_multithreaded(None);
    let rounds: usize = std::env::args().nth(1).map_or(15, |a| a.parse().unwrap());
    let works = [
        Work { name: "short: 1024 open x 1 KiB, 256 B pieces", messages: 1024, len: 1024, piece: 256, cycles: 200 },
        Work { name: "long: 64 open x 1 MiB, 16 KiB pieces", messages: 64, len: 1 << 20, piece: 16 << 10, cycles: 6 },
    ];
    for w in &works {
        let src = source(w);
        let bytes = (w.messages * w.len * w.cycles) as f64;
        let which: Vec<usize> = (0..w.messages).collect();
        let mut hashers: Vec<Hasher> = (0..w.messages).map(|_| Hasher::new(Mode::Plain, None)).collect();
        let mut receive = vec![0u8; w.messages * w.piece];
        let mut gather = vec![0u8; w.messages * w.len.min(ROOM_LEN)];
        let short = w.len < ROOM_LEN;
        // Rooms: the open messages' own, and as many again in the workers' hands.
        let limits = if short { Limits { messages: w.messages, rooms: 16 } } else { Limits { messages: w.messages, rooms: 2 * w.messages + 16 } };
        let mut pipe: Pipeline<usize> = Pipeline::new(Mode::Plain, limits);
        let mut outs = [vec![[0u8; 32]; w.messages], vec![[0u8; 32]; w.messages], vec![[0u8; 32]; w.messages]];
        let names = ["each-st", "each-mt", "pipeline"];
        let mut run = |arm: usize, outs: &mut [Vec<[u8; 32]>; 3]| match arm {
            0 => each_cycle(w, &src, &mut hashers, &mut receive, &which, &mut outs[0], update_each),
            1 => each_cycle(w, &src, &mut hashers, &mut receive, &which, &mut outs[1], update_each_multithreaded),
            _ if short => pipeline_short(w, &src, &mut pipe, &mut gather, &mut outs[2]),
            _ => pipeline_long(w, &src, &mut pipe, &mut outs[2]),
        };
        // Warm up, and check the three agree with the one-call hash.
        for arm in 0..3 {
            run(arm, &mut outs);
            run(arm, &mut outs);
        }
        for i in 0..w.messages {
            let want = *blake3_servil::convenience::hash(&src[i * w.len..][..w.len]).as_bytes();
            assert!(outs.iter().all(|o| o[i] == want), "message {i}: an arm's digest differs");
        }
        let mut wall = [Vec::new(), Vec::new(), Vec::new()];
        let mut cpu = [Vec::new(), Vec::new(), Vec::new()];
        for r in 0..rounds {
            for k in 0..3 {
                let arm = (r + k) % 3;
                let (c0, t0) = (cpu_ns(), Instant::now());
                for _ in 0..w.cycles {
                    run(arm, &mut outs);
                }
                wall[arm].push(t0.elapsed().as_nanos() as f64 / bytes);
                cpu[arm].push((cpu_ns() - c0) as f64 / bytes);
            }
        }
        println!("{}  ({} rounds of {} cycles, {:.0} MiB a round)", w.name, rounds, w.cycles, bytes / (1 << 20) as f64);
        println!("  {:9} {:>12} {:>12} {:>14}", "arm", "fastest ns/B", "median ns/B", "median CPU ns/B");
        for arm in 0..3 {
            wall[arm].sort_by(f64::total_cmp);
            cpu[arm].sort_by(f64::total_cmp);
            println!("  {:9} {:>12.4} {:>12.4} {:>14.4}", names[arm], wall[arm][0], wall[arm][rounds / 2], cpu[arm][rounds / 2]);
        }
    }
}
