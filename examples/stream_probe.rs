//! `stream` (messages borrowed, hashed in place) against `Queue::messages`
//! (owned buffers cycled back through a channel, bench-hashes' pattern):
//! the same messages, already in memory, in each; neither copies.
//!
//!   stream_probe samples API OUT [LEN...]
//!       (API written: each message read straight into the stream's bytes
//!       (submit_with); rounds: each round of messages read into the program's
//!       buffers, then a stream of them; queue-read: each read into a free
//!       buffer, then Queue::messages, as bench-hashes' ContinuousMessages)
//!       API stream | queue | new (lone messages only: a stream a message),
//!       each length (default 64 B to 1 MiB), one bench-hashes samples v4
//!       file for `bench-hashes compare`, with three scenarios:
//!       solo   one program's messages back to back (a sample: 1024
//!              messages, 64 at 1 MiB; ns per byte)
//!       two    two programs' at once, each as solo (both threads' samples)
//!       lone   one message after a 1 ms idle gap, its digest awaited (a
//!              sample: 25 messages; ns per message)
//!
//! The file's header records the CPUs busy during each cell (clocks::threads).
use std::sync::mpsc;

const PER_CALL: usize = 1024;
const LENS: [usize; 7] = [64, 256, 1024, 4096, 16384, 65536, 1 << 20];

struct Back(mpsc::SyncSender<Vec<u8>>);
impl blake3_servil::MessageHandler for Back {
    type Buffer = Vec<u8>;
    fn hashed(&mut self, buffer: Vec<u8>, hash: blake3_servil::Hash) {
        std::hint::black_box(hash);
        self.0.send(buffer).unwrap();
    }
}

/// A sample: wall ns, units (bytes or messages), start ms.
type Sample = (u64, u64, u64);

/// One mode's batches at messages of `len` bytes (1 MiB: 64 a batch).
fn solo(api: &str, len: usize) -> Vec<Sample> {
    let per_call = if len >= 1 << 20 { 64 } else { PER_CALL };
    let messages: Vec<Vec<u8>> = (0..per_call).map(|m| (0..len).map(|i| ((i + m) % 251) as u8).collect()).collect();
    let batches = match api {
        "stream" => blake3_servil::stream(blake3_servil::Mode::Hash, |s| {
            let b = clocks::measure(64, 2_000_000, || {
                for m in &messages {
                    s.submit(m, |d| {
                        std::hint::black_box(d);
                    });
                }
                s.collect(|d| {
                    std::hint::black_box(d);
                });
            });
            s.finish(|d| {
                std::hint::black_box(d);
            });
            b
        }),
        "written" => blake3_servil::stream(blake3_servil::Mode::Hash, |s| {
            // Each message read straight into the stream's bytes.
            let b = clocks::measure(64, 2_000_000, || {
                for m in &messages {
                    s.submit_with(
                        m.len(),
                        |at, room| room.copy_from_slice(&m[at..][..room.len()]),
                        |d| {
                            std::hint::black_box(d);
                        },
                    );
                }
                s.collect(|d| {
                    std::hint::black_box(d);
                });
            });
            s.finish(|d| {
                std::hint::black_box(d);
            });
            b
        }),
        "rounds" => {
            // A read of each message into the program's buffers, then a
            // stream of them: a buffer is refilled only after its scope.
            let mut buffers = messages.clone();
            clocks::measure(64, 2_000_000, || {
                for (b, m) in buffers.iter_mut().zip(&messages) {
                    b.copy_from_slice(m);
                }
                blake3_servil::stream(blake3_servil::Mode::Hash, |s| {
                    for b in &buffers {
                        s.submit(b, |d| {
                            std::hint::black_box(d);
                        });
                    }
                    s.finish(|d| {
                        std::hint::black_box(d);
                    });
                });
            })
        }
        "queue-read" => {
            // As bench-hashes' ContinuousMessages: each message read into a
            // free buffer, then submitted.
            let (tx, rx) = mpsc::sync_channel::<Vec<u8>>(per_call);
            let queue = blake3_servil::Queue::messages(blake3_servil::Mode::Hash, Back(tx));
            let mut free = messages.clone();
            let b = clocks::measure(64, 2_000_000, || {
                for m in &messages {
                    let mut buf = match free.pop() {
                        Some(b) => b,
                        None => rx.recv().unwrap(),
                    };
                    buf.copy_from_slice(m);
                    queue.submit(buf);
                }
            });
            for _ in free.len()..per_call {
                rx.recv().unwrap();
            }
            b
        }
        "queue" => {
            let (tx, rx) = mpsc::sync_channel::<Vec<u8>>(per_call);
            let queue = blake3_servil::Queue::messages(blake3_servil::Mode::Hash, Back(tx));
            let mut free = messages;
            let b = clocks::measure(64, 2_000_000, || {
                for _ in 0..per_call {
                    queue.submit(match free.pop() {
                        Some(b) => b,
                        None => rx.recv().unwrap(),
                    });
                }
            });
            for _ in free.len()..per_call {
                rx.recv().unwrap();
            }
            b
        }
        _ => panic!("solo and two: stream | queue"),
    };
    batches.iter().map(|b| (b.wall_ns, b.calls * (per_call * len) as u64, b.started_ns / 1_000_000)).collect()
}

/// One message at a time after a 1 ms idle gap, its digest awaited: a
/// server's request, a wait, the next.
fn lone(api: &str, len: usize) -> Vec<Sample> {
    let message: Vec<u8> = (0..len).map(|i| (i % 251) as u8).collect();
    let (batches, calls) = (20, 25);
    let mut unit = ();
    let mut gaps = |f: &mut dyn FnMut()| -> Vec<Sample> {
        (0..batches)
            .map(|_| {
                let started = clocks::now();
                let b = clocks::measure_after_gaps_prepared(calls, clocks::Gap::Idle, 1_000_000, &mut unit, |_| {}, |_| f());
                (b.calls.wall_ns, calls, clocks::since_ns(started) / 1_000_000)
            })
            .collect()
    };
    match api {
        "stream" => blake3_servil::stream(blake3_servil::Mode::Hash, |s| {
            let s = std::cell::RefCell::new(s);
            let samples = gaps(&mut || {
                let mut s = s.borrow_mut();
                s.submit(&message, |d| {
                    std::hint::black_box(d);
                });
                s.finish(|d| {
                    std::hint::black_box(d);
                });
            });
            samples
        }),
        "new" => gaps(&mut || {
            blake3_servil::stream(blake3_servil::Mode::Hash, |s| {
                s.submit(&message, |d| {
                    std::hint::black_box(d);
                });
                s.finish(|d| {
                    std::hint::black_box(d);
                });
            })
        }),
        "queue" => {
            let (tx, rx) = mpsc::sync_channel::<Vec<u8>>(1);
            let queue = blake3_servil::Queue::messages(blake3_servil::Mode::Hash, Back(tx));
            let mut free = Some(message.clone());
            gaps(&mut || {
                queue.submit(free.take().unwrap());
                free = Some(rx.recv().unwrap());
            })
        }
        _ => panic!("lone: stream | queue | new"),
    }
}

fn main() {
    blake3_servil::initialize_multithreaded();
    let args: Vec<String> = std::env::args().skip(1).collect();
    assert_eq!(args[0], "samples", "stream_probe samples API OUT [LEN...]");
    let (api, out) = (args[1].as_str(), &args[2]);
    let lens: Vec<usize> = if args.len() > 3 { args[3..].iter().map(|a| a.parse().unwrap()).collect() } else { LENS.to_vec() };
    let scenarios: &[&str] = match api {
        "new" => &["lone"],
        "rounds" | "queue-read" | "written" => &["solo", "two"],
        _ => &["solo", "two", "lone"],
    };
    let (mut rows, mut busy) = (String::new(), String::new());
    for &scenario in scenarios {
        for &len in &lens {
            let before = clocks::threads::snapshot();
            let started = clocks::now();
            let samples = match scenario {
                "solo" => solo(api, len),
                "two" => std::thread::scope(|t| {
                    let other = t.spawn(|| solo(api, len));
                    let mut samples = solo(api, len);
                    samples.extend(other.join().unwrap());
                    samples
                }),
                _ => lone(api, len),
            };
            let wall = clocks::since_ns(started);
            if let (Some(b), Some(a)) = (before, clocks::threads::snapshot()) {
                let total: u64 = clocks::threads::since(&b, &a).iter().map(|x| x.cpu_ns).sum();
                busy += &format!("# cpus busy, {scenario} {len} B: {}.{:02}\n", total / wall, total % wall * 100 / wall);
            }
            let unit = if scenario == "lone" { "message" } else { "B" };
            let ns: Vec<String> = samples.iter().map(|(w, u, _)| format!("{w}/{u}")).collect();
            let starts: Vec<String> = samples.iter().map(|(_, _, s)| s.to_string()).collect();
            rows += &format!("probe\t{scenario}\tMessages\t{len} B\t{unit}\t{}\t{}\n", ns.join(","), starts.join(","));
        }
    }
    let load = clocks::load::describe(&clocks::load::windows());
    std::fs::write(out, format!("# bench-hashes samples v4\n# probe: stream_probe {api}\n# load: {load}\n# power: not reported by this probe\n{busy}contender\tscenario\tuse_case\tpoint\tunit\tns/units\tstart ms\n{rows}")).unwrap();
}
