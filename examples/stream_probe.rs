//! `stream` (messages borrowed, hashed in place) against `Queue::messages`
//! (owned buffers cycled back through a channel, bench-hashes' pattern):
//! the same messages, already in memory, in each; neither copies.
//!
//!   stream_probe samples MODE OUT [LEN...]
//!       MODE stream | queue: each length (default 64 B to 1 MiB), one
//!       bench-hashes samples v4 file, for `bench-hashes compare`
//!
//! Each sample is a clocks::measure batch of 1024 messages; the file's
//! header records the CPUs busy during each length (clocks::threads).
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

/// One mode's batches at messages of `len` bytes (1 MiB: 64 a batch).
fn measure(mode: &str, len: usize) -> (Vec<clocks::Batch>, usize) {
    let per_call = if len >= 1 << 20 { 64 } else { PER_CALL };
    let messages: Vec<Vec<u8>> = (0..per_call).map(|m| (0..len).map(|i| ((i + m) % 251) as u8).collect()).collect();
    let batches = match mode {
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
        _ => panic!("stream_probe samples stream|queue OUT"),
    };
    (batches, per_call)
}

fn main() {
    blake3_servil::initialize_multithreaded();
    let args: Vec<String> = std::env::args().skip(1).collect();
    assert_eq!(args[0], "samples", "stream_probe samples MODE OUT");
    let (which, out) = (args[1].as_str(), &args[2]);
    let (mut rows, mut busy) = (String::new(), String::new());
    let lens: Vec<usize> = if args.len() > 3 { args[3..].iter().map(|a| a.parse().unwrap()).collect() } else { LENS.to_vec() };
    for len in lens {
        let before = clocks::threads::snapshot();
        let started = clocks::now();
        let (batches, per_call) = measure(which, len);
        let wall = clocks::since_ns(started);
        if let (Some(b), Some(a)) = (before, clocks::threads::snapshot()) {
            let total: u64 = clocks::threads::since(&b, &a).iter().map(|x| x.cpu_ns).sum();
            busy += &format!("# cpus busy at {len} B: {}.{:02}\n", total / wall, total % wall * 100 / wall);
        }
        let samples: Vec<String> = batches.iter().map(|b| format!("{}/{}", b.wall_ns, b.calls * (per_call * len) as u64)).collect();
        let starts: Vec<String> = batches.iter().map(|b| (b.started_ns / 1_000_000).to_string()).collect();
        rows += &format!("stream\tsolo\tOwnedMessages\t{len} B\tB\t{}\t{}\n", samples.join(","), starts.join(","));
    }
    let load = clocks::load::describe(&clocks::load::windows());
    std::fs::write(out, format!("# bench-hashes samples v4\n# probe: stream_probe {which}\n# load: {load}\n# power: not reported by this probe\n{busy}contender\tscenario\tuse_case\tpoint\tunit\tns/units\tstart ms\n{rows}")).unwrap();
}
