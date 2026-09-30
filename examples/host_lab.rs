//! Calls after register work and after memory-working gaps in a fresh
//! process. Every interval and count read belongs to clocks. The buffer
//! sizes are a diagnostic axis; the frozen benchmark keeps its 128 MiB.
use std::hint::black_box;
use clocks::{Batch, Counts};

fn show(values: Vec<u128>) -> String {
    let mut values = values;
    values.sort_unstable();
    let n = values.len();
    clocks::speeds::speeds(&values).into_iter().map(|speed| {
        let ns = (speed.median + (1u128 << 63)) >> 64;
        let share = (speed.count * 1000 + n / 2) / n;
        format!("{ns} ({share}/1000)")
    }).collect::<Vec<_>>().join(" | ")
}

fn main() {
    blake3_servil::initialize();
    let work: Vec<u8> = (0..128 * 1024 * 1024usize).map(|i| (i / 64) as u8).collect();
    let input: Vec<u8> = (0..65536usize).map(|i| (i / 8) as u8).collect();
    let mut produced = vec![0u8; input.len()];
    let lengths = [64, 512, 1024, 4096, 65536];
    let gaps = [0, 8 * 1024 * 1024, 128 * 1024 * 1024];
    let mut samples: Vec<Vec<Batch>> = (0..lengths.len() * gaps.len()).map(|_| Vec::new()).collect();
    let mut raw = String::from("round,length,work_bytes,calls,wall_ns,p_cycles,p_instructions,p_time_ns,e_cycles,e_instructions,e_time_ns\n");
    for round in 0..48 {
        for offset in 0..lengths.len() {
            let l = (offset + round) % lengths.len();
            let len = lengths[l];
            for g in (0..gaps.len()).map(|offset| (offset + round) % gaps.len()) {
                let bytes = gaps[g];
                let hash = |buffer: &[u8]| { black_box(blake3_servil::hash(black_box(buffer))); };
                let measured = if bytes == 0 {
                    produced[..len].copy_from_slice(&input[..len]);
                    clocks::measure_after_gaps(4, 1_000_000, || hash(&produced[..len]))
                } else {
                    clocks::measure_after_gaps_prepared(4, 1_000_000, &work[..bytes], &mut produced[..len],
                        |buffer| buffer.copy_from_slice(black_box(&input[..len])), hash).calls
                };
                let Counts { p, e } = measured.counts.unwrap_or_default();
                raw += &format!("{round},{len},{bytes},{},{},{},{},{},{},{},{}\n", measured.calls, measured.wall_ns,
                    p.cycles,p.instructions,p.time_ns,e.cycles,e.instructions,e.time_ns);
                samples[l * gaps.len() + g].push(measured);
            }
        }
    }
    std::fs::write("gap-samples.csv", raw).unwrap();
    let mut report = String::new();
    for (l, len) in lengths.into_iter().enumerate() {
        for (g, bytes) in gaps.into_iter().enumerate() {
            let batches = &samples[l * gaps.len() + g];
            let wall = show(batches.iter().map(|b| clocks::speeds::per_unit(b.wall_ns, b.calls)).collect());
            let cycles = if batches.iter().all(|b| b.counts.is_some()) {
                let cycles = show(batches.iter().map(|b| { let c=b.counts.unwrap(); clocks::speeds::per_unit(c.p.cycles+c.e.cycles,b.calls) }).collect());
                let mhz = show(batches.iter().map(|b| u128::from(b.counts.unwrap().mhz()) << 64).collect());
                format!("cycles/call {cycles}; MHz {mhz}")
            } else { "cycle counts unavailable".into() };
            report += &format!("length {len}; work {bytes}: ns/call {wall}; {cycles}\n");
        }
    }
    print!("{report}");
    std::fs::write("gap-report.txt", report).unwrap();
}
