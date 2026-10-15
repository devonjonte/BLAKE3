//! hash() nonstop on one thread, per length: mean ns per call
//! (clocks::measure 2 ms batches, clocks::summary mean). One line per length,
//! then the run's load description. Lengths are visited in the order given
//! by the arguments, so a collector can mirror the order between processes.
fn main() {
    blake3_servil::initialize();
    let lengths: Vec<usize> = std::env::args().skip(1).map(|a| a.parse().expect("lengths in bytes")).collect();
    assert!(!lengths.is_empty(), "give lengths in bytes");
    let input: Vec<u8> = (0..4096).map(|i| (i % 251) as u8).collect();
    for &len in &lengths {
        let message = &input[..len];
        let batches = clocks::measure(48, 2_000_000, || {
            std::hint::black_box(blake3_servil::hash(std::hint::black_box(message)));
        });
        let mean = clocks::summary::mean(batches.iter().map(|b| (b.wall_ns, b.calls)));
        let milli = (mean * 1000 + (1 << 63)) >> 64;
        println!("{len}\t{}.{:03}", milli / 1000, milli % 1000);
    }
    println!("load\t{}", clocks::load::describe(&clocks::load::windows()));
}
