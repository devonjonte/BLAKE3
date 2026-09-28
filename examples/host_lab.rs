//! Probe (probe/queue-throughput): the queue's throughput for short
//! messages when the program keeps enough in flight (Little's law), against
//! hash() in a loop and hash_many over the same bytes. The program keeps
//! `flight` buffers, refilling each as the handler hands it back through a
//! channel. Wall time; the threads' cycles are not read here.
use blake3_servil::{Efficiency, Hash, MessageHandler, Mode, Queue};
use std::sync::mpsc;

struct Back(mpsc::Sender<Vec<u8>>);
impl MessageHandler for Back {
    type Buffer = Vec<u8>;
    fn hashed(&mut self, buffer: Vec<u8>, hash: Hash) {
        std::hint::black_box(hash);
        self.0.send(buffer).unwrap();
    }
}

fn main() {
    blake3_servil::initialize_multithreaded();
    for (len, flight) in [(64usize, 64usize), (64, 1024), (64, 4096), (1024, 256), (1024, 1024), (16384, 64), (16384, 256)] {
        let messages = ((256usize << 20) / len).min(4_000_000);
        let input = vec![7u8; len];
        // hash() in a loop over the same bytes, copied as the queue's
        // program copies them.
        let mut buffer = vec![0u8; len];
        let start = clocks::now();
        for _ in 0..messages {
            buffer.copy_from_slice(&input);
            std::hint::black_box(blake3_servil::hash(std::hint::black_box(&buffer)));
        }
        let hash_ns = clocks::since_ns(start);
        for round in 0..3 {

            let (tx, rx) = mpsc::channel();
            let queue = Queue::messages(Mode::Hash, Efficiency::Time, Back(tx));
            let mut free: Vec<Vec<u8>> = (0..flight).map(|_| vec![0u8; len]).collect();
            let start = clocks::now();
            for _ in 0..messages {
                let mut buffer = match free.pop() {
                    Some(buffer) => buffer,
                    None => rx.recv().unwrap(),
                };
                buffer.copy_from_slice(&input);
                queue.submit(buffer);
            }
            for _ in free.len()..flight {
                rx.recv().unwrap();
            }
            let queue_ns = clocks::since_ns(start);
            if round == 2 {

                let per = |ns: u64| ns as f64 / messages as f64;
                println!("{len} B x {messages}, {flight} in flight: queue {:.1} ns/msg, hash() {:.1} ns/msg: queue {:.2}x hash()", per(queue_ns), per(hash_ns), hash_ns as f64 / queue_ns as f64);
            }
        }
    }
    // hash_many over 64-byte messages back to back, 1024 per call.
    let batch = vec![7u8; 64 * 1024];
    let mut out = vec![[0u8; 32]; 1024];
    let start = clocks::now();
    for _ in 0..4000 {
        blake3_servil::hash_many(std::hint::black_box(&batch), 64, &mut out);
    }
    println!("hash_many 64 B: {:.1} ns/msg", clocks::since_ns(start) as f64 / 4_096_000.0);
    let start = clocks::now();
    for _ in 0..4000 {
        blake3_servil::hash_many_multithreaded(std::hint::black_box(&batch), 64, &mut out);
    }
    println!("hash_many_multithreaded 64 B x 1024: {:.1} ns/msg", clocks::since_ns(start) as f64 / 4_096_000.0);
}
