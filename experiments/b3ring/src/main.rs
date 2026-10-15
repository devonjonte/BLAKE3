//! An experiment: b3sum's job (hash each file named, print its digest and
//! name in order) with io_uring reading the files into a fixed set of
//! buffers registered with the kernel, and hashing threads reading those
//! buffers in place. A file up to PIECE bytes is one read and one hash(); a
//! longer one is read in PIECE-byte pieces, each a whole subtree whose
//! chaining value a thread computes (hazmat), merged in order on this
//! thread. Up to BUFFERS reads are in flight at once. `--direct` first
//! opens files with O_DIRECT (reads bypass the page cache).
use blake3_servil::hazmat::{merge_subtrees_non_root, merge_subtrees_root, ChainingValue, HasherExt, Mode};
use io_uring::{opcode, types, IoUring};
use std::collections::VecDeque;
use std::fs::File;
use std::os::fd::AsRawFd;
use std::os::unix::fs::OpenOptionsExt;
use std::sync::{mpsc, Arc, Condvar, Mutex};

const PIECE: usize = 1 << 20;
const BUFFERS: usize = 64;

/// One buffer's worth of work for a hashing thread.
struct Job {
    file: usize,
    piece: usize,
    /// The piece's offset in its file; `None` for a whole file (hashed as the root).
    offset: Option<u64>,
    buffer: usize,
    len: usize,
}

enum Done {
    Root { file: usize, hash: blake3_servil::Hash, buffer: usize },
    Piece { file: usize, piece: usize, cv: ChainingValue, buffer: usize },
}

struct Buffers {
    base: *mut u8,
    /// Each buffer's length.
    piece: usize,
}
// Sound: each buffer is touched by one thread at a time: the kernel while
// its read is in flight, then the thread hashing it, then free again.
unsafe impl Send for Buffers {}
unsafe impl Sync for Buffers {}
impl Buffers {
    fn get(&self, i: usize, len: usize) -> &[u8] {
        // Sound: buffer i is PIECE bytes inside the allocation, and its read completed.
        unsafe { std::slice::from_raw_parts(self.base.add(i * self.piece), len) }
    }
}

/// A file being hashed: its pieces' values, merged in order as they come.
struct FileState {
    name: String,
    len: u64,
    pieces: usize,
    /// Pieces' values that came before the next one in order.
    waiting: Vec<Option<ChainingValue>>,
    next: usize,
    stack: Vec<ChainingValue>,
    hash: Option<blake3_servil::Hash>,
}

impl FileState {
    fn take(&mut self, piece: usize, cv: ChainingValue) {
        self.waiting[piece] = Some(cv);
        while self.next < self.pieces {
            let Some(cv) = self.waiting[self.next].take() else { break };
            // Lazy merging, as the Hasher's stack: before pushing piece n,
            // merge down to as many values as n has 1 bits.
            while self.stack.len() > self.next.count_ones() as usize {
                let right = self.stack.pop().unwrap();
                let left = self.stack.pop().unwrap();
                self.stack.push(merge_subtrees_non_root(&left, &right, Mode::Hash));
            }
            self.stack.push(cv);
            self.next += 1;
        }
        if self.next == self.pieces {
            let mut right = self.stack.pop().unwrap();
            while self.stack.len() > 1 {
                let left = self.stack.pop().unwrap();
                right = merge_subtrees_non_root(&left, &right, Mode::Hash);
            }
            let left = self.stack.pop().unwrap();
            self.hash = Some(merge_subtrees_root(&left, &right, Mode::Hash));
        }
    }
}

fn main() {
    blake3_servil::initialize();
    let mut names: Vec<String> = std::env::args().skip(1).collect();
    let direct = names.first().is_some_and(|a| a == "--direct");
    if direct {
        names.remove(0);
    }
    // Every read to make, in order: (file, piece, offset, len).
    let mut files: Vec<FileState> = Vec::new();
    let mut handles: Vec<File> = Vec::new();
    let mut reads: VecDeque<(usize, usize, u64, usize)> = VecDeque::new();
    for name in &names {
        let mut options = std::fs::OpenOptions::new();
        options.read(true);
        if direct {
            options.custom_flags(libc::O_DIRECT);
        }
        let file = options.open(name).unwrap_or_else(|e| panic!("{name}: {e}"));
        let len = file.metadata().unwrap().len();
        let pieces = if len as usize <= PIECE { 1 } else { (len as usize).div_ceil(PIECE) };
        let index = files.len();
        for piece in 0..pieces {
            let offset = (piece * PIECE) as u64;
            reads.push_back((index, piece, offset, (len - offset).min(PIECE as u64) as usize));
        }
        files.push(FileState { name: name.clone(), len, pieces, waiting: vec![None; pieces], next: 0, stack: Vec::new(), hash: None });
        handles.push(file);
    }

    // The buffers, as many and as long as the reads need (up to BUFFERS of
    // PIECE bytes), page-aligned (O_DIRECT needs it), registered with the ring.
    let longest = reads.iter().map(|r| r.3).max().unwrap_or(0);
    let piece = longest.div_ceil(4096).max(1) * 4096;
    let count = reads.len().clamp(1, BUFFERS);
    let layout = std::alloc::Layout::from_size_align(count * piece, 4096).unwrap();
    // Sound: a nonzero size.
    let base = unsafe { std::alloc::alloc(layout) };
    assert!(!base.is_null());
    let buffers = Arc::new(Buffers { base, piece });
    let mut ring = IoUring::new(BUFFERS as u32).expect("io_uring");
    let iovecs: Vec<libc::iovec> = (0..count).map(|i| libc::iovec { iov_base: unsafe { base.add(i * piece) }.cast(), iov_len: piece }).collect();
    // Sound: the buffers live until the process ends.
    unsafe { ring.submitter().register_buffers(&iovecs) }.expect("register buffers");

    // Hashing threads: a job list and the results back.
    let jobs: Arc<(Mutex<VecDeque<Job>>, Condvar)> = Arc::new((Mutex::new(VecDeque::new()), Condvar::new()));
    let (done_tx, done_rx) = mpsc::channel::<Done>();
    // As many threads as reads can use at once, up to one per CPU but this one.
    let threads = std::thread::available_parallelism().map_or(1, |n| n.get()).saturating_sub(1).clamp(1, count);
    for _ in 0..threads {
        let (jobs, done, buffers) = (jobs.clone(), done_tx.clone(), buffers.clone());
        std::thread::spawn(move || loop {
            let job = {
                let mut list = jobs.0.lock().unwrap();
                loop {
                    if let Some(job) = list.pop_front() {
                        break job;
                    }
                    list = jobs.1.wait(list).unwrap();
                }
            };
            let bytes = buffers.get(job.buffer, job.len);
            let result = match job.offset {
                None => Done::Root { file: job.file, hash: blake3_servil::hash(bytes), buffer: job.buffer },
                Some(offset) => {
                    let mut hasher = blake3_servil::Hasher::new();
                    hasher.set_input_offset(offset).update(bytes);
                    Done::Piece { file: job.file, piece: job.piece, cv: hasher.finalize_non_root(), buffer: job.buffer }
                }
            };
            done.send(result).unwrap();
        });
    }

    let mut free: Vec<usize> = (0..count).rev().collect();
    // The read in flight in each buffer: (file, piece, offset, len).
    let mut in_flight: Vec<Option<(usize, usize, u64, usize)>> = vec![None; count];
    let mut printed = 0;
    let mut out = String::new();
    let mut reading = 0;
    while printed < files.len() {
        // Fill every free buffer with the next read.
        while let (Some(&buffer), Some(&read)) = (free.last(), reads.front()) {
            free.pop();
            reads.pop_front();
            let (file, _, offset, len) = read;
            // O_DIRECT reads whole blocks: round the length up (the read stops at the end of the file).
            let request = if direct { len.div_ceil(4096) * 4096 } else { len };
            let entry = opcode::ReadFixed::new(types::Fd(handles[file].as_raw_fd()), unsafe { base.add(buffer * piece) }, request as u32, buffer as u16)
                .offset(offset)
                .build()
                // Punted to the kernel's worker threads, so cached files'
                // copies run on several CPUs at once (inline, this thread
                // copied every read alone).
                .flags(io_uring::squeue::Flags::ASYNC)
                .user_data(buffer as u64);
            // Sound: the buffer is free and registered, and stays put until the read completes.
            unsafe { ring.submission().push(&entry) }.expect("room in the submission queue");
            in_flight[buffer] = Some(read);
            reading += 1;
        }
        // Wait for a read or a result, whichever comes; hand finished reads to the threads.
        if reading > 0 {
            ring.submit_and_wait(if done_rx_try(&done_rx, &mut files, &mut free) { 0 } else { 1 }).expect("io_uring submit");
            let completed: Vec<(u64, i32)> = ring.completion().map(|c| (c.user_data(), c.result())).collect();
            for (buffer, result) in completed {
                let buffer = buffer as usize;
                let (file, piece, offset, len) = in_flight[buffer].take().unwrap();
                assert!(result >= 0, "{}: read failed: {}", files[file].name, std::io::Error::from_raw_os_error(-result));
                // A short read (a buffered read may return less): read the rest synchronously.
                let mut got = result as usize;
                while got < len {
                    // Sound: the buffer is this thread's until its job is queued.
                    let rest = unsafe { std::slice::from_raw_parts_mut(base.add(buffer * piece + got), len - got) };
                    let n = std::os::unix::fs::FileExt::read_at(&handles[file], rest, offset + got as u64).expect("read");
                    assert!(n > 0, "{}: file shrank", files[file].name);
                    got += n;
                }
                reading -= 1;
                let job = Job { file, piece, offset: (files[file].pieces > 1).then_some(offset), buffer, len };
                jobs.0.lock().unwrap().push_back(job);
                jobs.1.notify_one();
            }
        } else {
            let done = done_rx.recv().unwrap();
            finish_one(done, &mut files, &mut free);
        }
        while done_rx_try(&done_rx, &mut files, &mut free) {}
        while printed < files.len() && files[printed].hash.is_some() {
            out.push_str(&format!("{}  {}\n", files[printed].hash.unwrap().to_hex(), files[printed].name));
            printed += 1;
        }
        if out.len() > 1 << 16 || printed == files.len() {
            print!("{out}");
            out.clear();
        }
    }
    let _ = files.iter().map(|f| f.len).sum::<u64>();
}

/// Take one result if any came: whether one did.
fn done_rx_try(rx: &mpsc::Receiver<Done>, files: &mut [FileState], free: &mut Vec<usize>) -> bool {
    match rx.try_recv() {
        Ok(done) => {
            finish_one(done, files, free);
            true
        }
        Err(_) => false,
    }
}

fn finish_one(done: Done, files: &mut [FileState], free: &mut Vec<usize>) {
    match done {
        Done::Root { file, hash, buffer } => {
            files[file].hash = Some(hash);
            free.push(buffer);
        }
        Done::Piece { file, piece, cv, buffer } => {
            files[file].take(piece, cv);
            free.push(buffer);
        }
    }
}
