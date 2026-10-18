//! Many files at once (Linux): each of b3sum's file threads takes its files
//! a batch at a time, opens the batch, and asks the kernel to read each file
//! ahead (posix_fadvise WILLNEED, which starts the reads from storage and
//! returns at once), then reads and hashes each in turn. A tree of small
//! files read from storage keeps the device's queue deep (threads x BATCH
//! reads, where one read a thread kept threads reads); a cached file costs
//! one more system call.
//!
//! Each file is opened, and its metadata read, as before; a regular file
//! below `SMALL` is read whole into the thread's buffer and hashed, and the
//! change check (size and modification time as when opened) follows the
//! read. Larger files, other kinds of file, and any file whose read or check
//! is not exactly as expected go to `hash_path`, as before: the fast path
//! never decides a digest alone.
//!
//! io_uring did the same with more machinery: 4 reads in flight a thread in
//! a ring of its own (x0.866 against the hint's x0.85-0.87 from storage, in
//! the pilot), a dependency, and buffers per read
//! (bench-hashes-validation/b3sum-uring).

use crate::Args;
use std::io::Read;
use std::os::fd::AsRawFd;
use std::path::Path;
use std::sync::atomic::{AtomicUsize, Ordering};

/// Files below this go through the batch; larger ones are mapped or read as
/// before (`hash_path`; MAP_LEN).
const SMALL: u64 = crate::MAP_LEN as u64;

/// Files a thread opens and has read ahead at once: 80 with 20 threads.
/// From storage, 1000 files of 16 KiB took as long at 2, 4, 8 and 16 (the
/// pilot, bench-hashes-validation/b3sum-uring).
const BATCH: usize = 4;

/// Whether batches serve this run: several files, none of them stdin.
pub(crate) fn applies(args: &Args) -> bool {
    args.file_args.len() > 1 && args.file_args.iter().all(|p| p != Path::new("-"))
}

/// Hash every file of the run, printing in order: the files that failed.
pub(crate) fn hash_inputs(args: &Args) -> u64 {
    let threads = crate::threads().get().min(args.file_args.len());
    grow_descriptor_table(threads * std::env::var("B3_BATCH").ok().and_then(|v| v.parse().ok()).unwrap_or(BATCH) + 64);
    use crate::experiment as e;
    match args.experiment() {
        "nowait" => crate::hash_inputs_with(args, threads, |a: &Args, n: &AtomicUsize, d: &mut dyn FnMut(usize, anyhow::Result<e::Out>) -> bool| e::hash_some_nowait(a, n, d, false), e::print),
        "odirect" => crate::hash_inputs_with(args, threads, |a: &Args, n: &AtomicUsize, d: &mut dyn FnMut(usize, anyhow::Result<e::Out>) -> bool| e::hash_some_nowait(a, n, d, true), e::print),
        "stream" if args.len() == blake3::OUT_LEN as u64 && args.seek() == 0 && !args.keyed() => {
            crate::hash_inputs_with(args, threads, |a: &Args, n: &AtomicUsize, d: &mut dyn FnMut(usize, anyhow::Result<e::Out>) -> bool| {
                blake3::initialize_multithreaded(Some(crate::pool_threads()));
                e::hash_some_stream(a, n, d)
            }, e::print)
        }
        _ => crate::hash_inputs_with(args, threads, hash_some, crate::print_output),
    }
}

/// Room for `descriptors` open descriptors, made while this process has
/// one thread. The kernel's table starts at 64 and doubles as descriptors
/// need it; in a process whose threads share it, each growth waits for an
/// RCU grace period (expand_fdtable's synchronize_rcu): 10-13 ms a growth,
/// measured (openat of descriptor 64 and 128, i7-12700K, Linux 7.0). With
/// one thread, the kernel frees the old table at once. The table never
/// shrinks, so the room lasts the run.
fn grow_descriptor_table(descriptors: usize) {
    let target = descriptors.next_power_of_two() as i32 - 1;
    // Sound: plain descriptor calls on descriptors this function owns.
    unsafe {
        let fd = libc::open(c"/dev/null".as_ptr(), libc::O_RDONLY | libc::O_CLOEXEC);
        if fd >= 0 {
            if libc::dup2(fd, target) == target {
                libc::close(target);
            }
            libc::close(fd);
        }
    }
}

/// Hash the files whose turn `next` gives, a batch at a time, giving each
/// result to `done` (which returns false once nobody listens).
fn hash_some(args: &Args, next: &AtomicUsize, done: &mut dyn FnMut(usize, anyhow::Result<blake3::OutputReader>) -> bool) {
    let paths = &args.file_args;
    let mut buffer = Vec::new();
    loop {
        let mut batch = Vec::with_capacity(BATCH);
        while batch.len() < BATCH {
            let i = next.fetch_add(1, Ordering::Relaxed);
            if i >= paths.len() {
                break;
            }
            match std::fs::File::open(&paths[i]).and_then(|file| Ok((file.metadata()?, file))) {
                Ok((opened, file)) if opened.is_file() && opened.len() < SMALL => {
                    // Sound: advice on an open descriptor.
                    unsafe { libc::posix_fadvise(file.as_raw_fd(), 0, 0, libc::POSIX_FADV_WILLNEED) };
                    batch.push((i, opened, file));
                }
                // Not for the batch (or an error, which hash_path reports).
                _ => {
                    if !done(i, crate::hash_path(args, &paths[i])) {
                        return;
                    }
                }
            }
        }
        if batch.is_empty() {
            return;
        }
        for (i, opened, mut file) in batch {
            let size = opened.len() as usize;
            buffer.resize(size, 0);
            let read = file.read_exact(&mut buffer[..size]);
            let same = file.metadata().is_ok_and(|now| now.len() == opened.len() && now.modified().ok() == opened.modified().ok());
            let output = if read.is_ok() && same {
                let mut hasher = args.base_hasher.clone();
                hasher.update(&buffer[..size]);
                let mut output = hasher.finalize_xof();
                output.set_position(args.seek());
                Ok(output)
            } else {
                // Anything unexpected: as before, which reports it.
                crate::hash_path(args, &paths[i])
            };
            if !done(i, output) {
                return;
            }
        }
    }
}
