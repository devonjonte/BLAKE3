//! Many files at once (Linux): each of b3sum's file threads keeps several
//! reads in flight through its own io_uring, so a tree of small files read
//! from storage keeps the device's queue deep (threads x IN_FLIGHT reads,
//! where one read a thread kept threads reads).
//!
//! Each file is opened, and its metadata read, on its thread (plain system
//! calls, about a microsecond each when cached; io_uring would hand
//! `statx` to a kernel worker thread, several microseconds a hand-over); a
//! regular file below `SMALL` then has its whole read queued in the
//! thread's ring, into a buffer the thread reuses, and the change check
//! (size and modification time as when opened) follows the read. Larger
//! files, other kinds of file, and any file whose read or check is not
//! exactly as expected go to `hash_path`, as before: the fast path never
//! decides a digest alone.

use crate::Args;
use io_uring::{IoUring, opcode, types};
use std::os::fd::AsRawFd;
use std::path::Path;
use std::sync::atomic::{AtomicUsize, Ordering};

/// Files below this go through the ring; larger ones are mapped or read as
/// before (`hash_path`; MAP_LEN).
const SMALL: u64 = crate::MAP_LEN as u64;

/// Reads in flight a thread: 80 with 20 threads. From storage, 1000 files
/// of 16 KiB took as long at 2, 4, 8 and 16 a thread, and longer at 1
/// (bench-hashes-validation/b3sum-uring).
const IN_FLIGHT: usize = 4;

/// Whether the ring serves this run: several files, none of them stdin,
/// on several threads (the kernel runs some of io_uring's work on worker
/// threads of this process, which --num-threads 1 rules out).
pub(crate) fn applies(args: &Args) -> bool {
    args.file_args.len() > 1 && crate::threads().get() > 1 && args.file_args.iter().all(|p| p != Path::new("-"))
}

/// Hash every file of the run, printing in order: the files that failed.
pub(crate) fn hash_inputs(args: &Args) -> u64 {
    let threads = crate::threads().get().min(args.file_args.len());
    grow_descriptor_table(threads * IN_FLIGHT + 64);
    crate::hash_inputs_with(args, threads, hash_some, crate::print_output)
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

/// One read in flight.
struct Flight {
    index: usize,
    file: std::fs::File,
    opened: std::fs::Metadata,
}

/// Hash the files whose turn `next` gives, IN_FLIGHT reads at a time,
/// giving each digest to `done` as its read completes.
fn hash_some(args: &Args, next: &AtomicUsize, done: &mut dyn FnMut(usize, anyhow::Result<blake3::OutputReader>) -> bool) {
    let paths = &args.file_args;
    let mut ring = IoUring::new(IN_FLIGHT as u32 * 2).expect("io_uring");
    let mut buffers: Vec<Vec<u8>> = (0..IN_FLIGHT).map(|_| Vec::new()).collect();
    let mut flights: Vec<Option<Flight>> = (0..IN_FLIGHT).map(|_| None).collect();
    let mut free: Vec<usize> = (0..IN_FLIGHT).rev().collect();
    let mut more = true;
    loop {
        while more && !free.is_empty() {
            let i = next.fetch_add(1, Ordering::Relaxed);
            if i >= paths.len() {
                more = false;
                break;
            }
            let small = std::fs::File::open(&paths[i]).and_then(|file| Ok((file.metadata()?, file)));
            let (opened, file) = match small {
                Ok((opened, file)) if opened.is_file() && opened.len() < SMALL => (opened, file),
                // Not for the ring (or an error, which hash_path reports).
                _ => {
                    if !done(i, crate::hash_path(args, &paths[i])) {
                        return;
                    }
                    continue;
                }
            };
            let slot = free.pop().unwrap();
            let size = opened.len() as usize;
            let buffer = &mut buffers[slot];
            if buffer.len() < size {
                buffer.resize(size, 0);
            }
            let read = opcode::Read::new(types::Fd(file.as_raw_fd()), buffer.as_mut_ptr(), size as u32).offset(0).build().user_data(slot as u64);
            flights[slot] = Some(Flight { index: i, file, opened });
            // Sound: the buffer and the file stay, unmoved, until this read
            // completes (the slot is not reused before).
            unsafe { ring.submission().push(&read).expect("room in the ring") };
            // Submitted at once: a read of cached data completes here, and its
            // file is hashed now, while its bytes are in this core's cache;
            // only reads that wait for storage stay in flight.
            ring.submit().expect("io_uring_enter");
            if !finish(args, &mut ring, &mut flights, &mut free, &buffers, done) {
                return;
            }
        }
        if free.len() == IN_FLIGHT {
            return;
        }
        ring.submit_and_wait(1).expect("io_uring_enter");
        if !finish(args, &mut ring, &mut flights, &mut free, &buffers, done) {
            return;
        }
    }
}

/// Hash the files whose reads have completed, giving each digest to `done`:
/// false once nobody listens.
fn finish(args: &Args, ring: &mut IoUring, flights: &mut [Option<Flight>], free: &mut Vec<usize>, buffers: &[Vec<u8>], done: &mut dyn FnMut(usize, anyhow::Result<blake3::OutputReader>) -> bool) -> bool {
    {
        let completed: Vec<(u64, i32)> = ring.completion().map(|c| (c.user_data(), c.result())).collect();
        for (slot, read) in completed {
            let slot = slot as usize;
            let f = flights[slot].take().expect("a flight for each read");
            free.push(slot);
            let size = f.opened.len();
            let same = f.file.metadata().is_ok_and(|now| now.len() == size && now.modified().ok() == f.opened.modified().ok());
            let digest = if read as i64 == size as i64 && same {
                let mut hasher = args.base_hasher.clone();
                hasher.update(&buffers[slot][..size as usize]);
                let mut output = hasher.finalize_xof();
                output.set_position(args.seek());
                Ok(output)
            } else {
                // Anything unexpected: as before, which reports it.
                crate::hash_path(args, &args.file_args[f.index])
            };
            if !done(f.index, digest) {
                return false;
            }
        }
    }
    true
}
