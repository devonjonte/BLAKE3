//! Many files at once (Linux): b3sum keeps up to DEPTH files read from
//! storage in flight across its file threads, where it kept one a thread.
//!
//! Each small file (a regular file reporting 1 byte to `SMALL`) is opened,
//! its size read as a hint for how to read it, then read with
//! preadv2(RWF_NOWAIT), which succeeds only from the page cache: a cached
//! file is read and hashed at once, at today's cost. A file that misses is
//! advised (posix_fadvise WILLNEED, which starts its reads from storage
//! and returns) and set aside; once the thread holds its batch of such
//! files, it reads and hashes each in turn, by which time the reads have
//! arrived or are on the way. A file is read to its reported size or its
//! end, whichever comes first (a /sys file reports 4096 bytes and holds a
//! few). Files reporting 0 bytes (empty, or /proc's, which hold more),
//! larger files, other kinds of file, and read errors go to `hash_path`, as
//! before.
//!
//! Measured (bench-hashes-validation/b3sum-uring): from storage, 1000 files
//! of 16 KiB with one thread took 0.27 of today's time, with 20 threads 0.86
//! (there the drive's random reads set the pace, about 110,000 a second);
//! cached files cost what they did. Tried and dropped: io_uring with 4 reads
//! in flight a thread (as fast as the hint with a ring and a dependency), a
//! stream a thread with Stream::submit_reader (slower cached: x1.18-1.35),
//! O_DIRECT for files that miss (x1.27-1.85 from storage: one read a thread
//! at a time, and no readahead), advising every file without RWF_NOWAIT
//! first (WILLNEED walks a cached file's pages: x1.07-1.17 for one thread).

use crate::Args;
use std::io::{Seek, SeekFrom};
use std::os::fd::AsRawFd;
use std::path::Path;
use std::sync::atomic::{AtomicUsize, Ordering};

/// Files below this go through the batch; larger ones are mapped or read as
/// before (`hash_path`; MAP_LEN).
const SMALL: u64 = crate::MAP_LEN as u64;

/// Files read from storage in flight across the file threads. From
/// storage, 1000 files of 16 KiB with one thread took x0.51 of today's
/// time at 4 in flight, x0.34 at 16, x0.27 at 64; with 20 threads, 2 to 16
/// a thread took alike. At most DEPTH files below SMALL wait in memory
/// (32 MiB at most), or MIN_BATCH a thread when there are more threads.
const DEPTH: usize = 64;

/// Files that missed the cache a thread holds at least.
const MIN_BATCH: usize = 4;

/// Whether batches serve this run: several files, none of them stdin.
pub(crate) fn applies(args: &Args) -> bool {
    args.file_args.len() > 1 && args.file_args.iter().all(|p| p != Path::new("-"))
}

/// Hash every file of the run, printing in order: the files that failed.
pub(crate) fn hash_inputs(args: &Args) -> u64 {
    let threads = crate::threads().get().min(args.file_args.len());
    let batch = DEPTH.div_ceil(threads).max(MIN_BATCH);
    grow_descriptor_table(threads * batch + 64);
    crate::hash_inputs_with(args, threads, |args: &Args, next: &AtomicUsize, done: &mut dyn FnMut(usize, anyhow::Result<blake3::OutputReader>) -> bool| hash_some(args, next, done, batch), crate::print_output)
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

/// A file that missed the cache: its index, the open file, its metadata as
/// opened, and the bytes read so far.
struct Missed {
    index: usize,
    file: std::fs::File,
    opened: std::fs::Metadata,
    bytes: Vec<u8>,
}

/// Hash the files whose turn `next` gives, holding up to `batch` that missed
/// the cache, giving each result to `done` (false once nobody listens).
fn hash_some(args: &Args, next: &AtomicUsize, done: &mut dyn FnMut(usize, anyhow::Result<blake3::OutputReader>) -> bool, batch: usize) {
    let paths = &args.file_args;
    let mut buffer = Vec::new();
    let mut more = true;
    while more {
        let mut missed = Vec::with_capacity(batch);
        while missed.len() < batch {
            let i = next.fetch_add(1, Ordering::Relaxed);
            if i >= paths.len() {
                more = false;
                break;
            }
            let small = std::fs::File::open(&paths[i]).and_then(|file| Ok((file.metadata()?, file)));
            let (opened, file) = match small {
                // A size is a hint for how to read, not what the file holds:
                // a file reporting 0 bytes (an empty one, or one of /proc's,
                // which report 0 and hold more) is read to its end below.
                Ok((opened, file)) if opened.is_file() && opened.len() > 0 && opened.len() < SMALL => (opened, file),
                // Not for the batch (or an error, which hash_path reports).
                _ => {
                    if !done(i, crate::hash_path(args, &paths[i])) {
                        return;
                    }
                    continue;
                }
            };
            buffer.resize(opened.len() as usize, 0);
            let (cached, end) = read_cached(&file, &mut buffer);
            if cached == buffer.len() || end {
                // All of it, or all there is (a /sys file reports more).
                if !done(i, Ok(hashed(args, &buffer[..cached]))) {
                    return;
                }
                continue;
            }
            // Sound: advice on an open descriptor.
            unsafe { libc::posix_fadvise(file.as_raw_fd(), cached as i64, 0, libc::POSIX_FADV_WILLNEED) };
            missed.push(Missed { index: i, file, opened, bytes: buffer[..cached].to_vec() });
        }
        for Missed { index, mut file, opened, mut bytes } in missed {
            let at = bytes.len();
            bytes.resize(opened.len() as usize, 0);
            // To the size or the end, whichever comes first.
            let read = file.seek(SeekFrom::Start(at as u64)).and_then(|_| crate::fill(&mut file, &mut bytes[at..]));
            let output = match read {
                Ok(n) => Ok(hashed(args, &bytes[..at + n])),
                // A read error: as before, which reports it.
                Err(_) => crate::hash_path(args, &paths[index]),
            };
            if !done(index, output) {
                return;
            }
        }
    }
}

/// The bytes the page cache holds of `file` from its start, read into
/// `buffer` without waiting for storage (preadv2 with RWF_NOWAIT): how
/// many, and whether the file ended there (a read of 0; a read that would
/// wait for storage fails instead).
fn read_cached(file: &std::fs::File, buffer: &mut [u8]) -> (usize, bool) {
    let mut done = 0;
    while done < buffer.len() {
        let iov = libc::iovec { iov_base: buffer[done..].as_mut_ptr().cast(), iov_len: buffer.len() - done };
        // Sound: one iovec over the buffer's unread part.
        let n = unsafe { libc::preadv2(file.as_raw_fd(), &iov, 1, done as i64, libc::RWF_NOWAIT) };
        if n == 0 {
            return (done, true);
        }
        if n < 0 {
            break;
        }
        done += n as usize;
    }
    (done, false)
}

/// `bytes`, a file's content, hashed.
fn hashed(args: &Args, bytes: &[u8]) -> blake3::OutputReader {
    let mut hasher = args.base_hasher.clone();
    hasher.update(bytes);
    let mut output = hasher.finalize_xof();
    output.set_position(args.seek());
    output
}
