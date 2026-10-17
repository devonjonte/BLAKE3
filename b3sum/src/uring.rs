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

/// Reads in flight a thread (pilot: B3_IN_FLIGHT).
fn in_flight() -> usize {
    std::env::var("B3_IN_FLIGHT").ok().and_then(|v| v.parse().ok()).unwrap_or(4)
}

/// Whether the ring serves this run: several files, the default output.
pub(crate) fn applies(args: &Args) -> bool {
    args.file_args.len() > 1
        && !args.check()
        && !args.raw()
        && args.len() == blake3::OUT_LEN as u64
        && args.seek() == 0
        && crate::threads().get() > 1
        && args.file_args.iter().all(|p| p != Path::new("-"))
}

/// Hash every file of the run, printing in order: the files that failed.
pub(crate) fn hash_inputs(args: &Args) -> u64 {
    let print = |hash: blake3::Hash, path: &Path, args: &Args| crate::print_hash(&hash, path, args);
    // Pilot: B3_STREAM_IO=K, K threads reading and a stream each, the pool hashing.
    if let Some(io) = std::env::var("B3_STREAM_IO").ok().and_then(|v| v.parse::<usize>().ok()) {
        let threads = io.min(args.file_args.len());
        grow_descriptor_table(threads * in_flight() + 64);
        blake3::initialize_multithreaded(Some(crate::threads()));
        return crate::hash_inputs_with(args, threads, hash_some_streamed, print);
    }
    let threads = crate::threads().get().min(args.file_args.len());
    grow_descriptor_table(threads * in_flight() + 64);
    crate::hash_inputs_with(args, threads, hash_some, print)
}

/// The mode the run hashes in.
fn mode(args: &Args) -> blake3::Mode<'_> {
    match (&args.key, args.derive_key()) {
        (Some(key), _) => blake3::Mode::Keyed(key),
        (None, Some(context)) => blake3::Mode::DeriveKey(context),
        (None, None) => blake3::Mode::Hash,
    }
}

/// Digest places a streaming thread cycles through: more than a stream
/// holds in flight (1024 messages), so a place comes back before its turn.
const PLACES: usize = 2048;

/// As hash_some, each completed file a message to this thread's stream,
/// which the pool hashes while this thread goes on reading.
fn hash_some_streamed(args: &Args, next: &AtomicUsize, done: &mut dyn FnMut(usize, anyhow::Result<blake3::Hash>) -> bool) {
    let paths = &args.file_args;
    let depth = in_flight();
    let done = std::cell::RefCell::new(done);
    let listening = std::cell::Cell::new(true);
    // Submitted files in order (index, buffer), and buffers to reuse.
    let pending = std::cell::RefCell::new(std::collections::VecDeque::<(usize, Vec<u8>)>::new());
    let spare = std::cell::RefCell::new(Vec::<Vec<u8>>::new());
    let places: *mut blake3::Hash = Box::into_raw(vec![blake3::Hash::from_bytes([0; 32]); PLACES].into_boxed_slice()) as *mut blake3::Hash;
    let handed = |back: &mut [blake3::Hash]| {
        for hash in back.iter() {
            let (i, buffer) = pending.borrow_mut().pop_front().expect("a file for each place");
            if !(done.borrow_mut())(i, Ok(*hash)) {
                listening.set(false);
            }
            spare.borrow_mut().push(buffer);
        }
    };
    blake3::stream(mode(args), handed, |s| {
        let mut ring = IoUring::new(depth as u32 * 2).expect("io_uring");
        let mut flights: Vec<Option<(Flight, Vec<u8>)>> = (0..depth).map(|_| None).collect();
        let mut free: Vec<usize> = (0..depth).rev().collect();
        let mut more = true;
        let mut submitted = 0usize;
        loop {
            while more && !free.is_empty() && listening.get() {
                let i = next.fetch_add(1, Ordering::Relaxed);
                if i >= paths.len() {
                    more = false;
                    break;
                }
                let small = std::fs::File::open(&paths[i]).and_then(|file| Ok((file.metadata()?, file)));
                let (opened, file) = match small {
                    Ok((opened, file)) if opened.is_file() && opened.len() < SMALL => (opened, file),
                    _ => {
                        let digest = before(args, &paths[i]);
                        if !(done.borrow_mut())(i, digest) {
                            listening.set(false);
                        }
                        continue;
                    }
                };
                let slot = free.pop().unwrap();
                let size = opened.len() as usize;
                let mut buffer = spare.borrow_mut().pop().unwrap_or_default();
                if buffer.len() < size {
                    buffer.resize(size, 0);
                }
                let read = opcode::Read::new(types::Fd(file.as_raw_fd()), buffer.as_mut_ptr(), size as u32).offset(0).build().user_data(slot as u64);
                flights[slot] = Some((Flight { index: i, file, opened }, buffer));
                // Sound: the buffer's bytes (on the heap, unmoved when the Vec
                // moves) and the file stay until this read completes.
                unsafe { ring.submission().push(&read).expect("room in the ring") };
                ring.submit().expect("io_uring_enter");
                submitted += take(args, s, &mut ring, &mut flights, &mut free, &pending, &done, &listening, places, submitted);
            }
            if free.len() == depth {
                break;
            }
            ring.submit_and_wait(1).expect("io_uring_enter");
            submitted += take(args, s, &mut ring, &mut flights, &mut free, &pending, &done, &listening, places, submitted);
        }
        s.finish();
    });
}

/// The completed reads of hash_some_streamed: each file checked and
/// submitted to the stream, or hashed as before; how many were submitted.
#[allow(clippy::too_many_arguments)]
fn take<'env, D: FnMut(&'env mut [blake3::Hash])>(
    args: &Args,
    s: &mut blake3::Stream<'env, D>,
    ring: &mut IoUring,
    flights: &mut [Option<(Flight, Vec<u8>)>],
    free: &mut Vec<usize>,
    pending: &std::cell::RefCell<std::collections::VecDeque<(usize, Vec<u8>)>>,
    done: &std::cell::RefCell<&mut dyn FnMut(usize, anyhow::Result<blake3::Hash>) -> bool>,
    listening: &std::cell::Cell<bool>,
    places: *mut blake3::Hash,
    submitted: usize,
) -> usize {
    let completed: Vec<(u64, i32)> = ring.completion().map(|c| (c.user_data(), c.result())).collect();
    let mut n = 0;
    for (slot, read) in completed {
        let slot = slot as usize;
        let (f, buffer) = flights[slot].take().expect("a flight for each read");
        free.push(slot);
        let size = f.opened.len();
        let same = f.file.metadata().is_ok_and(|now| now.len() == size && now.modified().ok() == f.opened.modified().ok());
        if read as i64 != size as i64 || !same {
            let digest = before(args, &args.file_args[f.index]);
            if !(done.borrow_mut())(f.index, digest) {
                listening.set(false);
            }
            continue;
        }
        let (bytes, len) = (buffer.as_ptr(), size as usize);
        pending.borrow_mut().push_back((f.index, buffer));
        // Sound: the bytes stay allocated, unmoved, in `pending` until the
        // stream hands their place back; the place is free again by then
        // (PLACES exceeds what a stream holds in flight).
        let (message, place) = unsafe { (core::slice::from_raw_parts(bytes, len), &mut *places.add((submitted + n) % PLACES)) };
        s.submit(message, place);
        n += 1;
    }
    n
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
fn hash_some(args: &Args, next: &AtomicUsize, done: &mut dyn FnMut(usize, anyhow::Result<blake3::Hash>) -> bool) {
    let paths = &args.file_args;
    let mut ring = IoUring::new(in_flight() as u32 * 2).expect("io_uring");
    let mut buffers: Vec<Vec<u8>> = (0..in_flight()).map(|_| Vec::new()).collect();
    let mut flights: Vec<Option<Flight>> = (0..in_flight()).map(|_| None).collect();
    let mut free: Vec<usize> = (0..in_flight()).rev().collect();
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
                    if !done(i, before(args, &paths[i])) {
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
        if free.len() == in_flight() {
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
fn finish(args: &Args, ring: &mut IoUring, flights: &mut [Option<Flight>], free: &mut Vec<usize>, buffers: &[Vec<u8>], done: &mut dyn FnMut(usize, anyhow::Result<blake3::Hash>) -> bool) -> bool {
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
                Ok(hasher.finalize())
            } else {
                // Anything unexpected: as before, which reports it.
                before(args, &args.file_args[f.index])
            };
            if !done(f.index, digest) {
                return false;
            }
        }
    }
    true
}

/// A file hashed as before (hash_path): its 32-byte digest.
fn before(args: &Args, path: &Path) -> anyhow::Result<blake3::Hash> {
    let mut output = crate::hash_path(args, path)?;
    let mut digest = [0; blake3::OUT_LEN];
    output.fill(&mut digest);
    Ok(blake3::Hash::from_bytes(digest))
}
