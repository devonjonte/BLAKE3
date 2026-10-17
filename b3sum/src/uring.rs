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
    grow_descriptor_table(threads * IN_FLIGHT.max(pilot("B3_BATCH", 0)) + 64);
    match std::env::var("B3_MODE").as_deref() {
        Ok("stream") => return stream_readers(args),
        Ok("fadvise") => return crate::hash_inputs_with(args, threads, hash_some_fadvise, crate::print_output),
        _ => {}
    }
    crate::hash_inputs_with(args, threads, hash_some, crate::print_output)
}

/// Pilot switches (experiment only).
fn pilot(name: &str, default: usize) -> usize {
    std::env::var(name).ok().and_then(|v| v.parse().ok()).unwrap_or(default)
}

thread_local! {
    /// B3_DIRFD: the last directory opened, to open files relative to it.
    static DIR: std::cell::RefCell<Option<(std::path::PathBuf, std::os::fd::OwnedFd)>> = const { std::cell::RefCell::new(None) };
}

/// Open `path` (B3_DIRFD=1: relative to its directory, kept open between
/// files of one directory, so the kernel walks one name, not the path).
fn open(path: &Path) -> std::io::Result<std::fs::File> {
    if pilot("B3_DIRFD", 0) == 0 {
        return std::fs::File::open(path);
    }
    use std::os::fd::{FromRawFd, AsRawFd as _};
    use std::os::unix::ffi::OsStrExt;
    let (Some(parent), Some(name)) = (path.parent(), path.file_name()) else { return std::fs::File::open(path) };
    DIR.with_borrow_mut(|dir| {
        if dir.as_ref().is_none_or(|(p, _)| p != parent) {
            let d = std::fs::File::open(if parent.as_os_str().is_empty() { Path::new(".") } else { parent })?;
            *dir = Some((parent.to_path_buf(), d.into()));
        }
        let name = std::ffi::CString::new(name.as_bytes()).map_err(std::io::Error::other)?;
        // Sound: a plain openat on a directory this thread keeps open.
        let fd = unsafe { libc::openat(dir.as_ref().unwrap().1.as_raw_fd(), name.as_ptr(), libc::O_RDONLY | libc::O_CLOEXEC) };
        if fd < 0 {
            return Err(std::io::Error::last_os_error());
        }
        // Sound: a descriptor just opened, owned by the File.
        Ok(unsafe { std::fs::File::from_raw_fd(fd) })
    })
}

/// B3_MODE=fadvise: no io_uring. A thread takes B3_BATCH files (default 4),
/// opens each and asks the kernel to read it ahead (posix_fadvise
/// WILLNEED, which starts the reads and returns), then reads and hashes
/// each in turn.
fn hash_some_fadvise(args: &Args, next: &AtomicUsize, done: &mut dyn FnMut(usize, anyhow::Result<blake3::OutputReader>) -> bool) {
    use std::io::Read;
    let batch = pilot("B3_BATCH", 4);
    let paths = &args.file_args;
    let mut buffer = Vec::new();
    loop {
        let mut opened = Vec::new();
        for _ in 0..batch {
            let i = next.fetch_add(1, Ordering::Relaxed);
            if i >= paths.len() {
                break;
            }
            match open(&paths[i]).and_then(|file| Ok((file.metadata()?, file))) {
                Ok((meta, file)) if meta.is_file() && meta.len() < SMALL => {
                    // Sound: advice on an open descriptor.
                    unsafe { libc::posix_fadvise(file.as_raw_fd(), 0, 0, libc::POSIX_FADV_WILLNEED) };
                    opened.push((i, meta, file));
                }
                _ => {
                    if !done(i, crate::hash_path(args, &paths[i])) {
                        return;
                    }
                }
            }
        }
        if opened.is_empty() {
            return;
        }
        for (i, meta, mut file) in opened {
            let size = meta.len() as usize;
            buffer.resize(size, 0);
            let read = file.read_exact(&mut buffer[..size]);
            let same = file.metadata().is_ok_and(|now| now.len() == meta.len() && now.modified().ok() == meta.modified().ok());
            let output = if read.is_ok() && same {
                let mut hasher = args.base_hasher.clone();
                hasher.update(&buffer[..size]);
                let mut output = hasher.finalize_xof();
                output.set_position(args.seek());
                Ok(output)
            } else {
                crate::hash_path(args, &paths[i])
            };
            if !done(i, output) {
                return;
            }
        }
    }
}

/// B3_MODE=stream: B3_READERS threads (default 4) open and read each small
/// file into a buffer of its own and send it to this thread, which owns one
/// stream: the pool hashes every file; large files are hashed by their
/// reader as before. The default output only (32-byte digests, plain mode).
fn stream_readers(args: &Args) -> u64 {
    use std::io::Read;
    blake3::initialize_multithreaded(Some(crate::threads()));
    let paths = &args.file_args;
    let readers = pilot("B3_READERS", 4).min(paths.len());
    let next = AtomicUsize::new(0);
    enum Item { Bytes(Vec<u8>), Output(anyhow::Result<blake3::OutputReader>) }
    let (tx, rx) = std::sync::mpsc::sync_channel::<(usize, Item)>(1024);
    let mut digests = vec![blake3::Hash::from_bytes([0; 32]); paths.len()];
    let base = digests.as_ptr() as usize;
    let mut outputs: Vec<Option<anyhow::Result<blake3::OutputReader>>> = (0..paths.len()).map(|_| None).collect();
    let bytes: std::cell::RefCell<Vec<Vec<u8>>> = std::cell::RefCell::new((0..paths.len()).map(|_| Vec::new()).collect());
    let hashed: std::cell::RefCell<Vec<bool>> = std::cell::RefCell::new(vec![false; paths.len()]);
    let done = |back: &mut [blake3::Hash]| {
        for place in back.iter() {
            let i = (place as *const blake3::Hash as usize - base) / std::mem::size_of::<blake3::Hash>();
            bytes.borrow_mut()[i] = Vec::new();
            hashed.borrow_mut()[i] = true;
        }
    };
    let mut places: Vec<Option<&mut blake3::Hash>> = digests.iter_mut().map(Some).collect();
    std::thread::scope(|scope| {
        for _ in 0..readers {
            let (tx, next) = (tx.clone(), &next);
            scope.spawn(move || loop {
                let i = next.fetch_add(1, Ordering::Relaxed);
                if i >= paths.len() {
                    return;
                }
                let item = match open(&paths[i]).and_then(|file| Ok((file.metadata()?, file))) {
                    Ok((meta, mut file)) if meta.is_file() && meta.len() < SMALL => {
                        let mut v = vec![0u8; meta.len() as usize];
                        let read = file.read_exact(&mut v);
                        let same = file.metadata().is_ok_and(|now| now.len() == meta.len() && now.modified().ok() == meta.modified().ok());
                        if read.is_ok() && same { Item::Bytes(v) } else { Item::Output(crate::hash_path(args, &paths[i])) }
                    }
                    _ => Item::Output(crate::hash_path(args, &paths[i])),
                };
                if tx.send((i, item)).is_err() {
                    return;
                }
            });
        }
        drop(tx);
        blake3::stream(blake3::Mode::Hash, done, |s| {
            for (i, item) in rx {
                match item {
                    Item::Output(o) => outputs[i] = Some(o),
                    Item::Bytes(v) => {
                        let (ptr, len) = (v.as_ptr(), v.len());
                        bytes.borrow_mut()[i] = v;
                        // Sound: the bytes stay in `bytes` until the stream
                        // hands the place back (done empties it then).
                        s.submit(unsafe { core::slice::from_raw_parts(ptr, len) }, places[i].take().unwrap());
                    }
                }
            }
            s.finish();
        });
    });
    drop(places);
    let mut failed = 0u64;
    for (i, path) in paths.iter().enumerate() {
        let printed = match outputs[i].take() {
            Some(o) => o.and_then(|o| crate::print_output(o, path, args)),
            None => {
                assert!(hashed.borrow()[i], "every file hashed");
                println!("{}  {}", digests[i].to_hex(), path.to_string_lossy());
                Ok(())
            }
        };
        if let Err(e) = printed {
            failed += 1;
            eprintln!("{}: {}: {}", crate::NAME, path.to_string_lossy(), e);
        }
    }
    failed
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
    // Made at the thread's first small file: a run of large files makes
    // none (making one maps memory, which waits on the page faults other
    // threads take in their mappings).
    let mut ring: Option<IoUring> = None;
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
            let small = open(&paths[i]).and_then(|file| Ok((file.metadata()?, file)));
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
            // B3_ASYNC=1: the read on io_uring's kernel workers.
            let read = if pilot("B3_ASYNC", 0) == 1 { read.flags(io_uring::squeue::Flags::ASYNC) } else { read };
            flights[slot] = Some(Flight { index: i, file, opened });
            // Sound: the buffer and the file stay, unmoved, until this read
            // completes (the slot is not reused before).
            let ring = ring.get_or_insert_with(|| if pilot("B3_SQPOLL", 0) > 0 { IoUring::builder().setup_sqpoll(pilot("B3_SQPOLL", 0) as u32).build(IN_FLIGHT as u32 * 2) } else { IoUring::new(IN_FLIGHT as u32 * 2) }.expect("io_uring"));
            unsafe { ring.submission().push(&read).expect("room in the ring") };
            // Submitted at once: a read of cached data completes here, and its
            // file is hashed now, while its bytes are in this core's cache;
            // only reads that wait for storage stay in flight.
            ring.submit().expect("io_uring_enter");
            if !finish(args, ring, &mut flights, &mut free, &buffers, done) {
                return;
            }
        }
        if free.len() == IN_FLIGHT {
            return;
        }
        let ring = ring.as_mut().expect("a ring holds the reads in flight");
        ring.submit_and_wait(1).expect("io_uring_enter");
        if !finish(args, ring, &mut flights, &mut free, &buffers, done) {
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
