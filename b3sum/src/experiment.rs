//! Experiments, chosen with the hidden `--experiment MODE` (Linux), for runs
//! of several files (readahead::applies), so that every mode is the same
//! build on the same link layouts:
//!
//! - `base`: today's b3sum (no batches).
//! - `readahead`: the default of this build (readahead.rs).
//! - `nowait`: each small file read first with preadv2(RWF_NOWAIT), which
//!   succeeds only from the page cache, so a cached file costs what it does
//!   today; a file that misses is advised (WILLNEED) and read after the
//!   thread has BATCH such files.
//! - `odirect`: as `nowait`, but a file that misses is read with O_DIRECT,
//!   the device writing into an aligned buffer, bypassing the page cache.
//! - `stream`: each file thread has a stream; a small file goes to it with
//!   Stream::submit_reader, which reads it straight into the stream's ring,
//!   and the pool hashes it (32-byte output, plain or derive-key mode).

use crate::Args;
use std::io::Read;
use std::os::fd::AsRawFd;
use std::path::Path;
use std::sync::atomic::{AtomicUsize, Ordering};

const SMALL: u64 = crate::MAP_LEN as u64;
const BATCH: usize = 4;

/// Pilot: B3_BATCH, files that missed the cache a thread holds at once.
fn batch() -> usize {
    std::env::var("B3_BATCH").ok().and_then(|v| v.parse().ok()).unwrap_or(BATCH)
}

/// A digest from a mode: the reader, as before, or a stream's 32 bytes.
pub(crate) enum Out {
    Reader(blake3::OutputReader),
    Hash(blake3::Hash),
}

pub(crate) fn print(out: Out, path: &Path, args: &Args) -> anyhow::Result<()> {
    match out {
        Out::Reader(output) => crate::print_output(output, path, args),
        Out::Hash(hash) => {
            if args.no_names() {
                println!("{}", hash.to_hex());
                return Ok(());
            }
            let crate::FilepathString { filepath_string, is_escaped } = crate::filepath_to_string(path);
            if is_escaped {
                print!("\\");
            }
            if args.tag() {
                println!("BLAKE3 ({}) = {}", filepath_string, hash.to_hex());
            } else {
                println!("{}  {}", hash.to_hex(), filepath_string);
            }
            Ok(())
        }
    }
}

fn before(args: &Args, path: &Path) -> anyhow::Result<Out> {
    crate::hash_path(args, path).map(Out::Reader)
}

fn hashed(args: &Args, bytes: &[u8]) -> anyhow::Result<Out> {
    let mut hasher = args.base_hasher.clone();
    hasher.update(bytes);
    let mut output = hasher.finalize_xof();
    output.set_position(args.seek());
    Ok(Out::Reader(output))
}

/// A small regular file, open, with its metadata as opened; else None (the
/// caller hashes it as before).
fn small(path: &Path) -> Option<(std::fs::File, std::fs::Metadata)> {
    let file = std::fs::File::open(path).ok()?;
    let meta = file.metadata().ok()?;
    (meta.is_file() && meta.len() < SMALL).then_some((file, meta))
}

fn unchanged(file: &std::fs::File, opened: &std::fs::Metadata) -> bool {
    file.metadata().is_ok_and(|now| now.len() == opened.len() && now.modified().ok() == opened.modified().ok())
}

/// preadv2 with RWF_NOWAIT from `at`: the bytes read from the page cache
/// alone (0 where a read would wait for storage).
fn read_cached(file: &std::fs::File, buffer: &mut [u8], at: usize) -> usize {
    let mut done = 0;
    while at + done < buffer.len() {
        let iov = libc::iovec { iov_base: buffer[at + done..].as_mut_ptr().cast(), iov_len: buffer.len() - at - done };
        // Sound: one iovec over this buffer's unread part.
        let n = unsafe { libc::preadv2(file.as_raw_fd(), &iov, 1, (at + done) as i64, libc::RWF_NOWAIT) };
        if n <= 0 {
            break;
        }
        done += n as usize;
    }
    done
}

/// A buffer of at least `len` bytes, aligned to 4 KiB, for O_DIRECT.
struct Aligned {
    ptr: *mut u8,
    layout: std::alloc::Layout,
}

impl Aligned {
    fn new(len: usize) -> Self {
        let layout = std::alloc::Layout::from_size_align(len.next_multiple_of(4096).max(4096), 4096).unwrap();
        // Sound: a nonzero size.
        let ptr = unsafe { std::alloc::alloc(layout) };
        assert!(!ptr.is_null(), "an aligned buffer");
        Aligned { ptr, layout }
    }
    fn slice(&mut self) -> &mut [u8] {
        // Sound: the allocation, this long, owned by self.
        unsafe { std::slice::from_raw_parts_mut(self.ptr, self.layout.size()) }
    }
}

impl Drop for Aligned {
    fn drop(&mut self) {
        // Sound: allocated with this layout.
        unsafe { std::alloc::dealloc(self.ptr, self.layout) }
    }
}

/// `file` read whole with O_DIRECT into `buffer` (len rounded up to 4 KiB):
/// the bytes read, or None.
fn read_direct(path: &Path, size: usize, buffer: &mut Aligned) -> Option<usize> {
    use std::os::unix::fs::OpenOptionsExt;
    let mut file = std::fs::OpenOptions::new().read(true).custom_flags(libc::O_DIRECT).open(path).ok()?;
    let room = &mut buffer.slice()[..size.next_multiple_of(4096).max(4096)];
    let mut done = 0;
    loop {
        match file.read(&mut room[done..]) {
            Ok(0) => break,
            Ok(n) => done += n,
            Err(e) if e.kind() == std::io::ErrorKind::Interrupted => {}
            Err(_) => return None,
        }
        if done >= size || done % 4096 != 0 {
            break;
        }
    }
    Some(done)
}

/// `nowait` and `odirect`: as described above.
pub(crate) fn hash_some_nowait(args: &Args, next: &AtomicUsize, done: &mut dyn FnMut(usize, anyhow::Result<Out>) -> bool, direct: bool) {
    let paths = &args.file_args;
    let mut buffer = Vec::new();
    let mut aligned = Aligned::new(SMALL as usize);
    let mut more = true;
    while more {
        // Files that missed the cache: (index, file, metadata, bytes so far).
        let mut missed: Vec<(usize, std::fs::File, std::fs::Metadata, Vec<u8>, usize)> = Vec::new();
        while missed.len() < batch() {
            let i = next.fetch_add(1, Ordering::Relaxed);
            if i >= paths.len() {
                more = false;
                break;
            }
            let Some((file, opened)) = small(&paths[i]) else {
                if !done(i, before(args, &paths[i])) {
                    return;
                }
                continue;
            };
            let size = opened.len() as usize;
            buffer.resize(size, 0);
            let got = read_cached(&file, &mut buffer, 0);
            if got == size {
                let out = if unchanged(&file, &opened) { hashed(args, &buffer) } else { before(args, &paths[i]) };
                if !done(i, out) {
                    return;
                }
                continue;
            }
            if !direct {
                // Sound: advice on an open descriptor.
                unsafe { libc::posix_fadvise(file.as_raw_fd(), got as i64, 0, libc::POSIX_FADV_WILLNEED) };
            }
            missed.push((i, file, opened, buffer[..got].to_vec(), got));
        }
        for (i, mut file, opened, mut bytes, got) in missed {
            let size = opened.len() as usize;
            let complete = if direct {
                match read_direct(&paths[i], size, &mut aligned) {
                    Some(n) if n == size => {
                        bytes.clear();
                        bytes.extend_from_slice(&aligned.slice()[..size]);
                        true
                    }
                    _ => false,
                }
            } else {
                bytes.resize(size, 0);
                use std::io::{Seek, SeekFrom};
                file.seek(SeekFrom::Start(got as u64)).is_ok() && file.read_exact(&mut bytes[got..]).is_ok()
            };
            let out = if complete && unchanged(&file, &opened) { hashed(args, &bytes) } else { before(args, &paths[i]) };
            if !done(i, out) {
                return;
            }
        }
    }
}

/// Places a thread's stream cycles through: more than a stream holds.
const PLACES: usize = 2048;

/// `stream`: as described above.
pub(crate) fn hash_some_stream(args: &Args, next: &AtomicUsize, done: &mut dyn FnMut(usize, anyhow::Result<Out>) -> bool) {
    let paths = &args.file_args;
    let mode = match args.derive_key_context() {
        Some(context) => blake3::Mode::DeriveKey(context),
        None => blake3::Mode::Hash,
    };
    let done = std::cell::RefCell::new(done);
    let listening = std::cell::Cell::new(true);
    // Submitted files in order: (index, unchanged as read).
    let pending = std::cell::RefCell::new(std::collections::VecDeque::<(usize, bool)>::new());
    let places: *mut blake3::Hash = Box::into_raw(vec![blake3::Hash::from_bytes([0; 32]); PLACES].into_boxed_slice()) as *mut blake3::Hash;
    let handed = |back: &mut [blake3::Hash]| {
        for hash in back.iter() {
            let (i, ok) = pending.borrow_mut().pop_front().expect("a file a place");
            let out = if ok { Ok(Out::Hash(*hash)) } else { before(args, &paths[i]) };
            if !(done.borrow_mut())(i, out) {
                listening.set(false);
            }
        }
    };
    blake3::stream(mode, handed, |s| {
        let mut submitted = 0usize;
        while listening.get() {
            let i = next.fetch_add(1, Ordering::Relaxed);
            if i >= paths.len() {
                break;
            }
            let Some((file, opened)) = small(&paths[i]) else {
                let out = before(args, &paths[i]);
                if !(done.borrow_mut())(i, out) {
                    listening.set(false);
                }
                continue;
            };
            // Sound: the place is free again by its turn (PLACES exceeds what
            // a stream holds in flight).
            let place = unsafe { &mut *places.add(submitted % PLACES) };
            submitted += 1;
            // The read happens here, into the stream's ring; the hash, on the
            // pool, later.
            match s.submit_reader(&file, Some(opened.len()), place) {
                Ok(n) => pending.borrow_mut().push_back((i, n == opened.len() && unchanged(&file, &opened))),
                Err(_) => {
                    // No place comes back for a failed read.
                    submitted -= 1;
                    let out = before(args, &paths[i]);
                    if !(done.borrow_mut())(i, out) {
                        listening.set(false);
                    }
                }
            }
        }
        s.finish();
    });
}
