//! Helper functions for efficient IO.

use std::io;

pub(crate) fn copy_wide(mut reader: impl io::Read, hasher: &mut crate::Hasher) -> io::Result<()> {
    // A reader that fills 64 KiB has more: the rest goes through a 1 MiB
    // buffer, filled before each update. On SME2, 1 MiB pieces hash at the
    // one-shot rate, where 64 KiB pieces each meet the SME unit's slow
    // state after the reads between them (M4 Max, files of 8-64 MiB 23-33%
    // less time; NOTES-servil.md, "update_reader through a 1 MiB buffer").
    // The first 64 KiB lead the 1 MiB buffer, so its updates stay whole
    // 1 MiB subtrees (a Hasher's subtrees align to their own size). Every
    // byte read is hashed before an error returns: a caller that retries
    // after one (WouldBlock, say) loses nothing.
    let mut small = [0; 65536];
    let (n, read) = fill(&mut reader, &mut small);
    if n < small.len() || read.is_err() {
        hasher.update(&small[..n]);
        return read;
    }
    let mut buffer = std::vec![0; 1 << 20];
    buffer[..n].copy_from_slice(&small);
    let mut start = n;
    loop {
        let (filled, read) = fill(&mut reader, &mut buffer[start..]);
        let n = start + filled;
        hasher.update(&buffer[..n]);
        read?;
        if n < buffer.len() {
            return Ok(());
        }
        start = 0;
    }
}

/// Read into `buffer` until it is full, the reader ends, or it fails: the
/// bytes read, and the error if it failed.
fn fill(reader: &mut impl io::Read, buffer: &mut [u8]) -> (usize, io::Result<()>) {
    let mut filled = 0;
    while filled < buffer.len() {
        match reader.read(&mut buffer[filled..]) {
            Ok(0) => break,
            Ok(n) => filled += n,
            // see test_update_reader_interrupted
            Err(e) if e.kind() == io::ErrorKind::Interrupted => continue,
            Err(e) => return (filled, Err(e)),
        }
    }
    (filled, Ok(()))
}

// Try to `mmap` a file, unless it's short enough that ordinary reads are faster, currently 16 KiB.
// Return `Ok(None)` if mapping fails or if we don't attempt it. Only return `Err` for unexpected
// failures that could leave the `File` in a bad state.
//
// We seek to (near) end-of-file to get the length, and the prior cursor position is ignored. If
// mapping fails, we [`rewind`] the file cursor to start-of-file before returning `None`. We don't
// `rewind` if the mapping succeeds, however, to avoid unnecessary syscalls. In the unlikely event
// that the caller wants to do ordinary reads in addition to mapped reads, they need to `rewind`
// explicitly in that case. (This function isn't public, but that comes up in test cases.)
//
// [`rewind`]: https://doc.rust-lang.org/std/io/trait.Seek.html#method.rewind
//
// SAFETY: Mmaps are fundamentally unsafe, because you can call invariant-checking functions like
// str::from_utf8 on them and then have them change out from under you. Letting a safe caller get
// their hands on an mmap, or even a &[u8] that's backed by an mmap, is unsound. However, because
// this function is crate-private, we can guarantee that all can ever happen in the event of a race
// condition is that we either hash nonsense bytes or crash with SIGBUS or similar, neither of
// which should risk memory corruption in a safe caller.
//
// PARANOIA: But a data race...is a data race...is a data race...right? Even if we know that no
// platform in the "real world" is ever going to do anything other than compute the "wrong answer"
// if we race on this mmap while we hash it, aren't we still supposed to feel bad about doing this?
// Well, maybe. This is IO, and IO gets special carve-outs in the memory model. Consider a
// memory-mapped register that returns random 32-bit words. (This is actually realistic if you have
// a hardware RNG.) It's probably sound to construct a *const i32 pointing to that register and do
// some raw pointer reads from it. Those reads should be volatile if you don't want the compiler to
// coalesce them, but either way the compiler isn't allowed to just _go nuts_ and insert
// should-never-happen branches to wipe your hard drive if two adjacent reads happen to give
// different values. As far as I'm aware, there's no such thing as a read that's allowed if it's
// volatile but prohibited if it's not (unlike atomics). As mentioned above, it's not ok to
// construct a safe &i32 to the register if you're going to leak that reference to unknown callers.
// But if you "know what you're doing," I don't think *const i32 and &i32 are fundamentally
// different here. Feedback needed.
