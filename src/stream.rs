//! A stream of messages hashed in place by this crate's threads, in the
//! program's own memory, digests handed back in order ([`stream`]).
//!
//! How it runs:
//! - Each message of up to [`PIECE`] bytes is one entry in a ring of
//!   entries; entries gather into tasks of up to [`MEMBERS`] messages (or
//!   TASK_LEN / 4 bytes), hashed as the queue's members are: messages of
//!   one length side by side, the rest one at a time.
//! - A longer message is split into pieces of PIECE bytes, each a whole
//!   subtree at its offset and a task of its own; the program's thread
//!   merges the pieces' chaining values in order as it hands back the
//!   digest.
//! - Tasks go to the pool's task list a task at a time (one lock per task,
//!   no locked instruction per message). The open task is handed over when
//!   it fills, or when the program collects or finishes.
//! - Digests come back in order on the program's thread, from `submit`
//!   (when the ring is full), `collect` and `finish`. A program waiting
//!   hashes tasks no thread has taken.
//!
//! The messages are borrowed for the scope of [`stream`], which waits for
//! every task before it returns, also when its body panics: no thread
//! reads a message after the scope ends.

use crate::lanes::{MEMBERS, Member, OwnLine, TASK_LEN, TASKS, Task};
use crate::platform::Platform;
use crate::{CHUNK_LEN, CVBytes, CVWords, Hash, Mode, OUT_LEN};
use core::cell::UnsafeCell;
use core::marker::PhantomData;
use core::sync::atomic::{AtomicUsize, Ordering};

/// The longest message hashed as one entry; a longer one goes in pieces
/// this long (a task's subtree).
pub(crate) const PIECE: usize = TASK_LEN;

/// The most entries (messages and pieces) in flight in one stream (1024:
/// 4 KiB to 16 KiB messages 8-9% faster than at 8192, i7-12700K; 256 lost
/// 26-130% at 64 and 256 B).
const ENTRIES: usize = 1024;

/// One message, or one piece of a long one, from its submission to its
/// delivery: what the program's thread keeps of it. Its task's threads
/// write its `out`, then count down the `left` of the task's first entry
/// (Release, once a task); the program reads `out` once that is zero
/// (Acquire). Kept apart, so that the program's writes here share no
/// line with the threads'.
#[derive(Clone, Copy)]
struct Entry {
    len: usize,
    /// For a piece of a long message: its first chunk's index, and whether
    /// it is the message's last piece. `None` for a whole message.
    piece: Option<(u64, bool)>,
    /// The index of its task's first entry, whose `left` counts the task.
    first: usize,
}

/// What a task's threads write for an entry: a message's digest, two to a
/// line (the program reads each line once for two messages: 64 B messages
/// 0.249 -> 0.217 ns/B, 256 B x0.935, i7-12700K); or, in `pieces_out`, a piece's chaining value
/// (a piece at chunk 0, of two chunks or more, gives its two children
/// instead) on a line of its own.
struct Out<const N: usize>(UnsafeCell<[u8; N]>);

/// Hash a stream of messages on this crate's threads, in place: `body`
/// submits messages that live at least as long as the call
/// ([`Stream::submit`]), and receives their digests in order from
/// `submit`, [`collect`](Stream::collect) and [`finish`](Stream::finish).
/// `body` calls `finish` last (a scope that ends with digests not handed
/// back panics). A message of any length; this crate's threads read it
/// where it is, and `stream` returns only after they are done, also when
/// `body` panics.
///
/// The program calls [`crate::initialize_multithreaded`] first. A stream
/// holds up to 1024 messages (a message over 64 KiB counts once per 64 KiB)
/// in flight; when it is full, `submit` waits for room, handing back
/// finished digests and hashing a waiting task itself. A message stays
/// unhashed in a task still open until the task fills or the program
/// calls `collect` or `finish`, so a program that needs a digest soon
/// calls one of them.
///
/// ```
/// # blake3_servil::initialize_multithreaded();
/// use blake3_servil::Mode;
/// let messages: Vec<Vec<u8>> = (0..1000u32).map(|i| i.to_le_bytes().repeat(16)).collect();
/// let mut digests = Vec::new();
/// blake3_servil::stream(Mode::Hash, |s| {
///     for message in &messages {
///         s.submit(message, |hash| digests.push(hash));
///     }
///     s.finish(|hash| digests.push(hash));
/// });
/// assert_eq!(digests[7], blake3_servil::hash(&messages[7]));
/// ```
pub fn stream<'env, T>(mode: Mode, body: impl for<'s> FnOnce(&'s mut Stream<'env>) -> T) -> T {
    crate::lanes::require();
    let (key, flags) = mode.key_and_flags();
    let s = SPARE.with(|spare| spare.take()).unwrap_or_else(Storage::new);
    let mut stream = Stream { key, flags, s, open_first: 0, next: 0, delivered: 0, open: None, stack: Vec::with_capacity(64), pieces: 0, env: PhantomData };
    let result = body(&mut stream);
    assert_eq!(stream.delivered, stream.next, "a stream's body calls finish last");
    result
}

/// A stream's entries, and room for their tasks in the pool's list: kept
/// for the thread's next stream (a stream of one message up to 4 KiB
/// after a 1 ms pause: 55 us with 248 KiB allocated and faulted in each
/// time, 4-5 us with the spare; one stream kept open, 2.6-4 us. i7-12700K).
struct Storage {
    entries: Box<[Entry]>,
    outs: Box<[Out<OUT_LEN>]>,
    pieces_out: Box<[OwnLine<Out<64>>]>,
    /// For a task's first entry, the count of the task's entries still
    /// unhashed: on lines of their own (128 bytes, as the adjacent-line
    /// prefetcher pairs lines), so that the program polling one shares no
    /// line with the threads writing digests. Zero between streams.
    lefts: Box<[OwnLine<AtomicUsize>]>,
}

std::thread_local! {
    /// The storage of this thread's last stream.
    static SPARE: core::cell::Cell<Option<Storage>> = const { core::cell::Cell::new(None) };
}

impl Storage {
    fn new() -> Storage {
        // Every entry may be a task in flight at once.
        TASKS.make_room(ENTRIES);
        Storage {
            entries: std::vec![Entry { len: 0, piece: None, first: 0 }; ENTRIES].into_boxed_slice(),
            outs: (0..ENTRIES).map(|_| Out(UnsafeCell::new([0; OUT_LEN]))).collect(),
            pieces_out: (0..ENTRIES).map(|_| OwnLine(Out(UnsafeCell::new([0; 64])))).collect(),
            lefts: (0..ENTRIES).map(|_| OwnLine(AtomicUsize::new(0))).collect(),
        }
    }
}

impl Drop for Storage {
    /// Give back its room (none for the empty storage a stream leaves).
    fn drop(&mut self) {
        TASKS.give_room(self.lefts.len());
    }
}

/// The messages of one [`stream`] call, borrowed for its scope.
pub struct Stream<'env> {
    key: CVWords,
    flags: u8,
    /// Its own until the stream ends (then the thread's spare).
    s: Storage,
    /// The open task's first entry.
    open_first: usize,
    /// Entries submitted, and entries handed back (each counts on).
    next: usize,
    delivered: usize,
    /// Short messages gathered, not yet handed to the pool.
    open: Option<Task>,
    /// A long message being handed back: its pieces' chaining values so
    /// far (merged as the Hasher's stack merges), and how many.
    stack: Vec<CVBytes>,
    pieces: u64,
    /// Invariant in 'env, as std::thread::Scope is: the messages' lifetime.
    env: PhantomData<&'env mut &'env ()>,
}

// Sound: the entries are reached by the program's thread through `&mut
// self`, and by the pool's threads only for entries in tasks in flight,
// across the Release/Acquire pair on each entry's `left`; the messages are
// shared borrows, alive for 'env.
unsafe impl Send for Stream<'_> {}

impl<'env> Stream<'env> {
    /// Hash `message` where it is; `digest` receives any digests this call
    /// hands back.
    pub fn submit(&mut self, message: &'env [u8], mut digest: impl FnMut(Hash)) {
        if message.len() <= PIECE {
            let entry = self.add_entry(message.len(), None, &mut digest);
            let (key, flags) = (self.key, self.flags);
            let open = self.open.get_or_insert_with(|| Task::members(&key, flags, None));
            // The task's first member's `left` counts all of its members
            // (set as the task is handed over).
            if open.members == 0 {
                self.open_first = entry;
            }
            let first = self.open_first;
            self.s.entries[entry].first = first;
            let member = Member { input: message.as_ptr(), len: message.len(), out: self.s.outs[entry].0.get() as *mut u8, left: &*self.s.lefts[first] };
            open.member[open.members] = member;
            open.members += 1;
            open.len += member.len;
            if open.members == MEMBERS || open.len >= TASK_LEN / 4 {
                self.publish();
            }
            return;
        }
        let pieces = message.len().div_ceil(PIECE);
        for (i, piece) in message.chunks(PIECE).enumerate() {
            let counter = (i * PIECE / CHUNK_LEN) as u64;
            let entry = self.add_entry(piece.len(), Some((counter, i + 1 == pieces)), &mut digest);
            // A piece is a task of its own: a whole subtree at `counter`.
            self.s.lefts[entry].store(1, Ordering::Relaxed);
            let task = Task {
                key: self.key,
                flags: self.flags,
                out: self.s.pieces_out[entry].0.0.get() as *mut u8,
                left: &*self.s.lefts[entry],
                ..Task::of(piece, counter)
            };
            TASKS.push(core::iter::once(task));
        }
    }

    /// Hand back every digest finished, in order, without waiting; and hand
    /// the open task to the pool, so what it holds starts hashing.
    pub fn collect(&mut self, mut digest: impl FnMut(Hash)) {
        self.publish();
        self.deliver(&mut digest);
    }

    /// Hand back every message's digest, in order: this thread hashes any
    /// task no thread has taken, and waits for the rest.
    pub fn finish(&mut self, mut digest: impl FnMut(Hash)) {
        self.publish();
        while self.delivered < self.next {
            self.help(&mut digest);
        }
    }

    /// Hand back what is done; with nothing done, hash a waiting task or
    /// pause.
    fn help(&mut self, digest: &mut impl FnMut(Hash)) {
        if self.deliver(digest) == 0 && !crate::lanes::run_one_task() {
            core::hint::spin_loop();
        }
    }

    /// A new entry of `len` bytes, waiting for room when every entry is in
    /// flight.
    #[inline(always)]
    fn add_entry(&mut self, len: usize, piece: Option<(u64, bool)>, digest: &mut impl FnMut(Hash)) -> usize {
        if self.next - self.delivered == ENTRIES {
            self.wait_for_room(digest);
        }
        let index = self.next % ENTRIES;
        self.s.entries[index] = Entry { len, piece, first: index };
        self.next += 1;
        index
    }

    /// Hand back digests, and hash tasks, until an entry is free (out of
    /// line: a frame of its own, set up only when the stream is full).
    #[cold]
    #[inline(never)]
    fn wait_for_room(&mut self, digest: &mut impl FnMut(Hash)) {
        self.publish();
        while self.next - self.delivered == ENTRIES {
            self.help(digest);
        }
    }

    /// Hand the open task to the pool.
    fn publish(&mut self) {
        if let Some(task) = self.open.take() {
            // Before the push, whose lock orders it before the threads' reads.
            self.s.lefts[self.open_first].store(task.members, Ordering::Relaxed);
            TASKS.push(core::iter::once(task));
        }
    }

    /// Hand back every finished entry from the oldest on; how many.
    fn deliver(&mut self, digest: &mut impl FnMut(Hash)) -> usize {
        let mut count = 0;
        while self.delivered < self.next {
            let index = self.delivered % ENTRIES;
            let Entry { len, piece, first } = self.s.entries[index];
            if self.s.lefts[first].load(Ordering::Acquire) != 0 {
                break;
            }
            self.delivered += 1;
            count += 1;
            // Sound: the task wrote its outs before counting `left` down.
            match piece {
                None => digest(Hash(unsafe { *self.s.outs[index].0.get() })),
                Some((counter, last)) => {
                    let out = unsafe { *self.s.pieces_out[index].0.0.get() };
                    let (key, flags, platform) = (self.key, self.flags, Platform::detect());
                    let parent = |left: &CVBytes, right: &CVBytes| crate::hasher::parent_output(left, right, &key, flags, platform);
                    let cv: CVBytes = if counter == 0 && len > CHUNK_LEN {
                        parent(out[..OUT_LEN].try_into().unwrap(), out[OUT_LEN..].try_into().unwrap()).chaining_value()
                    } else {
                        out[..OUT_LEN].try_into().unwrap()
                    };
                    // As the Hasher's stack: before pushing piece n, merge
                    // down to as many values as n has 1 bits.
                    while self.stack.len() > self.pieces.count_ones() as usize {
                        let right = self.stack.pop().unwrap();
                        let left = self.stack.pop().unwrap();
                        self.stack.push(parent(&left, &right).chaining_value());
                    }
                    self.stack.push(cv);
                    self.pieces += 1;
                    if last {
                        let mut right = self.stack.pop().unwrap();
                        while self.stack.len() > 1 {
                            right = parent(&self.stack.pop().unwrap(), &right).chaining_value();
                        }
                        digest(parent(&self.stack.pop().unwrap(), &right).root_hash());
                        self.pieces = 0;
                    }
                }
            }
        }
        count
    }
}

impl Drop for Stream<'_> {
    /// Wait for every task still reading the messages (also when the body
    /// panicked), then keep the storage as the thread's spare. A stream
    /// lives only inside [`stream`], which owns it, so this runs before the
    /// scope ends.
    fn drop(&mut self) {
        self.publish();
        for i in self.delivered..self.next {
            let left = &self.s.lefts[self.s.entries[i % ENTRIES].first];
            while left.load(Ordering::Acquire) != 0 {
                if !crate::lanes::run_one_task() {
                    core::hint::spin_loop();
                }
            }
        }
        let empty = Storage { entries: Box::new([]), outs: Box::new([]), pieces_out: Box::new([]), lefts: Box::new([]) };
        let s = core::mem::replace(&mut self.s, empty);
        SPARE.with(|spare| spare.set(Some(s)));
    }
}

#[cfg(test)]
mod test {
    use super::*;

    /// Messages of every kind the stream handles (empty, short, one length
    /// many times over, a whole piece, a piece and a byte, several pieces
    /// and a partial one), in each mode, against hash_with, in order; far
    /// more entries than a stream holds at once, so it fills and waits.
    #[test]
    fn test_stream_against_hash_with() {
        let mut input = std::vec![0u8; (1 << 20) + 200];
        crate::test::paint_test_input(&mut input);
        let key = [5u8; 32];
        let lens: std::vec::Vec<usize> =
            (0..12000).map(|i| [0, 1, 63, 64, 64, 64, 100, 1024, 1024, 1500, 4096, PIECE, PIECE + 1, 200_000, (1 << 20) + 7, 64][i % 16]).collect();
        let message = |i: usize| &input[i % 97..][..lens[i]];
        for mode in [Mode::Hash, Mode::Keyed(&key), Mode::DeriveKey("stream test")] {
            let mut got = std::vec::Vec::new();
            stream(mode, |s| {
                for i in 0..lens.len() {
                    s.submit(message(i), |h| got.push(h));
                    if i % 500 == 499 {
                        s.collect(|h| got.push(h));
                    }
                }
                s.finish(|h| got.push(h));
            });
            assert_eq!(got.len(), lens.len());
            for i in 0..lens.len() {
                assert_eq!(got[i], crate::hash_with(mode, message(i)), "message {i}, {} bytes", lens[i]);
            }
        }
    }

    /// A stream takes more messages after finishing; a body that ends
    /// without finishing panics (after the threads are done with its
    /// messages), and so does one that panics itself.
    #[test]
    fn test_stream_finish_and_panics() {
        let input = std::vec![9u8; 300_000];
        let mut got = std::vec::Vec::new();
        stream(Mode::Hash, |s| {
            for round in 0..3 {
                for len in [0, 65, 70_000] {
                    s.submit(&input[..len], |h| got.push(h));
                }
                s.finish(|h| got.push(h));
                assert_eq!(got.len(), 3 * (round + 1));
            }
        });
        assert_eq!(got[5], crate::hash(&input[..70_000]));
        for unwinding in [false, true] {
            let result = std::panic::catch_unwind(|| {
                stream(Mode::Hash, |s| {
                    for len in [10, 100_000, 64, 300_000] {
                        s.submit(&input[..len], |_| {});
                    }
                    assert!(!unwinding, "the body panics");
                })
            });
            assert!(result.is_err());
        }
    }

    /// A few messages through a stream, small enough for Miri: the handover
    /// of entries to the pool's threads and back, checked for data races.
    #[test]
    fn test_miri_stream() {
        let input = std::vec![3u8; 3 * PIECE + 5];
        let lens = [0, 64, 64, 1000, PIECE + 1, 3 * PIECE + 5];
        let mut got = std::vec::Vec::new();
        stream(Mode::Hash, |s| {
            for len in lens {
                s.submit(&input[..len], |h| got.push(h));
            }
            s.finish(|h| got.push(h));
        });
        let want: std::vec::Vec<Hash> = lens.iter().map(|&l| crate::hash(&input[..l])).collect();
        assert_eq!(got, want);
    }
}
