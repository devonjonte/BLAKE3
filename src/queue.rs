//! The queue: streams of inputs handed over by ownership, hashed behind
//! the caller, their results delivered to a handler.
//!
//! # How it runs
//!
//! One mechanism: `submit` turns a submission into tasks on the caller's
//! thread and returns; the pool's threads hash the tasks; one delivery
//! thread hands the results back in order.
//!
//! - **Submit.** The submission goes into the queue's list of entries, in
//!   a box of its own (its bytes, results, and count of unfinished tasks
//!   stay in place while other threads read and write them). Its tasks are
//!   the whole subtrees `Hasher::update` would hash in it, in parts of at
//!   most `lanes::TASK_LEN` (`plan_subtrees`: a piece's chunk counters
//!   follow from its offset in the message; a message is a stream of one
//!   piece). They go onto the pool's task list (`lanes::TASKS`), which
//!   wakes a thread per task in flight, the SME2 thread first.
//! - **Hash.** The SME2 thread (on SME2) and the workers (on NEON) pop
//!   tasks; each writes its result into its entry and counts down.
//! - **Deliver.** The delivery thread takes each queue's front entry once
//!   its count is zero, replays `Hasher::update` with its results (and for
//!   a message finalizes), and calls the handler. Entries without tasks it
//!   hashes itself: those shorter than `TASK_MIN` (hashed faster than
//!   handed over), batches of fixed-length messages, and everything with
//!   `Efficiency::Energy`, which the delivery thread hashes alone. While any
//!   entry is in flight it holds the pool (the threads poll across the gaps
//!   between tasks); with none it and the pool sleep, so nothing runs
//!   between bursts for work that may come (AGENTS.md, "Serve real
//!   programs").
//!
//! The pool's workers never run user code; the delivery thread does, in
//! the handler calls.

use crate::lanes::{TASKS, Task};
use crate::{CVWords, Hash, Hasher, Mode, OUT_LEN};
use std::any::Any;
use std::collections::VecDeque;
use std::marker::PhantomData;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Condvar, Mutex};

/// What a [`Queue`] spends to hash: time or energy.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Efficiency {
    /// The least time: every thread that pays, as [`hash_multithreaded`](crate::hash_multithreaded).
    Time,
    /// The least energy: one thread, as [`hash`](crate::hash).
    Energy,
}

impl Efficiency {
    fn max_threads(self) -> usize {
        match self {
            Efficiency::Time => usize::MAX,
            Efficiency::Energy => 1,
        }
    }
}

/// The handler of a [`Queue::messages`]: one message per buffer, of any
/// length. See [`Queue`] for the rules every handler follows.
pub trait MessageHandler: Send + 'static {
    /// The program's buffer, handed over by [`Queue::submit`] and back here.
    type Buffer: AsRef<[u8]> + Send + 'static;
    /// `buffer` is hashed: `hash` is its digest in the queue's mode.
    fn hashed(&mut self, buffer: Self::Buffer, hash: Hash);
}

/// The handler of a [`Queue::pieces`]: one long message in pieces. See
/// [`Queue`] for the rules every handler follows.
pub trait PieceHandler: Send + 'static {
    /// The program's buffer, handed over by [`Queue::submit`] and back here.
    type Buffer: AsRef<[u8]> + Send + 'static;
    /// `buffer`'s bytes are part of the message now; the buffer is free.
    fn piece_done(&mut self, buffer: Self::Buffer);
    /// The message that [`Queue::finish`] ended has this digest.
    fn finished(&mut self, hash: Hash);
}

/// The handler of a [`Queue::fixed`]: messages of one length, back to
/// back in each buffer as [`hash_many`](crate::hash_many) takes them. See
/// [`Queue`] for the rules every handler follows.
pub trait FixedHandler: Send + 'static {
    /// The program's buffer of messages, handed over by [`Queue::submit`]
    /// and back here.
    type Buffer: AsRef<[u8]> + Send + 'static;
    /// The program's space for the digests, one per message.
    type Digests: AsMut<[[u8; OUT_LEN]]> + Send + 'static;
    /// `buffer` is hashed: `digests[i]` holds message i's digest.
    fn hashed(&mut self, buffer: Self::Buffer, digests: Self::Digests);
}

/// The three kinds of queue, as its second type parameter; a program
/// names them only to write down a queue's type.
pub mod shape {
    /// A [`Queue::messages`](crate::Queue::messages), the default.
    pub struct Messages;
    /// A [`Queue::pieces`](crate::Queue::pieces).
    pub struct Pieces;
    /// A [`Queue::fixed`](crate::Queue::fixed).
    pub struct Fixed;
}

/// A stream of inputs, hashed behind the program. Built for efficiency
/// (see [For best performance](crate#for-best-performance)): in time or in
/// energy, chosen per queue ([`Efficiency`]).
///
/// The program submits its buffers and moves on; each comes back, hashed,
/// through a call to the queue's handler, which the program implements.
/// No bytes are copied, and the buffers in flight are the ones the program
/// made: a program that cycles a fixed set (fill one, submit it, get it
/// back in a handler call, fill it again) hashes any amount in that much
/// memory. A queue takes one shape of input: messages of any length one
/// per buffer ([`Queue::messages`]), one long message in pieces
/// ([`Queue::pieces`]), or messages of one length back to back
/// ([`Queue::fixed`]). Every queue in a process shares one engine, so a
/// program makes a queue for each stream, on any thread. Buffers that
/// wait together are hashed together, over several threads where that
/// pays, so more buffers in flight keep more threads busy.
///
/// The rules every handler follows:
///
/// 1. **Short and never blocking**: every queue's results are delivered
///    from one thread, so a slow handler delays them all; heavy work
///    belongs on the program's own threads.
/// 2. **In order, one at a time**: a queue's handler is called in
///    submission order, one call at a time.
/// 3. **Submitting from inside is allowed**: a handler may submit to any
///    queue, its own included (refill and resubmit), and never waits.
/// 4. **A panic in a handler aborts the process.**
/// 5. **Dropping a queue cancels nothing**: every buffer submitted is
///    still hashed and comes back through the handler, which lives until
///    its last call.
///
/// ```
/// use blake3_servil::{Efficiency, Hash, MessageHandler, Mode, Queue};
/// use std::sync::mpsc;
///
/// struct Digests(mpsc::Sender<(Vec<u8>, Hash)>);
/// impl MessageHandler for Digests {
///     type Buffer = Vec<u8>;
///     fn hashed(&mut self, buffer: Vec<u8>, hash: Hash) {
///         self.0.send((buffer, hash)).unwrap();
///     }
/// }
///
/// let (sender, results) = mpsc::channel();
/// let queue = Queue::messages(Mode::Hash, Efficiency::Time, Digests(sender));
/// queue.submit(b"foo".to_vec());
/// queue.submit(b"bar".to_vec());
/// assert_eq!(results.recv().unwrap(), (b"foo".to_vec(), blake3_servil::hash(b"foo")));
/// assert_eq!(results.recv().unwrap(), (b"bar".to_vec(), blake3_servil::hash(b"bar")));
/// ```
pub struct Queue<H, S = shape::Messages> {
    /// An `Arc<Inner<H, item, S>>`, its item type fixed by the shape; the
    /// shape's methods know it and downcast.
    inner: Arc<dyn Any + Send + Sync>,
    shape: PhantomData<fn() -> (H, S)>,
}

/// One queue's state, shared by its handle and the delivery thread.
struct Inner<H, I, S> {
    /// The entries in flight, in submission order.
    state: Mutex<State<I>>,
    /// What the delivery thread alone touches.
    handling: Mutex<Handling<H>>,
    key: CVWords,
    flags: u8,
    max_threads: usize,
    /// The fixed-length queue's message length.
    message_len: usize,
    shape: PhantomData<fn() -> S>,
}

struct State<I> {
    entries: VecDeque<Box<Entry<I>>>,
    /// Where planning stands: past every piece submitted (the hasher
    /// stands past the delivered ones).
    plan: crate::PlanState,
    /// Whether the delivery thread holds this queue (entries in flight).
    active: bool,
}

/// A submission in flight: its item, its tasks' results, and how many of
/// its tasks are unfinished. No results: hashed at delivery.
struct Entry<I> {
    item: I,
    results: Vec<[u8; crate::BLOCK_LEN]>,
    left: AtomicUsize,
}

struct Handling<H> {
    handler: H,
    hasher: Hasher,
}

/// A queue of pieces' submissions.
enum PieceItem<B> {
    Piece(B),
    Finish,
}

/// The shortest message or piece hashed as tasks: shorter ones cost less to
/// hash at delivery than to hand over (Mac, many 1 KiB inputs: 1.62 ns/B as
/// tasks, 1.33 at delivery).
const TASK_MIN: usize = crate::SME2_SIZED_LEN;

impl<H: Send + 'static, S: 'static> Queue<H, S> {
    fn new<I: Send + 'static>(mode: Mode, efficiency: Efficiency, handler: H, message_len: usize) -> Self
    where
        Inner<H, I, S>: Deliver,
    {
        let (key, flags) = mode.key_and_flags();
        let inner = Inner::<H, I, S> {
            state: Mutex::new(State { entries: VecDeque::new(), plan: Default::default(), active: false }),
            handling: Mutex::new(Handling { handler, hasher: Hasher::new_internal(&key, flags) }),
            key,
            flags,
            max_threads: efficiency.max_threads(),
            message_len,
            shape: PhantomData,
        };
        Queue { inner: Arc::new(inner), shape: PhantomData }
    }

    /// The queue's state as its concrete type (a type comparison).
    fn inner<I: Send + 'static>(&self) -> Arc<Inner<H, I, S>> {
        self.inner.clone().downcast().unwrap_or_else(|_| unreachable!("a queue's state has its shape's type"))
    }
}

impl<H: Send + 'static, I: Send + 'static, S: 'static> Inner<H, I, S>
where
    Inner<H, I, S>: Deliver,
{
    /// Put `item` in flight, with tasks for `plan` to cut from it (it
    /// appends their inputs and chunk counters to `tasks`, and returns
    /// whether they are the entry's work or the entry is hashed at delivery).
    fn submit(self: &Arc<Self>, item: I, plan: impl FnOnce(&I, &mut crate::PlanState, &mut Vec<Task>) -> bool) {
        let mut state = self.state.lock().expect("a panic on the delivery thread aborts, so no lock is poisoned");
        let mut entry = Box::new(Entry { item, results: Vec::new(), left: AtomicUsize::new(0) });
        let mut tasks = Vec::new();
        if plan(&entry.item, &mut state.plan, &mut tasks) && !tasks.is_empty() {
            entry.results = vec![[0; crate::BLOCK_LEN]; tasks.len()];
            entry.left = AtomicUsize::new(tasks.len());
            let (out, left) = (entry.results.as_mut_ptr(), &entry.left as *const AtomicUsize);
            TASKS.push(tasks.into_iter().enumerate().map(|(index, task)| Task {
                key: self.key,
                flags: self.flags,
                // Sound: the entry's box keeps `results` and `left` in place.
                out: unsafe { out.add(index) },
                left,
                ..task
            }));
        }
        state.entries.push_back(entry);
        if !state.active {
            state.active = true;
            drop(state);
            DELIVERY.hold(self.clone());
        }
    }

    /*
     * The delivery thread's side: hand back every entry at the front whose
     * tasks are done, each through `deliver`, outside the state's lock (the
     * handler may submit to this queue). Returns whether it delivered any,
     * and whether the queue still has entries in flight.
     */
    fn deliver_with(&self, deliver: impl Fn(&Self, &mut Handling<H>, Entry<I>)) -> (bool, bool) {
        let mut delivered = false;
        loop {
            let entry = {
                // A submitter holding the lock means entries are coming:
                // leave it be (a wait here would park this thread) and look
                // again on the next round.
                let Ok(mut state) = self.state.try_lock() else { return (delivered, true) };
                match state.entries.front() {
                    None => {
                        state.active = false;
                        return (delivered, false);
                    }
                    Some(front) if front.left.load(Ordering::Acquire) > 0 => return (delivered, true),
                    Some(_) => state.entries.pop_front().unwrap(),
                }
            };
            let mut handling = self.handling.lock().expect("no lock is poisoned");
            deliver(self, &mut handling, *entry);
            delivered = true;
        }
    }
}

/// What the delivery thread runs for a queue in flight.
trait Deliver: Send + Sync + 'static {
    /// Deliver what is done: (whether any was, whether entries remain).
    fn deliver(&self) -> (bool, bool);
}

impl<H: MessageHandler> Deliver for Inner<H, H::Buffer, shape::Messages> {
    fn deliver(&self) -> (bool, bool) {
        self.deliver_with(|queue, handling, entry| {
            let hash = if entry.results.is_empty() {
                crate::hash_serial(entry.item.as_ref(), &queue.key, queue.flags)
            } else {
                // A message is a stream of one piece.
                let mut hasher = Hasher::new_internal(&queue.key, queue.flags);
                hasher.update_with_results(entry.item.as_ref(), &mut entry.results.iter());
                hasher.finalize()
            };
            handling.handler.hashed(entry.item, hash);
        })
    }
}

impl<H: PieceHandler> Deliver for Inner<H, PieceItem<H::Buffer>, shape::Pieces> {
    fn deliver(&self) -> (bool, bool) {
        self.deliver_with(|_, handling, entry| match entry.item {
            PieceItem::Piece(piece) => {
                if entry.results.is_empty() {
                    handling.hasher.update(piece.as_ref());
                } else {
                    handling.hasher.update_with_results(piece.as_ref(), &mut entry.results.iter());
                }
                handling.handler.piece_done(piece);
            }
            PieceItem::Finish => {
                let hash = handling.hasher.finalize();
                handling.hasher.reset();
                handling.handler.finished(hash);
            }
        })
    }
}

impl<H: FixedHandler> Deliver for Inner<H, (H::Buffer, H::Digests), shape::Fixed> {
    fn deliver(&self) -> (bool, bool) {
        self.deliver_with(|queue, handling, entry| {
            let (buffer, mut digests) = entry.item;
            crate::lanes::hash_many(buffer.as_ref(), queue.message_len, &queue.key, queue.flags, digests.as_mut(), queue.max_threads);
            handling.handler.hashed(buffer, digests);
        })
    }
}

impl<H: MessageHandler> Queue<H, shape::Messages> {
    /// A queue of messages of any length, one per buffer, each digest in
    /// `mode` delivered to `handler.hashed` with its buffer.
    pub fn messages(mode: Mode, efficiency: Efficiency, handler: H) -> Self {
        Self::new::<H::Buffer>(mode, efficiency, handler, 0)
    }

    /// Hash `buffer`'s bytes as one message; returns at once.
    pub fn submit(&self, buffer: H::Buffer) {
        let inner = self.inner::<H::Buffer>();
        let tasks = inner.max_threads > 1;
        inner.submit(buffer, |buffer, _, out| {
            let bytes = buffer.as_ref();
            tasks && bytes.len() >= TASK_MIN && {
                crate::plan_subtrees(&mut Default::default(), bytes, out);
                true
            }
        });
    }
}

impl<H: PieceHandler> Queue<H, shape::Pieces> {
    /// A queue of one long message in pieces: each piece comes back to
    /// `handler.piece_done`, and after [`finish`](Self::finish) the
    /// message's digest in `mode` to `handler.finished`. The next piece
    /// after `finish` starts a new message.
    pub fn pieces(mode: Mode, efficiency: Efficiency, handler: H) -> Self {
        Self::new::<PieceItem<H::Buffer>>(mode, efficiency, handler, 0)
    }

    /// Append `piece`'s bytes to the message; returns at once.
    pub fn submit(&self, piece: H::Buffer) {
        let inner = self.inner::<PieceItem<H::Buffer>>();
        let tasks = inner.max_threads > 1;
        inner.submit(PieceItem::Piece(piece), |item, plan, out| {
            let PieceItem::Piece(piece) = item else { unreachable!("a piece") };
            let bytes = piece.as_ref();
            crate::plan_subtrees(plan, bytes, out);
            tasks && bytes.len() >= TASK_MIN
        });
    }

    /// End the message: its digest goes to `handler.finished` after every
    /// piece has come back. Returns at once.
    pub fn finish(&self) {
        self.inner::<PieceItem<H::Buffer>>().submit(PieceItem::Finish, |_, plan, _| {
            *plan = Default::default();
            false
        });
    }
}

impl<H: FixedHandler> Queue<H, shape::Fixed> {
    /// A queue of messages of `message_len` bytes, many per buffer, laid
    /// out as [`hash_many`](crate::hash_many) takes them; their digests in
    /// `mode` come back to `handler.hashed` with the buffer, in the space
    /// the program submitted beside it.
    pub fn fixed(message_len: usize, mode: Mode, efficiency: Efficiency, handler: H) -> Self {
        Self::new::<(H::Buffer, H::Digests)>(mode, efficiency, handler, message_len)
    }

    /// Hash the messages in `buffer` into `digests`, one per message: the
    /// buffer holds exactly `digests.len()` messages under
    /// [`hash_many`](crate::hash_many)'s layout (checked here). Returns at
    /// once.
    pub fn submit(&self, buffer: H::Buffer, mut digests: H::Digests) {
        let inner = self.inner::<(H::Buffer, H::Digests)>();
        let slot = crate::many::slot_len(inner.message_len);
        assert_eq!(Some(buffer.as_ref().len()), slot.checked_mul(digests.as_mut().len()), "the buffer holds one slot of whole blocks per digest");
        inner.submit((buffer, digests), |_, _, _| false);
    }
}

/// The delivery thread's queues in flight, and whether it sleeps.
struct Delivery {
    queues: Mutex<(Vec<Arc<dyn Deliver>>, bool)>,
    wake: Condvar,
}

static DELIVERY: Delivery = Delivery { queues: Mutex::new((Vec::new(), false)), wake: Condvar::new() };

impl Delivery {
    /// Give the delivery thread `queue`, which has just put an entry in
    /// flight; start the thread with the first.
    fn hold(&self, queue: Arc<dyn Deliver>) {
        static STARTED: std::sync::Once = std::sync::Once::new();
        STARTED.call_once(|| {
            std::thread::Builder::new().name("blake3-servil-queue".into()).spawn(|| DELIVERY.run()).expect("the queue's delivery thread starts");
        });
        let mut queues = self.queues.lock().unwrap();
        queues.0.push(queue);
        if queues.1 {
            self.wake.notify_one();
        }
    }

    /// Deliver from every queue in flight, in turn; poll while any entry
    /// waits on its tasks, holding the pool (its workers poll too), and
    /// sleep while no queue is in flight. A panic in a
    /// handler aborts the process (handler rule 4); so does one in the
    /// hashing, a bug.
    fn run(&self) {
        let mut polled = std::time::Instant::now();
        let mut hold = None;
        loop {
            let mut queues = {
                let mut held = self.queues.lock().unwrap();
                while held.0.is_empty() {
                    // Nothing in flight: the pool may sleep, and so does this thread.
                    hold = None;
                    held.1 = true;
                    held = self.wake.wait(held).unwrap();
                    held.1 = false;
                }
                std::mem::take(&mut held.0)
            };
            hold.get_or_insert_with(crate::lanes::Hold::new);
            let mut delivered = false;
            queues.retain(|queue| {
                let (any, in_flight) = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| queue.deliver())).unwrap_or_else(|_| std::process::abort());
                delivered |= any;
                in_flight
            });
            self.queues.lock().unwrap().0.append(&mut queues);
            if !delivered {
                crate::lanes::poll_pause(&mut polled);
            }
        }
    }
}

#[cfg(test)]
mod test {
    use crate::lanes::Task;
    use crate::platform::Platform;
    use crate::{BLOCK_LEN, CHUNK_LEN, Hasher};
    use std::sync::atomic::AtomicUsize;

    /// Pieces planned into whole subtrees, hashed as tasks, and replayed
    /// give Hasher::update's digest, for runs of pieces of many lengths
    /// (whole chunks, partial chunks, single chunks, a chunk and a byte),
    /// starting from states Hasher::update left (empty, mid-chunk, a full
    /// chunk), in batches of every size.
    #[test]
    fn planned_pieces_match_update() {
        let lens: [usize; 14] = [CHUNK_LEN + 1, 1, 1000, CHUNK_LEN, 0, 2 * CHUNK_LEN, 3 * CHUNK_LEN, 4096 + 17, 16 * CHUNK_LEN, 64 * CHUNK_LEN, 65 * CHUNK_LEN, 100_000, 128 * CHUNK_LEN, 3 * 65536];
        let input: Vec<u8> = (0..4 << 20).map(|i: u32| (i.wrapping_mul(0x9E37_79B1) >> 24) as u8).collect();
        let key = [9u32; 8];
        for start in [0, 500, CHUNK_LEN, 3 * CHUNK_LEN] {
            for (step, batch) in [(1usize, 1usize), (3, 2), (5, 3), (7, 4), (11, 6)] {
                let pieces: Vec<usize> = (0..12).map(|i| lens[(i * step + start) % lens.len()]).collect();
                let mut want = Hasher::new_internal(&key, crate::KEYED_HASH);
                let mut got = want.clone();
                want.update(&input[..start]);
                got.update(&input[..start]);
                let mut plan = crate::PlanState::default();
                crate::plan_subtrees(&mut plan, &input[..start], &mut Vec::new());
                let mut offset = start;
                for group in pieces.chunks(batch) {
                    let slices: Vec<&[u8]> = group.iter().map(|&len| {
                        let piece = &input[offset..offset + len];
                        offset += len;
                        piece
                    }).collect();
                    let mut tasks = Vec::new();
                    for piece in &slices {
                        crate::plan_subtrees(&mut plan, piece, &mut tasks);
                    }
                    let mut results = vec![[0u8; BLOCK_LEN]; tasks.len()];
                    let left = AtomicUsize::new(tasks.len());
                    for (task, result) in tasks.into_iter().zip(&mut results) {
                        Task { key, flags: crate::KEYED_HASH, out: result, left: &left, ..task }.run(Platform::detect());
                    }
                    let mut replay = results.iter();
                    for piece in &slices {
                        want.update(piece);
                        got.update_with_results(piece, &mut replay);
                    }
                    assert!(replay.as_slice().is_empty(), "every result replayed");
                    assert_eq!(got.finalize(), want.finalize(), "start {start}, pieces {pieces:?}, batches of {batch}, after {offset} bytes");
                }
            }
        }
    }
}
