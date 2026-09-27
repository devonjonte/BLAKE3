//! The queue: streams of inputs handed over by ownership, hashed behind
//! the caller, their results delivered to a handler.
//!
//! # How it runs
//!
//! One engine thread per process serves every queue. A queue keeps its
//! waiting submissions in a list of its own; a submission to an idle queue
//! tells the engine the queue has work (one channel message, which wakes
//! the engine if it sleeps), and further submissions while the queue waits
//! or is served only join its list, so a busy queue costs no wakes.
//!
//! With `Efficiency::Time`, the engine cuts each submission into
//! independent tasks as it arrives (a message is one; a piece of a long
//! message is the whole subtrees `Hasher::update` would hash in it, their
//! chunk counters known from the piece's offset: `plan_subtrees`) and
//! publishes them to the queue's feed (`lanes::Feed`), a pool job that
//! stays registered while tasks are in flight: the pool's workers take
//! them as they appear, the engine takes some itself, and the engine
//! delivers from the front in submission order as each is done (a piece
//! by replaying `Hasher::update` with its subtrees' results). A message or
//! piece holding a subtree of `lanes::MIN_SPLIT_LEN` or more is hashed at
//! delivery the one-shot way, over the pool, and so is one shorter than
//! `FEED_MIN`, which costs less to hash than to hand over. Sleeping workers are woken
//! only while `WAKE_MIN` bytes or more are in flight; with nothing in
//! flight the feed retires and the workers sleep, so nothing runs between
//! bursts for work that may come (AGENTS.md, "Serve real programs").
//! `Efficiency::Energy` hashes each submission on the engine thread at
//! delivery. A queue of fixed-length messages hashes each buffer at
//! delivery through `hash_many`'s code.
//!
//! The engine serves queues in the order they told it; a queue being
//! served gives way after a delivery when another waits. The pool's
//! workers never run user code; the engine does, in the handler calls.

use crate::lanes::{Feed, Task};
use crate::{CVWords, Hash, Hasher, Mode, OUT_LEN};
use std::any::Any;
use std::collections::VecDeque;
use std::marker::PhantomData;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex, OnceLock, mpsc};

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

/// One queue's state, shared by its handle and the engine.
struct Inner<H, I, S> {
    /// Submissions waiting for the engine, and whether the engine has been
    /// told this queue has work (it is in the channel or being served).
    pending: Mutex<Pending<I>>,
    /// What the engine alone touches.
    handling: Mutex<Handling<H, I>>,
    key: CVWords,
    flags: u8,
    max_threads: usize,
    /// The fixed-length queue's message length.
    message_len: usize,
    shape: PhantomData<fn() -> S>,
}

struct Pending<I> {
    items: VecDeque<I>,
    scheduled: bool,
}

/// What the engine alone touches: the handler, the message in progress (a
/// queue of pieces), and the work in flight.
struct Handling<H, I> {
    handler: H,
    hasher: Hasher,
    /// Submissions taken from the pending list, hashed or being hashed, in
    /// order: delivered from the front as each is done.
    flight: VecDeque<Flight<I>>,
    /// Where the planning of a queue of pieces stands: past every piece
    /// in flight (the hasher stands past the delivered ones).
    plan: crate::PlanState,
    /// The tasks in flight, with `efficiency` Time; created on first use.
    feed: Option<Feed>,
    tasks: Vec<Task>,
}

/// A submission taken from the pending list: its tasks `first..first +
/// count` in the feed, or none (`count` 0: a message or piece the engine
/// hashes at delivery, alone or over the pool).
struct Flight<I> {
    item: I,
    first: usize,
    count: usize,
}

/// A queue of pieces' submissions.
enum PieceItem<B> {
    Piece(B),
    Finish,
}

/// The shortest message or piece that goes to the feed: shorter ones cost
/// less to hash at delivery than to hand over (Mac, many 1 KiB inputs:
/// 1.62 ns/B through the feed, 1.33 at delivery).
const FEED_MIN: usize = crate::SME2_SIZED_LEN;

/// The least work in flight that wakes sleeping workers for it, in bytes:
/// below it the engine hashes the tasks itself, and workers already awake
/// take their share.
const WAKE_MIN: usize = 128 * 1024;

impl<H: Send + 'static, S: 'static> Queue<H, S> {
    fn new<I: Send + 'static>(mode: Mode, efficiency: Efficiency, handler: H, message_len: usize) -> Self
    where
        Inner<H, I, S>: Serve,
    {
        let (key, flags) = mode.key_and_flags();
        let inner = Inner::<H, I, S> {
            pending: Mutex::new(Pending { items: VecDeque::new(), scheduled: false }),
            handling: Mutex::new(Handling { handler, hasher: Hasher::new_internal(&key, flags), flight: VecDeque::new(), plan: Default::default(), feed: None, tasks: Vec::new() }),
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
    Inner<H, I, S>: Serve,
{
    /// Add a submission; tell the engine when the queue was idle.
    fn submit(self: &Arc<Self>, item: I) {
        let mut pending = self.pending.lock().expect("a panic on the engine thread aborts, so no lock is poisoned");
        pending.items.push_back(item);
        if !pending.scheduled {
            pending.scheduled = true;
            drop(pending);
            engine_send(self.clone());
        }
    }
}

/// What the engine runs for a queue that has work.
trait Serve: Send + Sync + 'static {
    /// Take the waiting batch, hash it, and call the handler for each
    /// submission in order; back in line if more waits.
    fn serve(self: Arc<Self>);
}

impl<H: Send + 'static, I: Send + 'static, S: 'static> Inner<H, I, S>
where
    Inner<H, I, S>: Serve,
{
    /*
     * The engine's side of serve. Repeatedly: move pending submissions into
     * flight (`take`, which may leave some pending when the feed is full),
     * deliver the done ones from the front in order (`deliver`, returning
     * whether it delivered any), and when the front waits on tasks, hash
     * one itself or poll. Returns when nothing is in flight or pending
     * (the queue goes idle, its feed retired so the workers may sleep), or
     * after a delivery when another queue waits for the engine (this one
     * back in line, its tasks still in flight).
     */
    fn serve_with(
        self: Arc<Self>,
        take: impl Fn(&Self, &mut Handling<H, I>, &mut VecDeque<I>),
        deliver: impl Fn(&Self, &mut Handling<H, I>) -> bool,
    ) {
        let mut handling = self.handling.lock().expect("a panic on the engine thread aborts, so no lock is poisoned");
        let mut polled = std::time::Instant::now();
        loop {
            {
                let mut pending = self.pending.lock().expect("no lock is poisoned");
                take(&self, &mut handling, &mut pending.items);
                if handling.flight.is_empty() && pending.items.is_empty() {
                    pending.scheduled = false;
                    drop(pending);
                    if let Some(feed) = handling.feed.as_mut() {
                        feed.retire();
                    }
                    return;
                }
            }
            if deliver(&self, &mut handling) {
                if ENGINE_WAITING.load(Ordering::SeqCst) > 0 {
                    drop(handling);
                    engine_send(self);
                    return;
                }
            } else if !handling.feed.as_ref().is_some_and(|feed| feed.help(crate::platform::Platform::detect())) {
                crate::lanes::poll_pause(&mut polled);
            }
        }
    }
}

/// Queues sent to the engine and not yet taken: a queue being served gives
/// way after a delivery when any wait.
static ENGINE_WAITING: AtomicUsize = AtomicUsize::new(0);

/// Publish the handling's `tasks` (one submission's) to its feed and put
/// the submission in flight, or give it back when the feed lacks room.
fn publish<H, I>(handling: &mut Handling<H, I>, key: &CVWords, flags: u8, roots: bool, item: I) -> Result<(), I> {
    let feed = handling.feed.get_or_insert_with(|| Feed::new(key, flags, roots));
    if !feed.room(handling.tasks.len()) {
        return Err(item);
    }
    let first = feed.published();
    for task in handling.tasks.drain(..) {
        feed.publish(task);
    }
    feed.wake(WAKE_MIN);
    handling.flight.push_back(Flight { item, first, count: feed.published() - first });
    Ok(())
}

impl<H: MessageHandler> Serve for Inner<H, H::Buffer, shape::Messages> {
    fn serve(self: Arc<Self>) {
        self.serve_with(
            |queue, handling, pending| {
                while let Some(buffer) = pending.pop_front() {
                    let len = buffer.as_ref().len();
                    if queue.max_threads == 1 || len < FEED_MIN || len >= crate::lanes::MIN_SPLIT_LEN {
                        handling.flight.push_back(Flight { item: buffer, first: 0, count: 0 });
                        continue;
                    }
                    handling.tasks.push(Task { input: buffer.as_ref().as_ptr(), len, counter: 0 });
                    if let Err(buffer) = publish(handling, &queue.key, queue.flags, true, buffer) {
                        handling.tasks.clear();
                        pending.push_front(buffer);
                        break;
                    }
                }
            },
            |queue, handling| {
                let mut delivered = false;
                while let Some(front) = handling.flight.front() {
                    let hash = if front.count == 0 {
                        crate::lanes::hash_with_key(front.item.as_ref(), &queue.key, queue.flags, queue.max_threads)
                    } else {
                        let feed = handling.feed.as_mut().expect("tasks in flight have a feed");
                        let Some(result) = feed.result(front.first) else { break };
                        let hash = Hash(result[..OUT_LEN].try_into().unwrap());
                        feed.take_back(front.first + 1);
                        hash
                    };
                    let front = handling.flight.pop_front().unwrap();
                    handling.handler.hashed(front.item, hash);
                    delivered = true;
                }
                delivered
            },
        );
    }
}

impl<H: PieceHandler> Serve for Inner<H, PieceItem<H::Buffer>, shape::Pieces> {
    fn serve(self: Arc<Self>) {
        self.serve_with(
            |queue, handling, pending| {
                while let Some(item) = pending.pop_front() {
                    let piece = match &item {
                        PieceItem::Piece(piece) => piece.as_ref(),
                        PieceItem::Finish => {
                            handling.plan = Default::default();
                            handling.flight.push_back(Flight { item, first: 0, count: 0 });
                            continue;
                        }
                    };
                    let mut plan = handling.plan;
                    crate::plan_subtrees(&mut plan, piece, &mut handling.tasks);
                    // A short piece, and one holding a large subtree, is
                    // hashed at delivery (the large one over the pool, the
                    // one-shot way); so is every piece with efficiency
                    // Energy.
                    let alone = queue.max_threads == 1
                        || piece.len() < FEED_MIN
                        || handling.tasks.len() > crate::lanes::FEED_SLOTS / 2
                        || handling.tasks.iter().any(|task| task.len >= crate::lanes::MIN_SPLIT_LEN);
                    if alone || handling.tasks.is_empty() {
                        handling.tasks.clear();
                        handling.plan = plan;
                        handling.flight.push_back(Flight { item, first: 0, count: 0 });
                        continue;
                    }
                    match publish(handling, &queue.key, queue.flags, false, item) {
                        Ok(()) => handling.plan = plan,
                        Err(item) => {
                            handling.tasks.clear();
                            pending.push_front(item);
                            break;
                        }
                    }
                }
            },
            |queue, handling| {
                let mut delivered = false;
                while let Some(front) = handling.flight.front() {
                    match &front.item {
                        PieceItem::Piece(piece) if front.count > 0 => {
                            let feed = handling.feed.as_mut().expect("tasks in flight have a feed");
                            let (first, count) = (front.first, front.count);
                            if feed.result(first + count - 1).is_none() || (first..first + count).any(|index| feed.result(index).is_none()) {
                                break;
                            }
                            let mut results = (first..first + count).map(|index| feed.result(index).unwrap());
                            handling.hasher.update_with_results(piece.as_ref(), &mut results);
                            debug_assert!(results.next().is_none(), "every result replayed");
                            feed.take_back(first + count);
                        }
                        PieceItem::Piece(piece) => {
                            if queue.max_threads > 1 {
                                handling.hasher.update_multithreaded(piece.as_ref());
                            } else {
                                handling.hasher.update(piece.as_ref());
                            }
                        }
                        PieceItem::Finish => {}
                    }
                    match handling.flight.pop_front().unwrap().item {
                        PieceItem::Piece(piece) => handling.handler.piece_done(piece),
                        PieceItem::Finish => {
                            let hash = handling.hasher.finalize();
                            handling.hasher.reset();
                            handling.handler.finished(hash);
                        }
                    }
                    delivered = true;
                }
                delivered
            },
        );
    }
}

impl<H: FixedHandler> Serve for Inner<H, (H::Buffer, H::Digests), shape::Fixed> {
    fn serve(self: Arc<Self>) {
        self.serve_with(
            |_, handling, pending| handling.flight.extend(pending.drain(..).map(|item| Flight { item, first: 0, count: 0 })),
            |queue, handling| {
                let delivered = !handling.flight.is_empty();
                while let Some(Flight { item: (buffer, mut digests), .. }) = handling.flight.pop_front() {
                    crate::lanes::hash_many(buffer.as_ref(), queue.message_len, &queue.key, queue.flags, digests.as_mut(), queue.max_threads);
                    handling.handler.hashed(buffer, digests);
                }
                delivered
            },
        );
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
        self.inner::<H::Buffer>().submit(buffer);
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
        self.inner::<PieceItem<H::Buffer>>().submit(PieceItem::Piece(piece));
    }

    /// End the message: its digest goes to `handler.finished` after every
    /// piece has come back. Returns at once.
    pub fn finish(&self) {
        self.inner::<PieceItem<H::Buffer>>().submit(PieceItem::Finish);
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
        inner.submit((buffer, digests));
    }
}

/// Put `queue` in the engine's line.
fn engine_send(queue: Arc<dyn Serve>) {
    ENGINE_WAITING.fetch_add(1, Ordering::SeqCst);
    engine().send(queue).expect("the engine thread runs until the process ends");
}

/// The engine's channel: queues that have work, in the order they told it.
fn engine() -> &'static mpsc::Sender<Arc<dyn Serve>> {
    static ENGINE: OnceLock<mpsc::Sender<Arc<dyn Serve>>> = OnceLock::new();
    ENGINE.get_or_init(|| {
        let (sender, queues) = mpsc::channel::<Arc<dyn Serve>>();
        std::thread::Builder::new()
            .name("blake3-servil-queue".into())
            .spawn(move || {
                for queue in queues {
                    ENGINE_WAITING.fetch_sub(1, Ordering::SeqCst);
                    // A panic in a handler aborts the process (handler
                    // rule 4); so does one in the hashing, a bug.
                    if std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| queue.serve())).is_err() {
                        std::process::abort();
                    }
                }
            })
            .expect("the queue's engine thread starts");
        sender
    })
}

#[cfg(test)]
mod test {
    use crate::platform::Platform;
    use crate::{BLOCK_LEN, CHUNK_LEN, Hasher};

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
                // A sequence of piece lengths, deterministic from the step.
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
                    for (task, result) in tasks.iter().zip(&mut results) {
                        task.hash(&key, crate::KEYED_HASH, false, Platform::detect(), result);
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
