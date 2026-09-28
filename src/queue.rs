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
/// of throughput (see [For best performance](crate#for-best-performance)):
/// the most bytes or messages hashed per second, or per joule, chosen per
/// queue ([`Efficiency`]). Each submission comes back after a handover, so
/// a single input takes longer than [`hash`](crate::hash) takes; for the
/// lowest latency per input, call the one-shot functions. The queue's
/// throughput is the hashing's when the program keeps enough in flight to
/// cover the round trip: a few buffers of 64 KiB and more, or many small
/// messages (or batches of them, [`Queue::fixed`]).
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

/*
 * A queue's storage is allocated once and recycled, as io_uring's rings
 * are: submissions in flight occupy slots, which live in blocks that never
 * move (so tasks may point into them) and are handed back after delivery;
 * a block is added only when more submissions are in flight than ever
 * before, and the lists below keep their capacity. So a program cycling a
 * fixed set of buffers makes the queue allocate nothing after its first
 * round.
 */
struct State<I> {
    /// The slots' blocks, each SLOT_BLOCK slots (from Box::into_raw; freed
    /// on drop).
    blocks: Vec<*mut [Slot<I>; SLOT_BLOCK]>,
    /// The slots in flight, in submission order.
    order: VecDeque<usize>,
    /// The slots free.
    free: Vec<usize>,
    /// Room to plan a submission's tasks in.
    tasks: Vec<Task>,
    /// The most tasks a submission has had: every slot's results make room
    /// for as many when handed out, so no slot grows later than another.
    most: usize,
    /// Where planning stands: past every piece submitted (the hasher
    /// stands past the delivered ones).
    plan: crate::PlanState,
    /// Whether the delivery thread holds this queue (entries in flight).
    active: bool,
    /// Short messages gathered into one task, not yet handed to the pool.
    open: Option<Task>,
}

// Sound: the blocks are the state's own, reached through its lock or, for
// a slot in flight, by the one thread that holds it (below).
unsafe impl<I: Send> Send for State<I> {}

const SLOT_BLOCK: usize = 16;

/// A submission in flight: its item, its tasks' results (none: hashed at
/// delivery), and how many of its tasks are unfinished. The results keep
/// their capacity from one submission to the next.
struct Slot<I> {
    item: Option<I>,
    results: Vec<[u8; crate::BLOCK_LEN]>,
    left: AtomicUsize,
    /// Whether `results` holds the message's digest (a short message
    /// hashed with others), not its subtrees' results.
    digest: bool,
}

impl<I> State<I> {
    fn slot(&self, index: usize) -> *mut Slot<I> {
        // Sound: blocks[index / SLOT_BLOCK] exists for every slot handed out.
        unsafe { (self.blocks[index / SLOT_BLOCK] as *mut Slot<I>).add(index % SLOT_BLOCK) }
    }

    /// A free slot, adding a block when none is.
    fn take_slot(&mut self) -> usize {
        if self.free.is_empty() {
            let first = self.blocks.len() * SLOT_BLOCK;
            self.blocks.push(Box::into_raw(Box::new(std::array::from_fn(|_| Slot { item: None, results: Vec::with_capacity(self.most.max(1)), left: AtomicUsize::new(0), digest: false }))));
            self.free.extend((first..first + SLOT_BLOCK).rev());
            self.order.reserve(self.blocks.len() * SLOT_BLOCK);
        }
        self.free.pop().unwrap()
    }
}

impl<I> State<I> {
    /// Hand the open batch of short messages to the pool when it is full,
    /// or (with `now`) whenever a hashing thread would otherwise have
    /// nothing to do: a busy pool lets batches fill, an idle one gains more
    /// from a short batch now.
    fn close_open(&mut self, now: bool) {
        let full = self.open.as_ref().is_some_and(|open| open.members == crate::lanes::MEMBERS);
        if full || (now && self.open.is_some() && TASKS.in_flight() < crate::lanes::task_threads()) {
            TASKS.push(self.open.take().into_iter());
        }
    }
}

impl<I> Drop for State<I> {
    fn drop(&mut self) {
        for &block in &self.blocks {
            // Sound: from Box::into_raw, dropped once, with nothing in flight
            // (the delivery thread holds the queue until its last delivery).
            drop(unsafe { Box::from_raw(block) });
        }
    }
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

/// The shortest message or piece hashed as tasks of its own: shorter
/// messages go several to a task (`lanes::MEMBERS`), shorter pieces are
/// hashed at delivery (a piece's bytes join the message in order).
const TASK_MIN: usize = crate::SME2_SIZED_LEN;

impl<H: Send + 'static, S: 'static> Queue<H, S> {
    fn new<I: Send + 'static>(mode: Mode, efficiency: Efficiency, handler: H, message_len: usize) -> Self
    where
        Inner<H, I, S>: Deliver,
    {
        let (key, flags) = mode.key_and_flags();
        let inner = Inner::<H, I, S> {
            state: Mutex::new(State { blocks: Vec::new(), order: VecDeque::new(), free: Vec::new(), tasks: Vec::new(), most: 0, plan: Default::default(), active: false, open: None }),
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
    fn submit(self: &Arc<Self>, item: I, plan: impl FnOnce(&mut I, &mut crate::PlanState, &mut Vec<Task>) -> bool) {
        let mut guard = self.state.lock().expect("a panic on the delivery thread aborts, so no lock is poisoned");
        let state = &mut *guard;
        let index = state.take_slot();
        // Sound: a free slot is this thread's until it enters `order`.
        let slot = unsafe { &mut *state.slot(index) };
        let item = slot.item.insert(item);
        slot.results.clear();
        slot.digest = false;
        let mut tasks = std::mem::take(&mut state.tasks);
        let planned = plan(item, &mut state.plan, &mut tasks);
        if tasks.len() > state.most {
            state.most = tasks.len();
            // Every free slot makes room now, the ones in flight when next
            // handed out (below): growth follows the program's submissions,
            // not which slot timing hands out.
            for &free in &state.free {
                // Sound: a free slot is untouched by any task.
                unsafe { &mut *state.slot(free) }.results.reserve(state.most);
            }
        }
        slot.results.reserve(state.most);
        if planned && !tasks.is_empty() {
            slot.results.resize(tasks.len(), [0; crate::BLOCK_LEN]);
            slot.left.store(tasks.len(), Ordering::Relaxed);
            let (out, left) = (slot.results.as_mut_ptr(), &slot.left as *const AtomicUsize);
            TASKS.push(tasks.drain(..).enumerate().map(|(index, task)| Task {
                key: self.key,
                flags: self.flags,
                // Sound: the slot's block and results stay in place until
                // its delivery, after `left` reaches zero.
                out: task.out.is_null().then(|| unsafe { out.add(index) } as *mut u8).unwrap_or(task.out),
                left,
                ..task
            }));
        }
        tasks.clear();
        state.tasks = tasks;
        state.order.push_back(index);
        let mut state = guard;
        if !state.active {
            state.active = true;
            drop(state);
            DELIVERY.hold(self.clone());
        }
    }

    /// Put a short message in flight as a member of the queue's open batch
    /// of short messages (`bytes` from the item, which stays in its slot).
    fn submit_member(self: &Arc<Self>, item: I, bytes: impl FnOnce(&I) -> &[u8]) {
        let mut guard = self.state.lock().expect("a panic on the delivery thread aborts, so no lock is poisoned");
        let state = &mut *guard;
        let index = state.take_slot();
        // Sound: a free slot is this thread's until it enters `order`.
        let slot = unsafe { &mut *state.slot(index) };
        let bytes = bytes(slot.item.insert(item));
        slot.results.clear();
        slot.results.resize(1, [0; crate::BLOCK_LEN]);
        slot.digest = true;
        slot.left.store(1, Ordering::Relaxed);
        let open = state.open.get_or_insert_with(|| Task::members(&self.key, self.flags));
        // Sound: the slot's block, bytes, and result stay in place until its
        // delivery, after `left` reaches zero.
        open.member[open.members] = crate::lanes::Member { input: bytes.as_ptr(), len: bytes.len(), out: slot.results.as_mut_ptr() as *mut u8, left: &slot.left };
        open.members += 1;
        state.close_open(true);
        state.order.push_back(index);
        if !guard.active {
            guard.active = true;
            drop(guard);
            DELIVERY.hold(self.clone());
        }
    }

    /*
     * The delivery thread's side: hand back every entry at the front whose
     * tasks are done, each through `deliver`, outside the state's lock (the
     * handler may submit to this queue). Returns whether it delivered any,
     * and whether the queue still has entries in flight.
     */
    fn deliver_with(&self, deliver: impl Fn(&Self, &mut Handling<H>, I, &[[u8; crate::BLOCK_LEN]], bool)) -> (bool, bool) {
        let mut delivered = false;
        loop {
            let (index, slot, item) = {
                // A submitter holding the lock means entries are coming:
                // leave it be (a wait here would park this thread) and look
                // again on the next round.
                let Ok(mut state) = self.state.try_lock() else { return (delivered, true) };
                let Some(&index) = state.order.front() else {
                    state.active = false;
                    return (delivered, false);
                };
                let slot = state.slot(index);
                // Sound: the front slot is in flight, and only this thread
                // takes slots out of `order`.
                if unsafe { &(*slot).left }.load(Ordering::Acquire) > 0 {
                    // It may wait in the open batch: hand that over once a
                    // hashing thread is free.
                    state.close_open(true);
                    return (delivered, true);
                }
                state.order.pop_front();
                (index, slot, unsafe { (*slot).item.take() }.expect("a slot in flight holds its item"))
            };
            let mut handling = self.handling.lock().expect("no lock is poisoned");
            // Sound: the slot is out of `order` and not yet free: this
            // thread's alone, its tasks finished.
            deliver(self, &mut handling, item, unsafe { &(*slot).results }, unsafe { (*slot).digest });
            drop(handling);
            self.state.lock().expect("no lock is poisoned").free.push(index);
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
        self.deliver_with(|queue, handling, buffer, results, digest| {
            let hash = if digest {
                Hash(results[0][..OUT_LEN].try_into().unwrap())
            } else if results.is_empty() {
                crate::hash_serial(buffer.as_ref(), &queue.key, queue.flags)
            } else {
                // A message is a stream of one piece.
                let mut hasher = Hasher::new_internal(&queue.key, queue.flags);
                hasher.update_with_results(buffer.as_ref(), &mut results.iter());
                hasher.finalize()
            };
            handling.handler.hashed(buffer, hash);
        })
    }
}

impl<H: PieceHandler> Deliver for Inner<H, PieceItem<H::Buffer>, shape::Pieces> {
    fn deliver(&self) -> (bool, bool) {
        self.deliver_with(|_, handling, item, results, _| match item {
            PieceItem::Piece(piece) => {
                if results.is_empty() {
                    handling.hasher.update(piece.as_ref());
                } else {
                    handling.hasher.update_with_results(piece.as_ref(), &mut results.iter());
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
        self.deliver_with(|queue, handling, (buffer, mut digests), results, _| {
            if results.is_empty() {
                crate::hash_many_serial(buffer.as_ref(), queue.message_len, &queue.key, queue.flags, digests.as_mut());
            }
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
        if tasks && buffer.as_ref().len() < TASK_MIN {
            return inner.submit_member(buffer, |buffer| buffer.as_ref());
        }
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
        let (message_len, tasks) = (inner.message_len, inner.max_threads > 1);
        let slot = crate::many::slot_len(message_len);
        assert_eq!(Some(buffer.as_ref().len()), slot.checked_mul(digests.as_mut().len()), "the buffer holds one slot of whole blocks per digest");
        inner.submit((buffer, digests), |(buffer, digests), _, out| {
            let bytes = buffer.as_ref();
            // The digests' space is the program's, in the slot with its
            // buffer, which stays put until delivery.
            let digests = digests.as_mut().as_mut_ptr();
            let per_task = (crate::lanes::TASK_LEN / slot).max(1);
            for (index, range) in bytes.chunks(per_task * slot).enumerate() {
                let mut task = Task::of(range, 0);
                task.batch = Some(message_len);
                // Sound: `per_task` digests per range, within the space.
                task.out = unsafe { digests.add(index * per_task) } as *mut u8;
                out.push(task);
            }
            tasks && bytes.len() >= TASK_MIN
        });
    }
}

/// The delivery thread's queues in flight, and whether it sleeps.
struct Delivery {
    /// The queues handed over, whether the thread sleeps, and how many
    /// queues it holds (both lists keep room for all of them).
    queues: Mutex<(Vec<Arc<dyn Deliver>>, bool, usize)>,
    wake: Condvar,
}

static DELIVERY: Delivery = Delivery { queues: Mutex::new((Vec::new(), false, 0)), wake: Condvar::new() };

impl Delivery {
    /// Give the delivery thread `queue`, which has just put an entry in
    /// flight; start the thread with the first.
    fn hold(&self, queue: Arc<dyn Deliver>) {
        static STARTED: std::sync::Once = std::sync::Once::new();
        STARTED.call_once(|| {
            std::thread::Builder::new().name("blake3-servil-queue".into()).spawn(|| DELIVERY.run()).expect("the queue's delivery thread starts");
        });
        let mut queues = self.queues.lock().unwrap();
        queues.2 += 1;
        let held = queues.2;
        queues.0.reserve(held);
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
        // The queues this round serves, swapped with the held list's (both
        // keep their capacity: no allocation).
        let mut queues: Vec<Arc<dyn Deliver>> = Vec::new();
        loop {
            {
                let mut held = self.queues.lock().unwrap();
                while held.0.is_empty() {
                    // Nothing in flight: the pool may sleep, and so does this thread.
                    hold = None;
                    held.1 = true;
                    held = self.wake.wait(held).unwrap();
                    held.1 = false;
                }
                std::mem::swap(&mut held.0, &mut queues);
                let room = held.2;
                held.0.reserve(room);
            }
            hold.get_or_insert_with(crate::lanes::Hold::new);
            let mut delivered = false;
            let mut idle = 0;
            queues.retain(|queue| {
                let (any, in_flight) = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| queue.deliver())).unwrap_or_else(|_| std::process::abort());
                delivered |= any;
                idle += usize::from(!in_flight);
                in_flight
            });
            let mut held = self.queues.lock().unwrap();
            held.2 -= idle;
            held.0.append(&mut queues);
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
                        Task { key, flags: crate::KEYED_HASH, out: result.as_mut_ptr(), left: &left, ..task }.run(Platform::detect());
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
