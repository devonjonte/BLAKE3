//! The queue: streams of inputs handed over by ownership, hashed behind
//! the caller, their results delivered to a handler.
//!
//! This first version is simple and correct: one engine thread per
//! process takes the submissions of every queue in order and, for each,
//! hashes it with the one-shot code (`Efficiency::Time` on every thread
//! that pays, as `hash_multithreaded` does; `Efficiency::Energy` on the
//! engine thread alone) and calls the handler. Every queue's calls
//! therefore come in submission order, one at a time. The engine thread
//! sleeps on its channel whenever nothing is submitted. The pool's
//! workers never run user code. Making it fast (batching waiting inputs,
//! pipelining hashing beside delivery, submissions without an allocation)
//! is the work that follows; docs/api-design.md has the plan.

use crate::{CVWords, Hash, Hasher, Mode, OUT_LEN};
use std::marker::PhantomData;
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
/// program makes a queue for each stream, on any thread.
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
    handler: Arc<Mutex<Handling<H>>>,
    key: CVWords,
    flags: u8,
    max_threads: usize,
    /// The fixed-length queue's message length.
    message_len: usize,
    shape: PhantomData<S>,
}

/// What the engine thread alone touches: the handler, and for a queue of
/// pieces the message in progress.
struct Handling<H> {
    handler: H,
    hasher: Option<Hasher>,
}

impl<H: Send + 'static, S> Queue<H, S> {
    fn new(mode: Mode, efficiency: Efficiency, handler: H, hasher: bool, message_len: usize) -> Self {
        let (key, flags) = mode.key_and_flags();
        let hasher = hasher.then(|| Hasher::new_internal(&key, flags));
        Queue {
            handler: Arc::new(Mutex::new(Handling { handler, hasher })),
            key,
            flags,
            max_threads: efficiency.max_threads(),
            message_len,
            shape: PhantomData,
        }
    }

    /// Run `work` on the engine thread with the handling, after every
    /// earlier submission of every queue.
    fn send(&self, work: impl FnOnce(&mut Handling<H>) + Send + 'static) {
        let handler = self.handler.clone();
        engine()
            .send(Box::new(move || {
                let mut handling = handler.lock().expect("a panic on the engine thread aborts, so no lock is poisoned");
                work(&mut handling);
            }))
            .expect("the engine thread runs until the process ends");
    }
}

impl<H: MessageHandler> Queue<H, shape::Messages> {
    /// A queue of messages of any length, one per buffer, each digest in
    /// `mode` delivered to `handler.hashed` with its buffer.
    pub fn messages(mode: Mode, efficiency: Efficiency, handler: H) -> Self {
        Self::new(mode, efficiency, handler, false, 0)
    }

    /// Hash `buffer`'s bytes as one message; returns at once.
    pub fn submit(&self, buffer: H::Buffer) {
        let (key, flags, max_threads) = (self.key, self.flags, self.max_threads);
        self.send(move |handling| {
            let hash = crate::lanes::hash_with_key(buffer.as_ref(), &key, flags, max_threads);
            handling.handler.hashed(buffer, hash);
        });
    }
}

impl<H: PieceHandler> Queue<H, shape::Pieces> {
    /// A queue of one long message in pieces: each piece comes back to
    /// `handler.piece_done`, and after [`finish`](Self::finish) the
    /// message's digest in `mode` to `handler.finished`. The next piece
    /// after `finish` starts a new message.
    pub fn pieces(mode: Mode, efficiency: Efficiency, handler: H) -> Self {
        Self::new(mode, efficiency, handler, true, 0)
    }

    /// Append `piece`'s bytes to the message; returns at once.
    pub fn submit(&self, piece: H::Buffer) {
        let pooled = self.max_threads > 1;
        self.send(move |handling| {
            let hasher = handling.hasher.as_mut().expect("a queue of pieces holds its message");
            if pooled {
                hasher.update_multithreaded(piece.as_ref());
            } else {
                hasher.update(piece.as_ref());
            }
            handling.handler.piece_done(piece);
        });
    }

    /// End the message: its digest goes to `handler.finished` after every
    /// piece has come back. Returns at once.
    pub fn finish(&self) {
        self.send(move |handling| {
            let hasher = handling.hasher.as_mut().expect("a queue of pieces holds its message");
            let hash = hasher.finalize();
            hasher.reset();
            handling.handler.finished(hash);
        });
    }
}

impl<H: FixedHandler> Queue<H, shape::Fixed> {
    /// A queue of messages of `message_len` bytes, many per buffer, laid
    /// out as [`hash_many`](crate::hash_many) takes them; their digests in
    /// `mode` come back to `handler.hashed` with the buffer, in the space
    /// the program submitted beside it.
    pub fn fixed(message_len: usize, mode: Mode, efficiency: Efficiency, handler: H) -> Self {
        Self::new(mode, efficiency, handler, false, message_len)
    }

    /// Hash the messages in `buffer` into `digests`, one per message: the
    /// buffer holds exactly `digests.len()` messages under
    /// [`hash_many`](crate::hash_many)'s layout (checked here). Returns at
    /// once.
    pub fn submit(&self, buffer: H::Buffer, mut digests: H::Digests) {
        let message_len = self.message_len;
        let slot = crate::many::slot_len(message_len);
        assert_eq!(Some(buffer.as_ref().len()), slot.checked_mul(digests.as_mut().len()), "the buffer holds one slot of whole blocks per digest");
        let (key, flags, max_threads) = (self.key, self.flags, self.max_threads);
        self.send(move |handling| {
            crate::lanes::hash_many(buffer.as_ref(), message_len, &key, flags, digests.as_mut(), max_threads);
            handling.handler.hashed(buffer, digests);
        });
    }
}

type Work = Box<dyn FnOnce() + Send>;

/// The engine's submissions, started with the first queue.
fn engine() -> &'static mpsc::Sender<Work> {
    static ENGINE: OnceLock<mpsc::Sender<Work>> = OnceLock::new();
    ENGINE.get_or_init(|| {
        let (sender, submissions) = mpsc::channel::<Work>();
        std::thread::Builder::new()
            .name("blake3-servil-queue".into())
            .spawn(move || {
                for work in submissions {
                    // A panic in a handler aborts the process (handler
                    // rule 4); so does one in the hashing, a bug.
                    if std::panic::catch_unwind(std::panic::AssertUnwindSafe(work)).is_err() {
                        std::process::abort();
                    }
                }
            })
            .expect("the queue's engine thread starts");
        sender
    })
}
