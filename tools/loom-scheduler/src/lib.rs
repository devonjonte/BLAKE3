//! A Loom model of the pool's protocol in src/lanes.rs, operation by
//! operation and ordering by ordering, small enough for Loom to explore
//! every interleaving: one caller's one-shot job of a few pieces, and two
//! workers. It checks that every piece runs exactly once, that the caller's
//! wait returns, and that no thread stays parked while work waits (Loom
//! fails a model in which every thread is blocked).
//!
//! What it models (src/lanes.rs at #59's head):
//! - `Source::publish_job`: the job's `claimed` moved past the caller's own
//!   pieces, `published` stored with Release, then a SeqCst fence.
//! - `Pool::wake_for` and `wake_one`: count the parked bits; owe the wakes
//!   beyond the first; clear a bit (fetch_and) and unpark that worker.
//! - `Source::take`: compare-and-swap on `claimed`, only below `published`.
//! - `Source::finished` and `wait`: the finisher of the last piece unparks a
//!   caller that set `sleeping`; the caller sets it, then re-reads
//!   `finished` before each park. (The real wait polls first for 200 us;
//!   polling only delays the same steps, so the model goes straight to it.)
//! - `Pool::serve`'s park: set the bit, look once more (`visible`), clear the
//!   bit and go on if work is there, else park until a waker clears it; once
//!   woken, pay the owed wakes. A worker woken chains a wake while work waits
//!   (`run_one`).
//!
//! Model-only: after its job the caller sets `stop` and wakes every worker,
//! so that the workers' threads end (Loom explores threads that end).
//!
//! **SeqCst.** Loom models SeqCst *accesses* as AcqRel (its README,
//! "Limitations"), weaker than the C11 model the code relies on, and SeqCst
//! *fences* exactly. Three places rely on SeqCst accesses for a
//! store-buffering pair (each side stores, then loads what the other
//! stored, and one of the two must see the other): a parking worker's bit
//! against its re-check, and the waker's publish against its read of the
//! bits; the waiting caller's `sleeping` against its re-read of `finished`,
//! and the last finisher's count against its read of `sleeping`; and the
//! model's `stop` against the bits. There the model puts a SeqCst fence
//! between the store and the load (`sc`), which C11 gives the same
//! guarantee as a pair of SeqCst accesses, so Loom checks what the code is
//! entitled to.

use loom::sync::atomic::{fence, AtomicBool, AtomicU64, AtomicUsize, Ordering::*};
use loom::sync::{Arc, Mutex};
use loom::thread;

/// The order the code's SeqCst accesses give a store-buffering pair (see the
/// module docs).
fn sc(pool: &Pool) {
    if pool.broken != Broken::NoFences {
        fence(SeqCst);
    }
}

pub struct Pool {
    pub workers: usize,
    /// Bit w set: worker w is parked (or about to be).
    pub parked: AtomicU64,
    pub threads: Mutex<Vec<Option<thread::Thread>>>,
    pub owed: AtomicUsize,
    // The caller's job source.
    pub claimed: AtomicUsize,
    pub published: AtomicUsize,
    pub finished: AtomicUsize,
    pub sleeping: AtomicBool,
    pub owner: Mutex<Option<thread::Thread>>,
    /// How many times each piece ran (the job's outputs).
    pub ran: Vec<AtomicUsize>,
    pub stop: AtomicBool,
    /// Model checks of the model: a parking worker skips its look after
    /// setting its bit (the protocol's guard against a lost wake-up), or
    /// the store-buffering pairs go without their fences (Loom's SeqCst).
    pub broken: Broken,
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Broken {
    Nothing,
    NoRecheck,
    NoFences,
}

impl Pool {
    pub fn new(workers: usize, pieces: usize) -> Pool {
        Pool {
            workers,
            parked: AtomicU64::new(0),
            threads: Mutex::new(vec![None; workers]),
            owed: AtomicUsize::new(0),
            claimed: AtomicUsize::new(0),
            published: AtomicUsize::new(0),
            finished: AtomicUsize::new(0),
            sleeping: AtomicBool::new(false),
            owner: Mutex::new(None),
            ran: (0..pieces).map(|_| AtomicUsize::new(0)).collect(),
            stop: AtomicBool::new(false),
            broken: Broken::Nothing,
        }
    }

    /// Source::publish_job (the job's first number 0; `own` 0).
    pub fn publish_job(&self, pieces: usize) -> usize {
        self.claimed.store(0, Relaxed);
        self.published.store(pieces, Release);
        fence(SeqCst);
        pieces
    }

    /// Source::take: a piece's number, if any is left.
    pub fn take(&self) -> Option<usize> {
        let mut c = self.claimed.load(Acquire);
        loop {
            let p = self.published.load(Acquire);
            if c >= p {
                return None;
            }
            match self.claimed.compare_exchange_weak(c, c + 1, AcqRel, Acquire) {
                Ok(_) => return Some(c),
                Err(now) => c = now,
            }
        }
    }

    fn waiting(&self) -> usize {
        self.published.load(Acquire).saturating_sub(self.claimed.load(Acquire))
    }

    /// Run piece `i`, then Source::finished(1).
    pub fn run_piece(&self, i: usize) {
        self.ran[i].fetch_add(1, Relaxed);
        let now = self.finished.fetch_add(1, SeqCst) + 1;
        sc(self);
        if now == self.published.load(SeqCst) && self.sleeping.load(SeqCst) {
            if let Some(owner) = &*self.owner.lock().unwrap() {
                owner.unpark();
            }
        }
    }

    /// Pool::wake_for.
    pub fn wake_for(&self, wanted: usize) {
        let parked = self.parked.load(SeqCst).count_ones() as usize;
        if parked == 0 {
            return;
        }
        let awake = self.workers - parked;
        if awake < wanted {
            let need = (wanted - awake).min(parked);
            if need > 1 {
                self.owed.fetch_add(need - 1, SeqCst);
            }
            self.wake_one();
        }
    }

    /// Pool::wake_one: whether a parked worker was woken.
    pub fn wake_one(&self) -> bool {
        let mut bits = self.parked.load(SeqCst);
        while bits != 0 {
            let bit = 1u64 << bits.trailing_zeros();
            let before = self.parked.fetch_and(!bit, SeqCst);
            if before & bit != 0 {
                let w = bit.trailing_zeros() as usize;
                self.threads.lock().unwrap()[w].as_ref().expect("a parked worker set its thread").unpark();
                return true;
            }
            bits = before & !bit;
        }
        false
    }

    /// Source::wait.
    pub fn wait(&self, target: usize) {
        self.sleeping.store(true, SeqCst);
        sc(self);
        while self.finished.load(SeqCst) < target {
            thread::park();
        }
        self.sleeping.store(false, SeqCst);
    }

    /// Pool::serve, for worker `me`, until `stop`.
    pub fn serve(&self, me: usize) {
        self.threads.lock().unwrap()[me] = Some(thread::current());
        let bit = 1u64 << me;
        loop {
            // sources::run_one (the job's piece path).
            if let Some(i) = self.take() {
                if self.waiting() >= 2 && self.parked.load(Relaxed) != 0 {
                    self.wake_one();
                }
                self.run_piece(i);
                continue;
            }
            if self.stop.load(SeqCst) {
                return;
            }
            // Park: the bit, one more look, then the token.
            self.parked.fetch_or(bit, SeqCst);
            sc(self);
            if self.broken != Broken::NoRecheck && (self.waiting() > 0 || self.stop.load(SeqCst)) {
                self.parked.fetch_and(!bit, SeqCst);
                continue;
            }
            while self.parked.load(SeqCst) & bit != 0 {
                thread::park();
            }
            while self.owed.fetch_update(SeqCst, SeqCst, |n| n.checked_sub(1)).is_ok() {
                if !self.wake_one() {
                    self.owed.store(0, SeqCst);
                    break;
                }
            }
        }
    }
}

/// One caller's job of `pieces` pieces beside `workers` workers, every
/// interleaving: each piece runs once, and every thread ends.
pub fn job(workers: usize, pieces: usize, broken: Broken) {
    loom::model(move || {
        let pool = Arc::new(Pool { broken, ..Pool::new(workers, pieces) });
        *pool.owner.lock().unwrap() = Some(thread::current());
        let handles: Vec<_> = (0..workers).map(|w| {
            let pool = pool.clone();
            thread::spawn(move || pool.serve(w))
        }).collect();
        // Pool::run_job.
        let target = pool.publish_job(pieces);
        if pieces > 1 {
            pool.wake_for(pieces - 1);
        }
        while let Some(i) = pool.take() {
            pool.run_piece(i);
        }
        pool.wait(target);
        for (i, ran) in pool.ran.iter().enumerate() {
            assert_eq!(ran.load(Relaxed), 1, "piece {i} ran once");
        }
        // Model-only: end the workers.
        pool.stop.store(true, SeqCst);
        sc(&pool);
        while pool.wake_one() {}
        for h in handles {
            h.join().unwrap();
        }
    });
}
