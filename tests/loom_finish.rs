//! Every interleaving of the finish handshake (src/finish.rs: a caller
//! waiting for its job's last piece, and the workers finishing pieces),
//! under Loom. This file compiles the library's own finish.rs beside
//! Loom's primitives, so what Loom checks is the code the pool runs; a
//! copy would drift. Run it so:
//!
//!     RUSTFLAGS="--cfg loom" cargo test --release --test loom_finish
//!
//! Without the cfg it compiles to nothing (the cfg gate below), so the
//! ordinary suites are not slowed by it. What it establishes: with two
//! workers finishing one piece each and a caller waiting for both, the
//! caller returns on every schedule: no wake is lost between the
//! caller's setting its sleeping bit and its park, and a finisher that
//! completes the count while the bit is set unparks it. Loom reports a schedule where
//! every thread is blocked as a deadlock, which is the failure a lost
//! wake would be.
#![cfg(loom)]

/// Loom's primitives, under the name src/finish.rs imports them by.
mod finish_sync {
    pub use loom::sync::Mutex;
    pub use loom::sync::atomic::{AtomicUsize, Ordering};
    pub use loom::thread;
}

#[path = "../src/finish.rs"]
#[allow(dead_code)]
mod finish;

use finish::Finish;
use loom::sync::Arc;
use loom::sync::atomic::Ordering;
use loom::thread;

/// The caller publishes `pieces`, each worker finishes one, the caller
/// waits for all; with `poll` polls before it sleeps. (A spurious wake,
/// which the operating system may give and Loom's park does not model,
/// is src/finish.rs's own test's.)
fn run(pieces: usize, polls: usize) {
    loom::model(move || {
        let finish = Arc::new(Finish::new());
        finish.published.store(pieces, Ordering::SeqCst);
        finish.own();
        let workers: Vec<_> = (0..pieces)
            .map(|_| {
                let f = finish.clone();
                thread::spawn(move || f.finished(1))
            })
            .collect();
        let mut left = polls;
        finish.wait(pieces, || {
            thread::yield_now();
            left = left.saturating_sub(1);
            left > 0
        });
        assert_eq!(finish.finished_count(), pieces);
        for w in workers {
            w.join().unwrap();
        }
    });
}

#[test]
fn a_caller_sleeping_at_once_is_woken_by_the_last_piece() {
    run(2, 0);
}

#[test]
fn a_caller_polling_once_then_sleeping_is_woken() {
    run(2, 1);
}

#[test]
fn one_piece_one_worker() {
    run(1, 0);
}
