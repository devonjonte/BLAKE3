//! The finish handshake (src/finish.rs: a caller waiting for its job's
//! last piece, and the workers finishing pieces) under Shuttle. This file
//! compiles the library's own finish.rs beside Shuttle's primitives, so
//! what is checked is the code the pool runs; a copy would drift. Run it so:
//!
//!     RUSTFLAGS="--cfg shuttle" cargo test --release --test shuttle_finish
//!
//! Without the cfg it compiles to nothing, so the ordinary suites are not
//! slowed by it. What it establishes: with two workers finishing one
//! piece each and a caller waiting for both, the caller returns on every
//! schedule Shuttle tries: no wake is lost between the caller's setting
//! its sleeping bit and its park, and a finisher that completes the count
//! while the bit is set unparks it. A schedule where every thread is
//! blocked is a deadlock Shuttle reports, which is the failure a lost
//! wake would be. (This test first ran under Loom, which does not model
//! SeqCst's total order; the fork's handshakes are under one tool now,
//! Shuttle: Zooko, October 23.)
#![cfg(shuttle)]

/// Loom's primitives, under the name src/finish.rs imports them by.
mod finish_sync {
    pub use shuttle::sync::Mutex;
    pub use shuttle::sync::atomic::{AtomicUsize, Ordering};
    pub use shuttle::thread;
}

#[path = "../src/finish.rs"]
#[allow(dead_code)]
mod finish;

use finish::Finish;
use shuttle::sync::Arc;
use shuttle::sync::atomic::Ordering;
use shuttle::thread;

/// The caller publishes `pieces`, each worker finishes one, the caller
/// waits for all; with `poll` polls before it sleeps. (A spurious wake,
/// which the operating system may give and the model's park does not,
/// is src/finish.rs's own test's.)
fn run(pieces: usize, polls: usize) {
    shuttle::check_pct(
        move || {
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
        },
        3000,
        3,
    );
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
