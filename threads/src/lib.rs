//! BLAKE3-Servil on every core: [`blake3_servil_core`], re-exported whole,
//! and what uses other threads: the multithreaded forms of its calls, the
//! stream. TRIAL of the two-crate layout (BLAKE3 #335).
#![allow(clippy::too_many_arguments)]

pub use blake3_servil_core::{BLOCK_LEN, BUILD_VERSION, CHUNK_LEN, ContextKey, Hash, HexError, KEY_LEN, Mode, OUT_LEN, OutputReader, convenience, initialize};

// The core's inside, under the names this crate's files know it by.
#[allow(unused_imports)]
pub(crate) use blake3_servil_core::IncrementCounter;
#[allow(unused_imports)]
pub(crate) use blake3_servil_core::convenience::Hasher;
#[allow(unused_imports)]
pub(crate) use blake3_servil_core::hazmat::platform::MAX_SIMD_DEGREE;
#[allow(unused_imports)]
pub(crate) use blake3_servil_core::hazmat::{
    CHUNK_END, CHUNK_START, CVBytes, CVWords, DERIVE_KEY_MATERIAL, IV, KEYED_HASH, MAX_DEPTH, Output, ROOT, compress_parents_parallel,
    compress_subtree_to_parent_node, hash_all_at_once, hash_many_serial, hash_serial, hash_serial_on, hasher, incremental, many, platform, tree,
};
#[allow(unused_imports)]
pub(crate) mod block {
    pub use blake3_servil_core::throughput::{Batch, Block};
}
pub(crate) mod each {
    pub use blake3_servil_core::hazmat::each::*;
}

/// The primitives src/finish.rs runs on: the standard library's here, and
/// Shuttle's in tests/shuttle_finish.rs, which compiles that file beside its own
/// `finish_sync`.
mod finish_sync {
    pub use std::sync::Mutex;
    pub use std::sync::atomic::{AtomicUsize, Ordering};
    pub use std::thread;
}
mod finish;
/// The primitives src/park.rs runs on: the standard library's here, and
/// Shuttle's in tests/shuttle_park.rs, which compiles that file beside its
/// own `park_sync`.
mod park_sync {
    pub use std::sync::OnceLock;
    pub use std::sync::atomic::{AtomicU64, AtomicUsize, Ordering};
    pub use std::thread;
}
#[cfg(blake3_gpu)]
mod gpu;
mod lanes;
mod park;
mod stream;

#[cfg(test)]
mod forms_test;
/// The tests' helpers, the core's own file: this crate's tests use the
/// same messages, fixed values and guard pages.
#[cfg(test)]
#[path = "../../src/test_support.rs"]
#[allow(dead_code)] // Some serve the core's tests alone.
pub(crate) mod test;

/// A kind of path a call of this crate's ran, for its tests (the core
/// has its own record).
#[derive(Clone, Copy)]
#[allow(dead_code)]
pub(crate) enum Ran {
    Pool = 1,
    EqualMembers = 4,
    MemberAlone = 8,
}
#[cfg(test)]
std::thread_local! {
    pub(crate) static RAN: core::cell::Cell<u32> = const { core::cell::Cell::new(0) };
    pub(crate) static COUNTED: [core::cell::Cell<u64>; 6] = const { [const { core::cell::Cell::new(0) }; 6] };
}
#[inline(always)]
#[allow(dead_code)]
pub(crate) fn ran(kind: Ran) {
    #[cfg(test)]
    RAN.with(|r| r.set(r.get() | kind as u32));
    let _ = kind;
}
#[derive(Clone, Copy)]
#[allow(dead_code)]
pub(crate) enum Counted {
    BatchZeroed = 1,
}
#[inline(always)]
#[allow(dead_code)]
pub(crate) fn counted(what: Counted) {
    #[cfg(test)]
    COUNTED.with(|c| c[what as usize].set(c[what as usize].get() + 1));
    let _ = what;
}

/// [`initialize`], and start the threads that the multithreaded calls and
/// [`stream`](throughput::stream) use: every program that makes such calls calls this once,
/// before them, in place of `initialize`. It starts `threads - 1` workers,
/// and each multithreaded call hashes on its calling thread and the
/// workers (calls made at once share the workers), and on CPUs with SME2
/// (Apple M4) the SME2 thread too; `None` means one thread
/// a CPU (`std::thread::available_parallelism`, which follows the CPU
/// affinity the program runs under). With 1, calls hash on their calling
/// thread alone: no workers start, nor the SME2 thread. Otherwise it
/// starts the first worker and returns; the first worker starts the others
/// (each 20-30 us on Linux x86-64), and calls run on the workers started
/// so far. The
/// threads wait asleep whenever no call has work for them (their memory:
/// see [Memory](crate#memory)). Later calls return at once, and must ask
/// for the same number: another `Some` panics. A panic on a worker thread
/// (a bug in this crate) ends the process, its message printed, rather
/// than leaving the call that waits for that worker's piece waiting
/// forever.
///
/// `None` counts logical CPUs, so on a CPU with SMT (Hyper-Threading) both
/// threads of each core, and that is the faster default. On an EPYC 9255,
/// the 16-input kernels leave much of a core waiting on its loads, and a
/// core's second thread fills that time: two threads hash 1.4-1.7 times
/// what one does, as with official BLAKE3. The 32-input AVX-512 kernel
/// (Linux) keeps a core busier on its own, so a second thread adds less
/// (1.1-1.3 times); even so, on 1 GiB 24 threads, one a core, took 4-14%
/// longer than 48. A thread slowed by the other thread on its core, by an
/// efficiency core or by another program takes fewer of a call's pieces,
/// and the pieces shrink toward the end of the input, so the slowest thread
/// finishes holding a small one. To leave CPUs to other work, pass fewer
/// threads.
///
/// Several programs each with a full pool share the machine without
/// trouble, and unevenly. On an i7-12700K (20 CPUs), N programs each
/// streaming 64 KiB messages hashed 26 GB/s alone, 37-41 together at 2
/// to 10, and 21-28 at 20 to 80 (400 to 1600 threads): the machine's
/// total holds, and oversubscription costs it 31% at one program a core
/// and 48% at four. What each program gets is the OS's choice among
/// equal threads: at 20 programs the luckiest got 2.6 times the
/// unluckiest, at 80, 8 times (bench-hashes #116, November 2026). A
/// program that needs a predictable share beside others sizes its pool
/// to its share of the machine.
///
/// The threads are this process's: in a child forked after they started,
/// every multithreaded call and stream panics, saying so (the child has
/// none of them). A program that forks initializes the pool in the process
/// that hashes, after any fork; its single-threaded calls work anywhere.
///
/// Each thread that makes multithreaded calls keeps a little storage for
/// them (its cut of the input, 48 KiB for inputs up to 64 MiB, and its
/// job record), grown on its first call and on the first call that
/// outgrows it, and otherwise untouched: after that, a call allocates
/// nothing. This call prepares the calling thread's; a call from another
/// thread prepares that thread's the first time.
///
/// ```
/// blake3_servil::initialize_multithreaded(None);
/// let message = vec![blake3_servil::throughput::Block::ZERO; (1 << 20) / 64];
/// let hash = blake3_servil::throughput::hash_multithreaded(blake3_servil::Mode::Plain, &message, 1 << 20);
/// assert_eq!(hash, blake3_servil::convenience::hash(&[0u8; 1 << 20]));
/// ```
pub fn initialize_multithreaded(threads: Option<core::num::NonZeroUsize>) {
    static STARTED: std::sync::OnceLock<usize> = std::sync::OnceLock::new();
    let cpus = || std::thread::available_parallelism().map_or(1, |n| n.get());
    let started = *STARTED.get_or_init(|| {
        let threads = threads.map_or_else(cpus, |n| n.get());
        initialize();
        lanes::initialize(threads);
        threads
    });
    lanes::prepare_thread();
    if let Some(threads) = threads {
        assert_eq!(
            started,
            threads.get(),
            "blake3-servil: the multithreaded calls were started with {started} threads; initialize_multithreaded cannot change that to {threads}"
        );
    }
}

/// Whether every worker of the multithreaded calls' pool is parked (false
/// before [`initialize_multithreaded`]). Undocumented and unstable, for
/// tests only: a test that needs the pool idle waits for this, not for a
/// sleep that a loaded machine could outlast.
#[doc(hidden)]
pub fn __all_workers_parked() -> bool {
    lanes::all_workers_parked()
}

/// The throughput API: the core's, and the calls that use other cores.
pub mod throughput {
    use crate::platform::Platform;
    pub use crate::stream::{Stream, stream};
    use crate::{Hash, Hasher, Mode, OUT_LEN};
    use blake3_servil_core::hazmat::each::{Item, hash_each_on};
    pub use blake3_servil_core::throughput::*;

    /// This crate's pool, for the core's Hasher: its whole subtrees of
    /// MIN_SPLIT_LEN and more.
    const POOL: crate::incremental::Pool = crate::incremental::Pool { min_len: crate::lanes::MIN_SPLIT_LEN, children: crate::lanes::subtree_children };

    /// [`Hasher::update`](crate::convenience::Hasher::update), using other CPU
    /// cores where that is faster: the same result, never slower. Pieces of
    /// 512 KiB and more use them, as [`hash_multithreaded`] does; shorter ones
    /// hash on the calling thread. One `Hasher` may take both calls. When
    /// reading the pieces keeps your thread busy, a [`stream`] is faster
    /// ([`Stream::submit_reader`], or [`Stream::submit_with`]): it hashes each
    /// piece while your thread reads the next. The program calls
    /// [`initialize_multithreaded`](crate::initialize_multithreaded) first.
    ///
    /// ```
    /// # blake3_servil::initialize_multithreaded(None);
    /// use blake3_servil::{Mode, convenience::Hasher, throughput};
    /// let input = vec![7u8; 3 << 20];
    /// let mut hasher = Hasher::new(Mode::Plain, Some(input.len() as u64));
    /// for piece in input.chunks(64 * 1024) {
    ///     throughput::update_multithreaded(&mut hasher, piece);
    /// }
    /// assert_eq!(hasher.finalize(), blake3_servil::convenience::hash(&input));
    /// ```
    pub fn update_multithreaded<'h>(hasher: &'h mut crate::convenience::Hasher, input: &[u8]) -> &'h mut crate::convenience::Hasher {
        crate::lanes::require();
        hasher.update_on(input, POOL)
    }

    /// [`hash_many`], using other CPU cores where that is faster: the same
    /// hashes, never slower.
    ///
    /// ```
    /// # blake3_servil::initialize_multithreaded(None);
    /// use blake3_servil::Mode;
    /// let mut leaves = blake3_servil::throughput::Batch::new(256, 4096);
    /// (0..4096).for_each(|i| leaves.set(i, &[7u8; 256]));
    /// let mut hashes = vec![[0u8; 32]; 4096];
    /// blake3_servil::throughput::hash_many_multithreaded(Mode::Plain, &leaves, &mut hashes);
    /// assert!(hashes.iter().all(|h| h == blake3_servil::convenience::hash(&[7u8; 256]).as_bytes()));
    /// ```
    ///
    /// **Speed**: below 512 KiB in all it runs on the calling thread, at
    /// [`hash_many`]'s speed; larger batches use the other cores too (on an
    /// Apple M4 Max, 64-byte messages from about 10 down to 3 ns each). It
    /// shares the cores with other callers as [`hash_multithreaded`] does.
    // Inlined, so a constant mode folds to its constants (as
    // convenience::hash is: no mode stored for the call to read).
    #[inline(always)]
    pub fn hash_many_multithreaded<P: Prepared>(mode: Mode, batch: &P, out: &mut [[u8; OUT_LEN]]) {
        crate::lanes::require();
        let mut room = core::mem::MaybeUninit::uninit();
        let (key, flags) = mode.key(&mut room);
        // Its length against the digests here, on the caller's thread, as
        // hash_many's kernels check it: a multiplication.
        crate::many::assert_slots(batch.bytes(), batch.message_len(), batch.slot(), out.len());
        crate::lanes::hash_many(batch.bytes(), batch.message_len(), batch.slot(), key, flags, out);
    }

    /// [`hash`], using other CPU cores where that is faster: the same
    /// [`Hash`](struct@Hash), never slower. For a message whose bytes are not
    /// in blocks (a mapped file, say), [`update_multithreaded`] into a
    /// [`Hasher`](crate::convenience::Hasher) takes any slice, at the same
    /// speed on the i7-12700K from 512 KiB to 1 GiB (about 1% slower at 1 MiB).
    ///
    /// ```
    /// # blake3_servil::initialize_multithreaded(None);
    /// use blake3_servil::{Mode, throughput::{self, Block}};
    /// let message = vec![Block::ZERO; 1 << 14];
    /// let hash = throughput::hash_multithreaded(Mode::Plain, &message, 1 << 20);
    /// assert_eq!(hash, blake3_servil::convenience::hash(&[0u8; 1 << 20]));
    /// ```
    ///
    /// **Speed**, on an Apple M4 Max (16 cores): below 512 KiB it hashes on the
    /// calling thread, at [`hash`](crate::convenience::hash)'s speed; from 512 KiB it uses the other cores
    /// too: about 14 GB/s at 1 MiB, 21 GB/s at 4 MiB, and 26 to 29 GB/s from
    /// 16 MiB, 2 to 5 times [`hash`](crate::convenience::hash). The extra threads wait asleep between calls and
    /// use no CPU then.
    ///
    /// **Several callers at once**: calls from several threads of one program
    /// share the cores in turn, each getting a fair part; a call that finds the
    /// cores all busy hashes on its own thread, at [`hash`](crate::convenience::hash)'s speed.
    ///
    /// **CPUs with performance and efficiency cores** (Intel's since Alder
    /// Lake): a multithreaded call or stream uses every core, and afterwards
    /// the OS sometimes leaves the calling thread on an efficiency core for a
    /// while, where single-threaded hashing runs at about half speed (AVX2's
    /// 256-bit operations run as two halves there). Measured on an i7-12700K
    /// under Linux 7.0: beside nonstop multithreaded streams, 7% of 16 KiB
    /// single-threaded hashes ran partly on an efficiency core, 2.2 times
    /// slower, about 6% on their average. A program that alternates the two
    /// and needs its single-threaded speed steady can keep that thread on the
    /// performance cores (`sched_setaffinity` on Linux).
    ///
    /// The program calls [`initialize_multithreaded`](crate::initialize_multithreaded) first; a call before it
    /// panics.
    // Inlined, so a constant mode folds to its constants (as
    // convenience::hash is: no mode stored for the call to read).
    #[inline]
    pub fn hash_multithreaded(mode: Mode, input: &[Block], len: usize) -> Hash {
        crate::lanes::require();
        let mut room = core::mem::MaybeUninit::uninit();
        let (key, flags) = mode.key(&mut room);
        crate::lanes::hash_with_key(&Block::bytes(input)[..len], key, flags)
    }

    /// [`hash_each`], using other CPU cores where that is faster: the
    /// same hashes, never slower. Collections of 512 KiB and more in all use
    /// them, as [`hash_multithreaded`](crate::throughput::hash_multithreaded) does.
    /// Requires `out.len() == items.len()`.
    ///
    /// ```
    /// # blake3_servil::initialize_multithreaded(None);
    /// use blake3_servil::{Mode, throughput::{self, Block}};
    /// let blocks: Vec<Vec<Block>> = (0..100).map(|i| vec![Block([i as u8; 64]); (1000 * i as usize).div_ceil(64)]).collect();
    /// let items: Vec<(&[Block], usize)> = blocks.iter().enumerate().map(|(i, b)| (&b[..], 1000 * i)).collect();
    /// let (mut a, mut b) = (vec![[0u8; 32]; 100], vec![[0u8; 32]; 100]);
    /// throughput::hash_each_multithreaded(Mode::Plain, &items, &mut a);
    /// throughput::hash_each(Mode::Plain, &items, &mut b);
    /// assert_eq!(a, b);
    /// ```
    pub fn hash_each_multithreaded(mode: Mode, items: &[(&[Block], usize)], out: &mut [[u8; OUT_LEN]]) {
        crate::lanes::require();
        assert_eq!(items.len(), out.len(), "one digest per item");
        let mut room = core::mem::MaybeUninit::uninit();
        let (key, flags) = mode.key(&mut room);
        let alone_len = |len: usize| len >= crate::lanes::MIN_SPLIT_LEN;
        let alone = |item: &[u8]| alone_len(item.len());
        // The items that hash alone are set aside in the pool's collection
        // call (a zero stand-in) and hashed after, each over the whole pool.
        if items.iter().map(|i| i.bytes().len()).filter(|&len| !alone_len(len)).sum::<usize>() < crate::lanes::MIN_SPLIT_LEN {
            hash_each_on(key, flags, items, out, Platform::detect(), |item| {
                if alone(item) { Hash::from_bytes([0; OUT_LEN]) } else { crate::hash_serial(item, key, flags) }
            });
        } else {
            crate::lanes::hash_each(key, flags, items, out);
        }
        for (item, out) in items.iter().map(Item::bytes).zip(out.iter_mut()) {
            if alone(item) {
                *out = *crate::lanes::hash_with_key(item, key, flags).as_bytes();
            }
        }
    }

    /// [`update_each`], using other CPU cores where
    /// that is faster (pieces of 512 KiB and more): the same result, never
    /// slower.
    /// Requires each `i < hashers.len()`.
    ///
    /// # Key-dependent timing
    ///
    /// The same [key-independence contract](crate#key-dependent-timing) as
    /// [`update_each`] applies when workers participate.
    pub fn update_each_multithreaded(hashers: &mut [Hasher], pieces: &[(usize, &[u8])]) {
        crate::lanes::require();
        blake3_servil_core::hazmat::each::update_turn(hashers, pieces, Some(POOL));
    }
}
