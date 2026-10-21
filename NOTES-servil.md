# Notes for the servil fork's maintainers

`servil`, the main branch of github.com/johnservil/BLAKE3, is a fork of
BLAKE3 1.8.7 published as the crate `blake3-servil` (library
`blake3_servil`), so it links beside crates.io `blake3`. Its purpose: the
fastest BLAKE3 on Apple M4-class hardware, natively and in virtual
machines, in every situation a program meets (alone, beside other work,
beside other hashing threads), judged by the worst case first (AGENTS.md).

This file holds what the code alone does not say: what runs where, the
hardware facts the design rests on, what was tried and rejected, and the
tools' pitfalls. Commit messages carry the full numbers behind each change;
`git notes --ref perf show <commit>` has each promotion's gate verdicts.
Runner job numbers below refer to `runner/results/` (outside git, on the
mount).

Treat the benchmark (`bench-hashes/`, its own repository) as a customer:
tune to the hardware, never to its harness.

## The design, and why

**Single chunk (to 1 KiB)**: c1 does the whole chunk and root in one call,
saves only the registers it names, keeps flags and counter in registers,
reads a full final block in place (a short one from a padded copy).

**NEON plans** (`CHUNK_PLANS`): each count's plan was the one with the
smallest worst ratio to the best plan across a P-core, an E-core, and the
VM, then the user's choice of P-core speed for 4 and 8 chunks. q kernels:
the last scalar lane hashes a partial chunk (block count and final length
in a seventh argument, bytes from a zero-padded copy) beside the whole
chunks for its own blocks, then a second loop finishes the whole ones. Ten
whole chunks keep one k10 call and the partial chunk after it (every split
costs more); one whole chunk uses q1 (a NEON pair with a duplicate lane)
from five partial blocks (below that P-cores lost up to 14%).

**SME2**: eight groups per entry into streaming mode (the entry costs about
half a microsecond). Serial calls use SME2 under the turn; the pool never
does (pacing SME2 against NEON, permits per SME unit, and SME-only workers
were all measured; see Rejected).

**The turn** (30c599b, the user's decision): a flag on its own cache line,
plain load and store (two calls taking it at one instant can both get it,
which is what running SME2 at once always cost). Accepted costs: shared
cells lose the mode where both copies hold an SME unit, shared small
batches +6-16%. `perf_regress` gives no verdict on it (it moves the
control, SHA-256 in the same process).

**The pool** (`lanes.rs`): `cpus - 1` workers plus callers; jobs in a
lock-free slot table; pieces pulled through a cursor, shrinking toward the
end (`next_piece_len`, 8-128 KiB, so the slowest thread's last piece is
small); one `active` count limits reservations and publishes results;
workers ranked (rank r takes from a job only 20 ns x r after registration,
so a call's pieces go to few); polls spin with `spin_loop` and yield every
20 µs, only while a job is registered or a `Hold` lives; a worker that
finds neither sleeps at once (1046c10, Zooko: nothing kept awake between
calls; before, workers spun 200 µs after their last piece, which the
benchmark's back-to-back loops rewarded and few programs meet); a call
arriving when callers fill the CPUs hashes its input whole. Every piece runs NEON (on
the Mac the NEON pool beat the SME2 pool at every mt point from 128 KiB).
Polls are loads only; `cursor` and `active` sit on their own lines
(fifteen pollers' RMWs had stalled a caller's register by 10-150 µs).
`initialize()` spawns the workers; the first multithreaded call does if the
program has not (documented: up to tens of milliseconds, once).

**Waking** (1046c10, September 27, 2026): every call meets sleeping
workers, so a call wakes only those it can use (pieces - 1, within its
budget, less those awake or on their way). The caller wakes one; the
first to wake takes the rest as owed and wakes them one by one before
its first piece. Costs measured (median of 51, after 1 ms): the waker
pays about 3 µs per `notify_one` on the Mac, 4-12 µs in the VM;
`notify_all` of fifteen costs the waker 25-56 µs; a woken worker arrives
15-20 µs after its wake on the Mac, 20-45 µs in the VM, on a core the
idle time slowed. A 1 MiB call on the Mac: the first worker at 10-18 µs,
the last at 45-70 µs, the first woken's own first piece about 35 µs in
(it spends about 2.6 µs per wake). **MIN_SPLIT_LEN = 768 KiB**: with 1 ms
of sleep before each call the split came back sooner from 512 KiB on the
Mac (136 µs against 158; 256-384 KiB level; jobs 364-367) and from
768 KiB in the VM (146 against 181; 512 KiB 154 against 130); Zooko took
the length where it pays on both (hash_multithreaded is built for a low
worst case). **Now 512 KiB** (Zooko, September 28, 2026, native first;
c46c57c): Mac after the gap 512 KiB about 40% faster, the VM's 20-30%
slower. The split once sat at 32 KiB, when the workers polled between
calls; with sleeping workers a wake costs 15-70 µs, more than a 32 KiB
input takes one core. After idle, VM: mt 64 KiB 1.68 -> 0.59 ns/B (st 0.55),
256 KiB 0.50 -> 0.28 (st 0.29), 4096 x 64 B 32.2 -> 17.1 (st 18.1); back to
back, Mac solo 1 MiB mt 0.067 ns/B against st 0.152.

**Two aims, stated in the API docs** (Zooko, September 27, 2026): each
hashing interface is built for top speed (hash, hash_many, Stream: the
fastest way to do the task for a caller that keeps it fed) or for a low
worst case (hash_multithreaded, hash_many_multithreaded: other cores only
where waking them pays on every machine measured, never slower than the
single-threaded form, nothing running between calls). A judgment call
between speed and everyone's worst case goes to the aim the interface is
built for; users who want top speed on a stream of inputs are steered to
the interfaces that keep the engine fed. Zooko on the name of the second
aim: still open ("the what else is a little unclear").

**The SME2 thread** (0366e48, September 25, 2026): a multithreaded call
that gets the SME2 turn hashes a prefix of its input itself, in whole
subtrees of up to 1 MiB back to back, sized to 1.65 NEON threads' worth
(none below 128 KiB), then helps on NEON. The split came from a sweep
(probe/sme2-thread, job 187: 62% beside one NEON thread, 38% beside three,
12% beside fifteen, on both machines). Budgets, against the NEON pool
(jobs 188-191): Mac 2 threads -20 to -25%, 4 -8 to -14%, 8 -3 to -8%, all
level to -7%; VM 2 -24 to -29%, 4 -13 to -19%, 8 -3 to -11%, all level. Two
threads now beat one at every size (they did not: 1 MiB 0.160 against
0.146 on the Mac). A 24 KiB prefix at 256 KiB over 16 threads cost 18-20%
(VM), hence the floor. **Two SME units are reachable**: two threads running
the raw chunk kernel at once, 2.0-2.4x one's throughput on the Mac, 1.7-2.0x
on the VM (job 187); a second SME2 thread in the pool is the next idea.

**Stream, deleted** (September 27, 2026, Zooko: nothing to distract from
the API plan until the benchmark is frozen). It hashed behind the caller
in four 1 MiB buffers the caller filled (a copy, unless the data arrived
by read), on a hashing thread per calling thread (59ad5c1, c242b2e), and
held the pool while its next buffer waited (a `lanes::Hold`, 3d7102e:
streamed mt 32 MiB 0.065 -> 0.043 ns/B on the Mac). The planned queue
(docs/api-design.md) passes the caller's buffers by ownership instead;
the hold comes back with it. The code is in git history.

**The planned API** (September 28, 2026; docs/api-design.md,
tests/api_plan.rs). `Mode` (plain, keyed, derive-key) and `Threads` (One,
All, Budget(n)) are arguments of `hash_with` and `hash_many_with`; the
`_with_budget` functions went. Every batch path takes the mode's key words
and flags (`many::hash_many_on(input, len, key, flags, ..)`, down to the
SME2 chunked-message kernel and the NEON `hash_messages_raw`, which gained
a flags argument): the mode's flags ride in the low byte of each kernel's
packed flags, beside CHUNK_START / CHUNK_END / PARENT / ROOT, so every mode
costs the same (perf_regress on the VM: level). `initialize()` runs the
self-test alone; `initialize_multithreaded(None)` also starts the pool.

**The queue, as rebuilt from scratch** (September 28, 2026; branch
candidate/queue-simple; `src/queue.rs` module docs have the mechanism).
The streaming API maximises throughput (Zooko): latency is spent to buy
it, and the hashing threads must never wait on a handover.
- `submit` (the caller's thread) plans tasks: the whole subtrees
  `Hasher::update` would hash, in parts of at most `lanes::TASK_LEN` (64
  KiB; 32 level, 16 KiB 50% slower on streams, jobs 468-473); a message is
  a stream of one piece and is finalized at delivery; `Queue::fixed`
  batches are ranges of slots through `hash_many`'s kernels; messages
  under 16 KiB (`TASK_MIN`) go up to 64 to a task (`lanes::Member`), side
  by side on the multi-lane kernels when each is one block, and so do
  `Queue::fixed` batches under 64 KiB (up to 64 KiB of them). An open
  task goes to the pool when full or when the delivery thread waits on
  it, outside the queue's lock. No one-shot thresholds (the 768 KiB split
  is the one-shot calls' business).
- One task list (`lanes::TASKS`, a Mutex<VecDeque> polled with try_lock).
  An SME2 thread hashes tasks only on SME2 under the turn; the workers
  only on NEON (Zooko's suggestion). Pushes wake a thread per task in
  flight, the SME2 thread first. A task costs the list about a
  microsecond of throughput on the Mac (batches of 16 64-byte messages
  as a task each: 68 ns per message, twice hashing them at delivery),
  hence members.
- One delivery thread holds the pool (`lanes::Hold`) while anything is in
  flight and sleeps with nothing in flight. The submitters and it share
  no lock on their common paths (September 28, night): entries are
  chained in submission order through each slot's `next` (a submitter
  links after `State::tail`; the delivery thread follows from the last
  slot it delivered, which it keeps as the chain's head until the next
  is delivered); each delivered slot goes back through `returned` before
  the handler runs (so the slots follow the program's in-flight count,
  not the threads' timing; handing back a round's slots at its end grew
  the queue by blocks under `tests/queue_no_alloc.rs`); the queue's hold
  is an atomic flag with a store-then-recheck handshake (the submitter
  links then sets it; the delivery thread clears it then looks for a
  link). The delivery thread waits on the entry it stopped at through
  that entry's own count, without the lock.

**Where a 64-byte message's time went** (September 28, night; VM probes
under `perf`, Mac jobs 480-497). The benchmark's program thread is the
bottleneck for short messages: it never waited for a buffer with 1024 in
flight. Its `submit` cost 258 ns on the VM: 50000 futex calls per million
messages (a std Mutex parking the loser of the queue lock, which the
delivery thread held while each front slot's count missed in its cache),
the `Arc` clone per call, the delivery thread's polling taking the
lock's line. After the chain, `lock_polling` (try_lock a while before
parking), and the borrowed state: 3000 futex calls per million, submit
about 110 ns (VM) and 63 ns (Mac, probe/queue-submit, job 492: taking a
returned buffer from the harness's channel another 25 ns). Mac, solo,
old -> new: 64 B messages 2.6 -> 1.15 ns/B, 256 B 0.63 -> 0.29, 16 KiB
0.165 -> 0.072; batches of 16 34 -> 8-19 ns/msg, of 64 21 -> 6.5, of 256
11 -> 4.2; shared batches of 16 84 -> 12-19. SHA-256 does a 64-byte
message in 36 ns, about what a handover's cache lines cost; `Queue::fixed`
is the API that beats it. The delivery thread closing a part-filled
task only after 16 polls (`CLOSE_AFTER_POLLS`): first tried on the VM
alone (level), then on the Mac after a traced run (job 680) showed
batches of 16 at two speeds, 5.5-8.8 and 30-32 ns/msg, the program's
thread busy throughout: handing each part-filled task over at once took
the submitters' lock and made tasks of a few, a loop. Taken (jobs
701-704): batches of 16 at one speed, 5.2-5.4 ns/msg; of 64, the slow
speed 15-16 -> 5.4-5.9; 1 KiB messages 0.18-0.22 -> 0.13-0.14 ns/B; VM
batches of 16 27% faster. Tried and left out: a 64 KiB byte cap
on message members (4 KiB messages 10-30% slower, jobs 494-497); each
slot on a 128-byte line of its own (jobs 504-507), the delivery thread
backing off over idle rounds (jobs 534-537), and a short message's digest
in its slot beside `left` (jobs 544-547): all level on the Mac. A task's
short messages as one chain entry (a group: items in a reused array,
one count, sealed when the task closes or another entry follows): the VM
probe slower (175-190 against 150-166 ns per message; the delivery
thread polls the open group's count while the submitter writes the same
slot), and which slots become groups follows the threads' timing, so
their first reserve came after warm-up (tests/queue_no_alloc.rs: 6
allocations); dropped unbuilt on the Mac. So the
64-byte cell sits at the handover's floor in this harness: the program's
thread, the bottleneck, spends 25 ns taking a returned buffer from its
channel and about 40-60 ns in `submit`, mostly lines another core wrote.

**The 64-byte cell at full clock** (September 28, morning, Mac, the
fixed benchmark; probe/submit-64, jobs 742, 755, 763; traced run, job
762). The program's thread stays the bottleneck (busy 99-100%), at 3.76-
3.90 GHz where SHA-256's lone thread runs at 4.45 (its cluster's other
cores are busy). Per message it retires 432-484 instructions in every
sample, and takes 129-579 cycles (median 158): the spread between
samples, 0.54-2.3 ns/B, is stalls, not clock or core kind (all on P).
Its fastest samples match SHA-256 (0.54 against 0.55 ns/B). `submit`
alone, 1024 pre-filled buffers in a burst: 28-34 ns, 100-127 cycles,
about 320 instructions per message; taking a buffer back from the
program's channel 10 ns and 122 instructions; the copy 55. So both
halves have work: `submit`'s instructions (a lock, the slot, the open
task's member, the link, the `Any` downcast through a call) and its
stalls. A write prefetch of the slot four submissions ahead
(probe/slot-prefetch, jobs 758-761): level (old against old moves the
servil cells up to 23%; SHA-256 in the same runs within 1%).

**A ceiling near one 16 KiB task a microsecond** (September 28, night,
Mac, jobs 572-587, open): two programs through their own queues move 16
KiB messages no faster in all than one alone (solo 0.07 ns/B, shared
0.14 each: about 0.87 million tasks a second), where 4 KiB messages
(gathered 64 to a task) and 64 KiB ones (a task each, at the hashing
threads' capacity) scale. Not the task's size (MEMBERS 16, tasks of
about 600 B instead of 2 KiB: level, probe/members-16) nor the list's
lock (pollers leaving it to pushers: level, probe/push-first). Gathering
messages under 32 KiB into tasks of up to 256 KiB (probe/members-32k):
shared 16 KiB 0.142 -> 0.089 ns/B, solo 0.068 -> 0.072 (+6%, fewer tasks
to spread): a trade for Zooko. The SME2 thread is not it either
(level without it). What it is (probe/submit-16k, jobs 608-611, 625):
`submit` itself, 780 ns per 16 KiB message alone and 2.6 us with two
programs: the task list's lock (acquired in 90-170 ns alone, 630 ns with
two pushers and the pollers; held 230-510 ns a push, while the pusher
copied the 2 KiB task into ring slots other cores last read and
incremented the in-flight count every finishing thread writes). The
count moved outside the lock (taken: two programs 2.0 -> 1.65 us per
message in the probe, the benchmark's shared 16 KiB -4%); pollers pausing
after a failed try_lock helped two programs (2.9 -> 2.0 us in the probe;
in the benchmark, probe/poll-pause, jobs 630-633: shared 16 KiB -9%, solo
16 KiB +3%) and was left out; 600-byte tasks (MEMBERS 16) held the
lock 137 ns instead of 227. Linking a task's members through their
entries instead of carrying them (candidate/member-links, tasks of about
100 bytes; jobs 626-629): 16 KiB messages 6% faster, batches of 4096 3%,
64-byte messages 25-33% slower (a line per member entry, 64 a task,
against the carried array's 17): left out. Keeping both would take two
task lists, small subtree tasks and gathered tasks with their arrays;
past that, a lock-free list.

**The SME2 thread and gathered tasks** (September 28, night, Mac, jobs
588-603). With no SME2 thread (probe/no-sme2-thread, NEON workers
hashing every task): 64-byte messages 15-20% faster, 16 KiB 10-15%,
batches of 16 about 10% and of 65536 7%, 1 KiB messages 15-20% slower
(or noise: 0.12-0.19 across runs), the rest level. Taken: the SME2
thread runs gathered tasks (short messages, small batches) on NEON
(64-byte messages 14-15% faster solo and shared, batches of 16 and 64
10-15%, the rest level; VM no regression). The SME2 thread running every
task on NEON (probe/sme2-thread-all-neon, jobs 604-607): level on 16 KiB
to 64 MiB messages and batches of 4096 and 65536, so subtree tasks keep
SME2, at the same speed for less energy per byte.

**The 64-byte continuous cell's two speeds** (job 680, a full run with
`--trace-clocks`): all twelve solo samples on P-cores; the benchmark
thread's clock 2.6-3.2 GHz against the core's 4.4 (other busy cores of
its cluster lower it); 0.74 ns/B at 3.06 GHz, 0.78-1.14 at 2.61. Neither
core kind nor clock explains the spread; open. Job 705 (after the
delivery thread's later close): servil 0.83-1.21 ns/B, SHA-256 in the same
run 0.84-1.07, both at 2.3-3.0 GHz (the machine's clock through a full
run, the same for both): at the clock they share, the two are close.

**The queue's ceiling for 64 KiB messages** (probe/submit-64k, job 714;
open): with the benchmark's 1 MiB in flight (16 buffers), a program
spends 3.9 us per 64 KiB message: 1.4 us in `submit`, 1.7 us waiting for
a buffer to come back, the rest copying. So the engine is the limit,
about 16 GB/s, where hash_multithreaded reaches 45: a round trip near 64
us for tasks that hash in 10 (SME2) to 30 us (a P-core's NEON). E-cores
holding up in-order delivery would explain it (80 us a task), but the
pool's threads at user-interactive QoS measured level
(probe/workers-qos, jobs 715-718). 1 MiB messages alike (10 us in
submit, 32 waiting, 57 in all). Timed by stage (probe/task-times, job
719, 64 KiB messages): NEON workers took 88% of the tasks at 33 us of
hashing each, the SME2 thread 12% at 20 us; a task waited 4-6 us in the
list; a message's round trip averaged 51 us. Tasks of about 100 bytes,
their members in a queue's fixed set of member blocks
(candidate/member-blocks, jobs 720-723): 2% faster overall, mixed by
cell (batches of 4096 7% slower solo, shared 16 KiB 11%), 64 KiB level:
the task's size is not this ceiling; left out. Tasks of 32 KiB
(probe/task-32k, jobs 724-727): large messages 10% faster solo, batches
of 1024 18% slower (two tasks now); subtrees of 32 KiB with batch tasks
kept at 64 KiB (probe/task-32k-subtrees, jobs 728-733, three runs a
side): 256 KiB-64 MiB messages 4-14% faster solo, 64 KiB 5% slower,
shared level: a trade, left out.

**Idle workers sleep** (September 28, night): a worker, and the SME2
thread, that finds nothing for 50 us (`lanes::WORKER_IDLE`, about a
wake's cost) sleeps even while a job or a queue holds the pool; pushes
and jobs wake as many as they want awake. Before, every worker a stream
woke polled until the stream drained (the queue's first burst of 1024
64-byte messages pushes about 16 tasks and woke all fifteen). VM probe,
a million 64-byte messages: user CPU 0.77 -> 0.67-0.72 s at the same
speed; after hash_multithreaded 8 MiB the process spent 145 us of CPU
in the next 200 ms, against 748; Mac continuous cells level or better
(jobs 548-551); perf_regress on the VM: no regression.

**Wakes as a tree** (probe/wake-tree, jobs 634-637): the caller waking two
sleepers itself and each woken worker up to three of those owed, instead
of one and then all the rest: level from 1 to 8 MiB and on batches of
16384 and 65536 after the gap; left out.

**Hot words on lines of their own** (September 28, night, Mac): the task
list's lock, its `queued` count, and the in-flight count apart (jobs
655-664: 16 KiB messages 14% faster solo, 9% shared, 64 B level), the
queue's submitter lock, returned-slots lock, delivery lock, and `active`
apart (jobs 665-670: 256 B 5% solo and 11% shared, 1 KiB 6%, 16 KiB 3%),
free slots taken oldest-returned first (jobs 651-654: 64 B 9%, 256 B
5-10%): taken. The pool's slots, `callers`, `linger_until`, `registered`,
and `sleepers` apart (probe/pool-lines, jobs 671-676): level, left out.

**WORKER_IDLE's length** (jobs 682-693): 200 us level with 50; 15 us
breaks lingering (workers without a piece sleep between updates: streams
of 8 MiB 0.115 -> 0.27 ns/B) and read the continuous cells 5-10% faster,
a gain that vanished when lingering was exempt from it (probe/idle-15-
linger: level): likely the lingering stream's aftereffect on the cells
after it in each round (eight cores hashing NEON at high power, then
polling), not the queue's own. Left at 50 us; lingering's effect on its
neighbours is one more cost for Zooko's bound.

**The caller's own pieces on SME2** (September 28, night): run_job's
caller hashing its later pieces on its own platform (SME2 under the
turn) instead of NEON: level on the Mac from 1 to 128 MiB (jobs
529-532); left out. **The split at 512 KiB** (`probe/split-512`): Mac
after the gap 512 KiB 0.35 -> 0.19-0.24 ns/B and 8192 messages 22.5 ->
13.3 ns/msg (jobs 538-541), VM 512 KiB 20-30% slower; taken (Zooko, September 28). **4 KiB pieces** (`MIN_PIECE_LEN`,
`probe/piece-4k`, jobs 552-559): streams through a lingering Hasher
25-70% slower (a 64 KiB job's cut ends in 4 KiB pieces), one message
level once lingering kept eight workers; left at 8 KiB.
- Storage is recycled, io_uring style (Zooko: no malloc per submission):
  slots in blocks that never move, results keeping their capacity, lists
  growing only to the program's in-flight high-water mark;
  `tests/queue_no_alloc.rs` counts every allocation (none after warm-up).
  The pool's task list is shared by every queue: each makes room in it
  for its slots times the most tasks a submission has had, and gives the
  room back when dropped (September 28, night). The room "every task in
  flight" it had before counted tasks finished but not yet counted down,
  so the list grew after warm-up once in 60-100 runs of the test (half
  the time under TSan); now 0 in 150, and 0 in 8 under TSan.
- Measured (Mac): see bench-hashes NEXT-STEPS, "Resume here". Per-message
  delivery is serial by contract, so a program's own per-message costs
  bound `Queue::messages` for tiny messages; `Queue::fixed` is the API
  for them.

**Lingering between multithreaded updates** (September 28, night; Zooko's
decision of that day in docs/api-design.md, the bound his open question).
`Hasher::update_multithreaded` past a message's first 128 KiB
(`LINGER_AFTER`), for an update of 64 KiB or more, sets the pool's
`linger_until` 50 us ahead (`lanes::LINGER`) and wakes sleepers without
waiting; workers poll while a job is registered or the deadline is
ahead. The next update hashes its whole subtrees of 64 KiB and more over
the pool (`subtree_children` from `LINGER_SPLIT_LEN`; eight NEON pieces
of 8 KiB, the caller's SME2 share zero at that size) when the eight
workers it wants are awake, else on its own thread. Mac, 64 KiB pieces
after the gap, old -> new (jobs 508-515): 128 MiB 0.24 -> 0.098 ns/B, 32
MiB 0.25 -> 0.108, 4 MiB 0.27 -> 0.146, 1 MiB 0.26 -> 0.19; shared 128
MiB 0.26 -> 0.11; 64-512 KiB level within the after-gap noise (jobs
520-523). Using the pool as soon as the deadline was set, before the
woken workers arrived, left the caller alone on NEON (slower than its
SME2): 256 KiB 10% slower. The bound's reasoning: waiting as long as a
wake costs before sleeping spends at most twice what knowing the future
would; a program that stops updating leaves workers polling at most
50 us.

Its energy (probe/energy-new against probe/energy-old, jobs 560-567;
`proc_pid_rusage` V6 `ri_energy_nj`, the kernel's estimate; Mac, 32 MiB
in 64 KiB pieces with a copy per piece): `update` 450-480 pJ/B at 0.28-
0.30 ns/B; `update_multithreaded` before lingering 405 pJ/B at 0.33,
lingering 1.7-2.6 nJ/B at 0.13-0.23 ns/B: 4-6x the energy for 1.5-2.6x
the speed. About eight cores stay busy (CPU time 1.1-1.8 ns per byte):
each 64 KiB job wakes the workers its eight pieces want, and every woken
worker polls between updates, hashing on NEON (more energy per byte than
SME2) when it has a piece. Four workers kept ready instead of eight:
level. A lingering update's 64 KiB job on four threads instead of eight
(probe/linger-4 against probe/energy-final, jobs 617-624): 18% less
energy (1.55-1.60 against 1.89-1.98 nJ/B) and half the CPU time; in the
benchmark long streams 7-12% slower solo (128 MiB 0.102 -> 0.114 ns/B)
and 18-27% shared, 1 MiB 20% faster solo and 256 KiB 20% shared: a
time-for-energy choice left to Zooko with the bound. The same probe, the queue: 1 KiB messages 5.5 -> 4.1-4.8 nJ/B at
4x the speed; 64-byte messages 450-470 -> 520-580 nJ per message at 1.4x
the speed (more threads poll: CPU per message 165 -> 290-325 ns).

**The feed design, superseded** (candidate/queue-speed, September 28): a
64-slot ring per queue beside a pool job, an engine thread doing intake,
helping, and delivery. Lessons kept: the engine as both hasher and
deliverer delayed deliveries (help-any) or starved short streams
(help-front); helping after a wait, waking after a burst, 16 KiB tasks,
and an SME2 turn per worker task all lost (probe/queue-timeline, jobs
422-449). Pieces waiting in the engine's pending list while it hashed
were the bubble the rebuilt design removed.

**Streaming scope** (Zooko, September 25, 2026): input in memory goes to
one call (`hash`, `hash_multithreaded`); input that arrives goes to a
`Stream`, each read landing in its buffers. `Hasher::update_multithreaded`
(caller and hashing taking turns) left the public API, and `Stream`'s
copying `update` and `io::Write` went with it; a caller whose pieces arrive
in buffers it does not own copies them into `buffer()` itself. The
benchmark's streamed use case measures that one pattern, each piece's
read standing as a memory copy for every contender.

**Batches over the pool**: messages gathered into ranges by
`next_piece_len`; servil mt below the split threshold hashes on the
calling thread, and fewer than 1024 messages of a block or less go there
with no length pass (a pass before SME2 kernels cost 25%).

**TABLE = 128** one-block messages per platform call (VM, 1024 messages:
128 -> 9.7 ns, 256 -> 10.2, 512 and up 12.5); likely the same
back-to-back effect; not measured natively.

**The trades, measured again on the fixed benchmark** (September 28,
morning; bench-hashes 92b21b2, whose continuous cells run in a phase of
their own at full clock; each trade cherry-picked onto c46c57c as
`trade/<name>`, Mac old/new/new/old full runs, new/old medians of the
pooled samples, servil mt; `tmp/ab.py`). The calls after the gap move
by up to 1.9x either way between identical code (their clock states), so
only the continuous cells and the long streams read here:
- `trade/members-32k` (messages under 32 KiB gathered, a gathered task
  up to 256 KiB; jobs 743-746): continuous 16 KiB messages 26% slower
  solo, 30% faster shared; the other continuous cells level (geometric
  means solo 1.01, shared 0.98).
- `trade/subtrees-32k` (subtree tasks of 32 KiB, batch tasks of 64 KiB;
  jobs 747-750): continuous messages 3% faster (geometric mean, solo and
  shared), 256 KiB-64 MiB 6-7% faster solo; continuous batches of 64
  messages 11% slower solo, of 4096 14% slower shared.
- `trade/linger-4` (a lingering update's job on four threads, 18% less
  energy in probe/linger-4; jobs 751-754): streams of 4-128 MiB in 64
  KiB pieces 2-7% slower solo and 15-41% slower shared, 1-2 MiB 13-26%
  faster; continuous cells level.
