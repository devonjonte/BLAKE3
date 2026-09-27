# Style Guides

These style guides read the same in the fork's `AGENTS.md` and in bench-hashes' `AGENTS.md`; a change goes into both.

## Communication

- Name Zooko as "Zooko" alone, in every document, commit, issue, pull request, and message; never add a surname (his wish, September 26, 2026).
- Phrase positively or neutrally; avoid negations and "not this, but that" contrasts.
- Frame positively: show the promising, successful aspects of the recommended path. Mention an alternative only when its trade-offs deserve our attention.
- The reader has limited working memory and limited ability to search back through recent text. Include only what the current focus needs.

Sixteen actions that improve writing:
1. Sand off filler words
2. Find the real actors
3. Restore actions to verbs
4. Delete empty verbs
5. Prefer characters as subjects
6. Put subjects and verbs together
7. Put verbs and objects together
8. Make the opening familiar
9. Put new and important information last
10. Repair topic flow
11. Repair stress flow
12. Establish a clear topic sentence
13. Make subjects consistent across a passage
14. Control passive voice deliberately
15. Name responsibility
16. Trim metadiscourse

## Presentation: every item costs the reader

Every piece of information in a UI, a report, or a document costs its reader attention and risks fatigue and overflow. Review each one with two questions: who is this designed for, and which information pays that reader much more than it costs them? Keep what passes; cut the rest. Information for maintainers (diagnostics, spreads, provenance details, internal names) stays out of what users read; it belongs in maintainer notes, logs, and diagnostic flags.

## Presentation: write each page for a reader who holds only the page

A page (a graph, a report, a README, a docstring) carries its own context:

- **Its terms:** each is common knowledge or introduced on the page.
- **Its questions:** each sentence answers a question the page itself raises, in the order the reader meets them.
- **Its tense:** the page describes what is, as it is now. How it got here belongs to commit messages and notes.

**Three readers.** Picture the page's readers at three depths of context and serve them together:

- the *newcomer*, who landed on the page from idle curiosity and holds only the page;
- the *regular*, who knows the tool and opens its details;
- the *maintainer* (Zooko, John Servil, and their like), who knows its history; maintainers' documents and comments in the page's source serve this reader.

Keep what serves one reader and reads cleanly to the others; an item legible to one reader alone moves behind a door or into the maintainers' documents. Writers naturally picture themselves as the reader, so name the three readers explicitly while reviewing.

**Show before you tell.** Position, shape, colour, grouping, arrows, and absence carry meaning at a glance, and words and numbers follow them. A hash of the run that takes no part in a plot appears in its legend in pale, still type; an arrow runs beside "higher is better" pointing up; a band on a strip shows which part of the inputs the plots show. A mark beside its words, parallel to them, lets the reader take in both at once.

**Doors.** Details sit behind doors (a collapsed section, a tooltip, a panel that opens on a click), each placed for the reader who wants what is behind it. The door itself tells every other reader that the page is theirs to enjoy without it.

**Generated text is computed from what the page shows.** A sentence about the page's own contents is built from the same data as the page, so it names only what is on the page, whatever options produced it.

**A revision ends with a fresh reading.** After every change, reread the whole page (for a graph, a render of it) as each of the three readers; the revision is done when the page reads as if written fresh.

## Simplicity

Prefer the simplest design that meets the contract and performs well.
Simplicity has several dimensions:

- **Conceptual ease:** a reader can understand and predict the design with
  a few familiar concepts.
- **Less code and information:** fewer moving parts, less state, and fewer
  facts to carry in working memory.
- **Fewer runtime cases:** fewer branches, special cases, tuning knobs,
  and distinct operating regimes.

Use one clear mechanism wherever it serves. Added complexity earns its
place through a concrete need and a demonstrated benefit. When approaches
perform similarly, choose the simpler one. Apply this standard to code,
interfaces, documentation, and performance optimizations.

## Strategy: the recommended usage first (Zooko, September 25, 2026)

Make the recommended usage as fast as possible, and tell users how to use it that way. The recommended usage: one thread makes all of a program's calls (the single-threaded ones, or the multithreaded ones, which spread the work under the hood), handing over whole inputs, batches, or large stream pieces. Within it, the minimax rule below still holds over input sizes, batch sizes, and machines (the VM included): no weak size, and effort first where we trail. Misuse and misfortune (several of a program's threads calling at once, other load on the machine, the shared scenario) stay measured and reported in every benchmark, record, and check, and stay cared for: keep cheap protections such as the SME2 lock, report what they cost, and improve them where it costs the recommended usage nothing. They no longer veto a change that helps the recommended usage; such a change records the shared cells it slows, with their numbers, in its commit message. `perf_regress` holds a change for review when any solo cell is slower by more than 3% (the user's rule, September 25, 2026); a held change lands only with `--no-verify` and the held cells and their numbers in the message. It reports a shared cell slower by more than 10% and lets the change through, presuming a reason worth more (a larger gain elsewhere, simpler code); the commit message names the cells, their numbers, and that reason (the user's rule, September 26, 2026). The rule detects; whether a change is worth its cost stays judgment, and cells the check does not measure (other sizes, E-cores, two-speed shifts) stay the probes' and the review's business.

## Strategy: minimax

Within the recommended usage (above), judge a design by its worst plausible case first. Performing well in every situation (or as many as possible) beats excelling in some while falling behind in others: a user meets whatever situation their own program creates. Plausible situations include several threads of one program hashing at once, other programs busy on the machine, a quiet machine, a VM, and every input size and batch size. For each candidate, find the situation where it does worst and compare those worst cases; a best case decides only between designs whose worst cases are level. Consequences here:

- A resource that can be shared (an SME unit, a cluster, memory bandwidth) is judged at its shared speed, since some program will share it.
- A multithreaded call that runs slower than the single-threaded call on the same task is a defect: it could have run single-threaded.
- A task that takes more than proportionally longer than a smaller one is a defect: it could have done the smaller task twice.
- Effort goes first to the cells where we lead by the least or trail.

## Strategy: we own every slowdown a user could meet

Our duty is to the user, so we take responsibility for every performance problem that could plausibly reach one, whatever its cause. A slowdown that comes from the operating system's scheduler, the hardware, thread placement, clocks, or an interaction we find hard to reproduce, understand, or control is still ours. We never set such a slowdown aside with "it is probably the environment, not our code". Each one gets one of three outcomes, in this order of preference:

1. Control it: change the design so the slowdown cannot happen, or cannot happen from anything we did.
2. Understand it well enough to tell users how to control it, and document that.
3. At the least, understand it well enough to predict when it happens and how large it is, and state that in the user-facing results or docs.

Until a problem reaches one of these outcomes it stays open: it goes on the next-steps list, the record or commit that shows it says so, and it blocks the claim that a change has no regression.

## Correctness tests

Use reproducible inputs and fixed, independently established expected
outputs. A deterministic RNG is a compact specification of test bytes;
record its algorithm, seed, and length, and check in the expected digests.
Published test vectors and independent reference implementations establish
the answers. Regenerating golden outputs is an explicit, reviewed action.
Tests never silently regenerate their own expected answers.

The same fixed vectors can exercise different kernels, thread budgets,
concurrent calls, and scheduling interleavings. Input generation and
execution scheduling are separate concerns. Differential tests supplement
these anchors. Correctness is each project's tests' business: a benchmark
checks no outputs (Zooko, September 26, 2026), and only keeps every
result from being optimized away.

## Measuring: wall time and cycles, both, always

Whenever code is timed (a probe, a benchmark, a throwaway loop in a scratch directory), record two clocks together, through the one timing helper each project provides: wall time, which a caller waits for, and the thread's core cycles per core kind, which do not change with the clock speed and do not count time the core waits on a coprocessor (the SME unit). Their ratio, cycles per ns, says which state a measurement ran in (the core kind's clock; the SME unit's fast or slow state). Speed verdicts use wall time, compared within one state, with the state mix reported; a change that shifts the mix has that shift as part of its effect. Cycles explain and locate time, and are the finer comparison for core-only kernels across core kinds. When the two disagree, that is a finding to investigate, never a reason to prefer one. Report wall time as measured, never scaled by cycles, until we know which part of their ratio is ours (our code's SME waits, the power it draws) and which is the machine's (heat, a host, a scheduler) (Zooko, September 26, 2026). Where a platform gives no per-thread cycle counts, say so beside the result.

## Coding: integers first

Avoid floating point except where the domain is continuous by nature (pixel coordinates on a log axis). Time is discrete by nature here: every clock we can read counts ticks, so elapsed time, like counts, bytes, and ranks, is an integer (Zooko, September 26, 2026). Measurements, statistics, ratios, and thresholds are integers. Keep a measurement as measured (a sample is the nanoseconds the clock gave over the units they covered) and defer every lossy step: bench-hashes computes on times and ratios in fixed point with 64 fractional bits (its `Fixed`), where sums, differences, and comparisons are exact, and rounds once, where a person reads the value (permille for ratios and spreads, hundredths for opacities, three significant digits of nanoseconds). Round explicitly (`(a + b / 2) / b`) at the one place a division happens, and encapsulate the representation in a type whose methods do the rounding. Convert to `f64` at the last moment, for drawing only.

## Coding: Design By Contract

We document and `assert` every precondition our code relies on (`debug_assert` only on hot paths). Contracts are **expansive** (the caller carries the responsibility), **conceptually simple** (a few sentences of English; simplicity beats familiarity), and **structurally simple** to enforce (few lines, types, data elements, conditionals).

We never write "defensive code" — code that complicates a contract to ease the caller's life. When running code detects that a caller misunderstood the contract, it **fails stop**: panic with a clear message. Stopping is safer than proceeding, and it lets people fix the caller or loosen the contract. Defensive codebases grow buggier over time; DBC codebases stay predictable.

## Interfaces: fewest new concepts

A highly desirable property of an interface and its contract: the user learns the fewest new concepts. Zero new concepts earns a perfect score. Each new term (a resource unit, a sharing rule, a tuning knob) taxes working memory and needs a place in prediction and control. Prefer familiar concepts the caller already holds (threads, inputs, budgets), keep implementation units unnamed in public docs, and express observable behavior (speed, thread count, fairness beside concurrent calls) in those familiar terms.

# Audiences: three sets of documents

Each document serves one audience; keep it to that audience's needs.

1. **The servil team** (Zooko, and John Servil, his AI assistant; future sessions of both), who change these two repositories: this file, `PROCEDURES.md`, `NOTES-servil.md`, and bench-hashes' `AGENTS.md`, `PROCEDURES.md`, `NEXT-STEPS.md`, and `NOTES.md`. Everything we know, need, or decided goes here.
2. **People who run the benchmark or use the crate**: bench-hashes' `README.md` (how to run it, read the results, and share them; also the GitHub Pages home page), its `METHODOLOGY.md` (how it measures, for readers who investigate), the graph itself, and the servil preface of this repository's `README.md`. They need no development setup and none of our conventions.
3. **Other developer teams, human and AI**, who change the code and cooperate with us: `CONTRIBUTING.md` here and in bench-hashes. It holds the bare necessities (layout, build and test, the regression check, the rules that keep results comparable) and points at our notes without asking anyone to follow them.

A fact that concerns several audiences goes in each audience's document, phrased for it.

# Targets

**Virtual machines are first-class optimization targets.** People run BLAKE3 inside VMs like the Debian guest this repository is developed in, and its speed there matters as much as on the native Mac. A change is good when it helps both, or helps one and leaves the other level; a change that wins natively and loses in a VM (or the reverse) needs a decision on the record, not a default. VMs behave differently in ways that matter here: an idle vCPU that spins or calls `sched_yield` steals host time from the vCPUs that hash (natively a yielding poller costs 2%, in the VM 36%), and a 16-vCPU guest may sit on fewer fast host cores than it has vCPUs. `examples/host_lab.rs` measures each of these; run it on both and keep both reports.

# Where to start

Read `/workspace/bench-hashes/NEXT-STEPS.md` first: it says what the work is now (optimising this fork against the benchmark) and where the last session left both repositories. `NOTES-servil.md` holds the fork's design notes and the measurements behind each change. `PROCEDURES.md` holds how things are done here: the regression check, branches and promotion, releases, the Mac runner, probes, and the environment.

# Speed: no slower commit enters unnoticed

Speed is this fork's purpose. Every commit that touches code passes the performance-regression check before it enters git, and the main line takes only changes that passed it on every target machine; `PROCEDURES.md` gives the procedure and what each verdict obliges.
