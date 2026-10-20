# Procedures and environment

For the servil team: how things are done in this repository and its guest. The principles they serve are in `AGENTS.md`; bench-hashes' own procedures are in its `PROCEDURES.md`.

# The performance-regression check: every code commit

Speed is this fork's purpose, so no commit that makes it slower may enter git unnoticed. **Every commit that can change the machine code the gate's machines run (AArch64, on macOS and Linux) must pass `bench-hashes check` first.** The hook runs it for every commit touching `src/`, `c/`, `build.rs`, `Cargo.toml`, or `Cargo.lock`; a commit there that leaves that code as it was (code for other targets under `cfg`, tests, examples, comments) skips it with `git commit --no-verify` and a line in its message saying why. The check (bench-hashes' `src/check.rs`) builds the working tree and `HEAD` (`--against REV` for another commit) side by side, records once which lines of the fork each benchmark cell executes, measures the cells that execute a line the change touches (every cell for a change to assembly, the build script or a manifest, or with `--cells all`), each pair of runs with a fresh link layout, and judges them with `clocks::summary::discoveries`; there are no stored numbers and nothing to keep current, and any machine can run it. A comment-only change measures nothing; a change to the stream measures its cells, in minutes. The rule, its margins and pair count are bench-hashes' (`COMPARISONS.md`: their evidence, the alternatives tried, and the Mac calibration), and are changed there.

**Install the pre-commit hook once per checkout**, and the check runs by itself on every code commit:

- macOS host: `sh tools/install-git-hooks.sh`
- the Debian VM: `sh /workspace/blake3-servil/vm/setup.sh` (after every VM restart; the mount drops executable bits, so the guest's hook lives in `/tmp/git-hooks`)

**Run it by hand** when the hook is not installed or before pushing: `cd bench-hashes && cargo run --release -- check`. It measures the working tree, so commit with everything the commit contains in the tree (`git commit -a`, or stash unrelated edits first). Nothing else should run on the machine meanwhile, and on the VM nothing heavy on the host either.

**What each result obliges you to do:**

- *Exit 0, no regression:* commit.
- *Exit 1, a regression:* the hook aborts the commit. Do not commit around it. Find the cause and fix it, or, when the slowdown is the deliberate price of something worth more (correctness, simplicity with a measured cost), stop and ask the user; if they accept it, commit with `git commit --no-verify` and state the regressed cells, their numbers, and the user's decision in the commit message.
- *Exit 2, no verdict:* `clocks` found other programs keeping the machine busy during a run, or saw no load window. Stop whatever else is running and check again.

**Releases** follow the checklist in "Releases" below.

**eBASH, after each release** (once the submission is due: NOTES-servil.md, "eBASH"):
1. `sh supercop/make-tarball.sh vX.Y.Z+<commit>` pins SUPERCOP's `crypto_hash/blake3/rust_servil` to the release and writes its tarball into `supercop/`, in place of the last one; commit both and push.
2. `sh supercop/check.sh` runs the pinned crate through a fresh SUPERCOP tree, as eBASH does (a minute or more: ask for the host first), and reports its checksums and SUPERCOP's choice. Both must pass; the cycles count only from an idle machine.
3. Give Zooko the email below, to send to the eBATS list (subscribe first: an empty message to ebats-subscribe@list.cr.yp.to), with the tarball's URL at that commit. `supercop/README.md` says what the submission is; NOTES-servil.md, "eBASH", why and what is open.

```
To: ebats@list.cr.yp.to
Subject: BLAKE3: new implementation crypto_hash/blake3/rust_servil

Dan,

Please include https://raw.githubusercontent.com/johnservil/BLAKE3/<commit>/supercop/<tarball>
in SUPERCOP. It adds one implementation, crypto_hash/blake3/rust_servil,
and leaves the existing ones unchanged: the blake3-servil Rust crate,
pinned by its Cargo.lock and called as its users call it. The crate
picks its kernels at run time for each message length, so its timings
at every length are the ones its users get.

License CC0-1.0 OR Apache-2.0; copyright and patent level 0.

Zooko
```

The email and the tarball are all Dan reads: the submission succeeds when he adds it with one action, so it looks like the code already in SUPERCOP (its layout, file names and conventions), and anything that saves him no work stays in our notes.

**Commits that skipped the check** (`--no-verify`, or made where the hook was absent) must be checked before they are pushed: check out each in turn and run `check --against <its parent>`; for a run of them, also the last against the first, which sees slowdowns each step kept under the margin.

The check's Mac calibration (its false holds and sensitivity on the M4 Max) is in bench-hashes' `COMPARISONS.md`; the earlier rule's, which judged five fixed cells, is history in `NOTES-servil.md` ("The regression check, calibrated").

# Branches: candidates, then servil

`servil` is this fork's main line. Every commit on it has passed the whole gate below, on the VM and natively on the Mac.

Work happens on `candidate/<topic>` branches (`candidate/p-e-classification`, `candidate/workgroup-placement`). Their commits pass the pre-commit check on the machine where they are made, as every code commit does, and may be pushed before native measurement: that is how the Mac's benchmark runner, which builds from GitHub alone, gets them.

A candidate reaches `servil` only when all of these hold, and, if it changes compiled code, never without the performance check:

1. It is a fast-forward of `servil`'s current tip, so what was measured is exactly what lands. When `servil` has moved, rebase and check again.
2. Every test suite passes, judged by each suite's exit status (a failing test binary prints no `test result` line, so a list of result lines can hide it): the fork's default, and `pure` builds, the integration tests, the official vectors, the C API's (`capi/`), b3sum's, and the benchmark's own tests. `sh tools/check-builds.sh` passes on the VM: the builds the suites leave out (without std, tested; one CPU, tested; warnings as errors for the default and `pure` builds and b3sum; compile checks for x86-64), the failures GitHub's CI used to be the first to see (an unused import, `servil` 1352c21, October 5, 2026; the no_std and wasm32 builds of Devon's #26 and #33, October 15). Where the candidate changes code for other targets (x86-64, Windows, AArch64 without SME2 or SHA-3), GitHub's CI runs its tests there too: start the `tests` workflow by hand on the candidate (`workflow_dispatch`); it is the one place those targets run. Where the candidate changes the library's Rust, mutation testing passes on the change: `pypy3 tools/mutants/check.py --since servil` tests the mutants in the lines it changes (seconds to minutes) and fails on a new survivor; when the change removes or alters test code, it runs the whole set by itself (44 minutes), since that can weaken the tests of code the change leaves alone. Jobs of hours run overnight, while Zooko sleeps, on `servil` as it stands (Zooko, October 17: his waking hours are for work with him): the long proofs, the whole mutation run (`pypy3 tools/mutants/check.py`, which also catches stale entries and code a change made dead), and any other. A failure there is fixed forward first thing. The long proofs run after a change lands, not before it (Zooko, October 17: waiting half a day for them held every other change back while `servil` could not move): when a landed commit changes an AArch64 assembly kernel or the verify tools, `sh tools/verify/long-proofs.sh servil` runs them on the VM and posts the commit's GitHub status "long proofs" (the Lean specification and the proofs' definition, the hybrid kernels, the SME2 kernels at every group count, the instruction models against the CPU, and the proofs' mutants; hours, nothing measuring meanwhile). A failure is a regression, fixed forward first; the next change to a kernel or the verify tools waits until they pass.
3. `bench-hashes check --against servil` (in the candidate's checkout) reports no cell slower on the VM.
4. The same comparison reports no regression natively on the Mac.

**A candidate that changes no compiled code** (nothing in `src/`, `c/`, `build.rs`, `Cargo.toml`, or `Cargo.lock`: documents, workflows, proof and other tools) needs 1, 2, and CI alone (Zooko, October 14, 2026): its speed comparisons would compare identical code, and the host is rarely idle.

A regression the user accepts, as the section above describes, lands with the user's decision, the regressed cells, and their numbers in the merge's message (for a fast-forward, the promoted commit's message; amend the message only, leaving the measured tree unchanged). The user accepts such trades under this rule (September 25, 2026; revised September 27): every slowed cell stays ahead of every competitor, the gains outweigh the losses, and the user decides; a streaming API's cells may not slow to speed up another API (AGENTS.md, "The streaming APIs first"). A candidate waiting on the Mac waits on its branch; the VM's verdict alone does not promote it.

A promotion fast-forwards `servil` to the candidate, records the gate's evidence (suites, both verdicts, their job numbers) as a note on the tip (`git notes --ref=perf add`; push `servil` with `refs/notes/perf`), and deletes the candidate branch here and on GitHub. After a promotion, pin bench-hashes to the new tip (`cargo update -p blake3-servil` in bench-hashes, commit the `Cargo.lock`, push): that pin is what users measure, and records are made on it.

# Releases

A release is a commit everyone can stand behind: every check that the main line runs once per change, run once more on that exact commit, plus the user-facing pages rewritten for it. Each step names what does it. `pypy3 tools/release-check.py [COMMIT]` reads where each mechanical step left its result (CI, the long-proofs status, the runner's verdicts, the night's logs) and prints PASS, FAIL, or OPEN with the command that makes the evidence; it runs nothing heavy itself, so it can be run at any time of day.

**What goes in.** Agree with Zooko which open candidates, PRs and issues the release takes, and record the list in the release's tracking issue (one issue, its checklist ticked as each item lands). Every candidate lands through the main line's gate (above). A release blocks on every open issue labelled for it.

**The release commit.** Once everything is in, these run on `servil`'s tip, each recorded in the tracking issue:

1. CI, every job, by `workflow_dispatch` on the tip.
2. `sh tools/check-builds.sh`: every build variant.
3. `bench-hashes check --against <previous release tag> --cells all`, on the VM and as a Mac `check` job. Each commit is checked only against its parent, so slowdowns too small to flag one at a time could add up; this check sees their sum.
4. The long proofs (`long-proofs.yml`, or `tools/verify/long-proofs.sh`), every kernel.
5. The full mutation run (`pypy3 tools/mutants/check.py`): every survivor known and explained.
6. `cargo publish --dry-run` in the root, and in `b3sum/`: the packages build from what they contain.

**The pages users read**, rewritten for the release and read as a newcomer would (AGENTS.md, "write each page for a reader who holds only the page"):
- `README.md`: the servil preface;
- `QUALITY.md`: the overview of what is proved, tested, and open; `docs/quality-manual.md`: every check and how to run it;
- `CHANGELOG.md`: what changed for users since the last release, in their terms;
- the supported-platforms table: exactly what CI runs.

**Benchmark results.** A full bench-hashes run on the release commit, on the Mac (and on any other machine whose owner offers one), published to bench-hashes' GitHub Pages with the release named on the map.

**Version and tag.** `sh tools/gen-ver.sh X.Y.Z` from a clean tree: one commit on top of HEAD setting the version to X.Y.Z+<HEAD's hash> (b3sum's requirement and lock with it), and the tag vX.Y.Z+<hash> on it. The hash in the version string names the code commit, so a holder of the string alone can check they have the right code.

**What users download.**
- `cargo publish` in the root, then in `b3sum/` (the library on crates.io; `cargo install` builds b3sum on the user's machine).
- b3sum's release binaries, from a clean tree at the tag, on each machine: `sh tools/b3sum-release.sh`. On Linux this links statically, the recommended build; on the Mac, as macOS links. Attach each `dist/b3sum-VERSION-TARGET`, with its `.sha256` and `.b3`, to the tag's GitHub release.
- The C library: `cargo build --release` in `capi/`. Attach `libb3_servil.a`, the shared library, and `b3.h`.
- The GitHub release's text: the CHANGELOG entry.

**Afterwards.**
- eBASH: the steps below, pinned to the new tag.
- The night's checks resume on the main line.
- The tracking issue closes, with links to the release and the published results.

# Before a question goes to Zooko

Before a change or a question goes on Zooko's decision list, ask whether it adds to or rescues a second mechanism for a problem the design already solves (AGENTS.md, "Revisit complexity as you learn"). If it does, settle first which mechanism stays: make the first serve, or remove the second.

# The Mac

`tools/runner/README.md` describes the runner. Zooko starts it with `sh ~/piplayground/blake3-servil/blake3-servil/tools/runner/setup-mac.sh` (again after a change to `runner.py`, which it installs). Write `runner/jobs/NNN-name.json` naming pushed commits; wait with `pypy3 tools/runner/wait_for.py NNN-name`; results land in `runner/results/`. A job runs once per file name, so a changed job takes a new number. Keep the VM idle while a Mac job runs, Activity Monitor closed (it keeps `sysmond` near a whole CPU busy: with it open, 170 of 219 load windows of a 4-run benchmark read busy, closed 5 of 214; jobs 1567, 1572, October 17), and the Mac on mains power: on battery it runs more calls that follow a pause on the efficiency cores (233 of 400 against 32; jobs 351, 357), and every job's `verdict.json` records the power state at its start and end (`power at start`, `power at end`); read them before trusting a job. A direct A/B is four `benchmark` jobs, old new new old, back to back, read with `bench-hashes compare` (the old jobs' samples files, `--`, the new jobs'; and each side against itself, for what repetition alone moves); a calibration is one `benchmark` job with `"repeat": N`. Mac-only measurements (cycles by core kind, QoS) go in a `probe/<topic>` branch that adds its own `examples/host_lab.rs` (NOTES-servil.md, "Probes on the Mac"); a probe's branch becomes a tag of the same name once its finding is in the NOTES (`probe/*` and `archive/*` tags keep every probe of the fork's history, each cited where its finding is).

# Probes

Every clock read, in the fork, in bench-hashes, and in any scratch probe, goes through the `clocks/` crate in this repository (AGENTS.md, "Measuring"): `clocks::measure(batches, batch_ns, || ...)` for a probe's batches (each batch's wall time and the thread's counts per core kind, shown as ns per call and the clock it ran at), `clocks::measure_after_gaps_prepared(calls, gap, gap_ns, input, prepare, call)` for calls that must each come after a gap (`clocks::Gap::Idle`, a sleep, or `clocks::Gap::Busy(work)`, a fixed other program and a walk of `work`; each call timed alone and summed, since a call of a few clock ticks cannot be timed alone: the crate's "Resolution"), `clocks::now()` and `clocks::since_ns()` for wall time alone, `clocks::Counts::read()` for the counts. The fork's examples have it as a dev-dependency; a scratch crate adds `clocks = { path = "/workspace/blake3-servil/clocks" }`. Its documentation says which clocks and why (github.com/johnservil/measure-clocks3, `CPU-TIME-CLOCKS-AND-FREQUENCY.md`, has the experiments). The pool's pacing in `src/lanes.rs` reads `Instant` directly: control, not measurement, and the library depends on nothing.

Two probes need no quiet machine, because they count instead of time, and they guide designs for cores we have no machine for:
- `sh tools/insn_count/count.sh x86_64|aarch64 CPU LEN...`: instructions per `hash()` call, the fork's and upstream's, under qemu (CPU a qemu model: eBASH's Arm cores are cortex-a53, cortex-a72, cortex-a76, neoverse-n1); `tools/insn_count/one_call.py` splits one call's by function. Exact and repeatable, so it compares two builds while the host is busy.
- `sh tools/mca/model.sh OBJECT LABEL...`: LLVM 19's llvm-mca cycles per pass of a loop or function on the Cortex-A53, A57 (for the A72) and Neoverse N1 (for the A76) models.

A count or a model is reported as such, never as a measurement, and never replaces the check's verdict.

# The check and older commits

The benchmark calls the current fork API; a commit that predates it fails to build, and is compared with the tools of its own time (AGENTS.md, "Contracts change everywhere at once"). A release check is against the previous release tag, every cell (`check --against <tag> --cells all`). To run the benchmark by hand against the working tree, `cd bench-hashes && cargo run --release -- build-against ..` builds it in a directory of its own and prints the executable's path.

# Environment

## Where things are

- `/workspace` is the host folder mounted through sandboxfs, and this fork is checked out at `/workspace/blake3-servil` (github.com/johnservil/BLAKE3, main branch `servil`, work on `candidate/<topic>` branches). It persists across VM restarts.
- `/workspace/blake3-servil/bench-hashes` is the benchmark's own repository (github.com/johnservil/bench-hashes, branch `main`), nested inside the fork. It depends on the fork by git (`servil` branch) at the commit its `Cargo.lock` pins, so a user's `cargo run --release` measures that commit. To build it against this checkout's working tree, run `cargo run --release -- build-against ..` in it: it builds in a directory of its own (the bench's sources copied beside the fork, its own `Cargo.lock`, the fork and `clocks` patched to paths) and prints the executable's path; nothing tracked changes, and Cargo rebuilds only what changed. `/workspace/blake3-servil/.git/info/exclude` keeps it, `benchmark-results/`, `tmp/`, `vm/`, and the token out of the fork's status.
- `/workspace/blake3-servil/vm/` holds everything the guest needs that a restart would otherwise remove:
  - `vm/home/` is `HOME` for `git` and `cargo`: `.gitconfig` with `safe.directory = *`, John Servil's `user.name`/`user.email`, and the credential helper.
  - `vm/home/bin/gh-cred.sh` speaks the git credential protocol and reads the johnservil classic token from `/workspace/blake3-servil/ghtokenclassic.txt` (never print that file). Both repos have `credential.helper = !sh /workspace/blake3-servil/vm/home/bin/gh-cred.sh` (the mount drops executable bits, hence `!sh`).
  - `vm/setup.sh` installs `clang-19` from apt.llvm.org, and `pypy3` and `librsvg2-bin` from Debian, when they are absent; creates `/tmp/target`; configures git and cargo for every shell of the boot (below); re-points both repos' credential helpers; and installs the guest's pre-commit hook in `/tmp/git-hooks`. Run `sh /workspace/blake3-servil/vm/setup.sh` first after a VM restart.
- Guest disk (`/tmp`, `/usr`, apt packages) vanishes with the VM. Only `/workspace` persists.
- So everything that cannot be rebuilt lives under `/workspace`: worktrees (in `tmp/wt-*`, which git ignores), uncommitted work, logs, and results. Builds and caches stay on `/tmp`, and so must anything executed (the mount drops executable bits): `CARGO_TARGET_DIR` (the VM's cargo config sets `/tmp/target`) keeps the check's and `build-against`'s builds there too. Commit work in progress at each step (a restart on October 17 wiped an uncommitted worktree in `/tmp`).

## Building and running

- Use `pypy3` for every Python tool, the proofs in `tools/verify/` among them (Debian's pypy3 reads the `python3-z3` package). One interpreter is the simpler rule (Zooko, October 12, 2026); per tool, CPython is faster where time goes into libz3 (prove_hybrid k10: 178 s against pypy3's 233 s) and pypy3 where it goes into the executor. C2SP's submitted scripts keep `python3` for portability.
- The VM is Debian 12 on AArch64 with 16 vCPUs (inspect `nproc` after a restart). Its CPU exposes SME2 with 512-bit streaming vectors (`/proc/cpuinfo` lists `sme2`), so the fork's kernels run here. Absolute timings differ from Apple hardware; relative comparisons hold.
- The fork's SME2 kernel is `c/blake3_sme2_aarch64.S`, compiled by the `cc` crate with `-march=armv9-a+sme2`. The system `cc` (GCC 12) and `as` (binutils 2.40) predate SME2, so under them the fork builds without the SME2 kernel and warns (the user's decision, September 25, 2026, for Debian 12 and Raspberry Pi OS users); every VM build takes `CC=clang-19`, which assembles SME2, and the check fails stop when a build on an SME2 machine lacks the kernel; `TMPDIR` gives clang a temporary directory that exists in the guest.
- `vm/setup.sh` configures the guest system for the whole boot, so every `git` and `cargo` command runs as it is: `/etc/gitconfig` includes `vm/home/.gitconfig` (whose `safe.directory` covers the mount's files, which show as uid 501 while the guest runs as uid 0), `$CARGO_HOME/config.toml` sets the target directory and `CC=clang-19`, and the Mac's `HOME`, which the guest's shells inherit, is created in the guest, and its `TMPDIR` is a link into the tmpfs (`/tmp/mac-tmpdir`), so every tool's temporary files stay off the small root filesystem.
- Build the fork: `cargo build --release`
- Test the fork: `cargo test --release` (add `` or `--features pure` for the other platform paths), and the official published vectors with `--manifest-path /workspace/blake3-servil/test_vectors/Cargo.toml`, all with the same environment prefix.
- Run the benchmark from `/workspace/blake3-servil/bench-hashes`, since it writes `benchmark-results/` relative to the current directory: `cd /workspace/blake3-servil/bench-hashes && cargo run --release -- --quick --contenders blake3-official,blake3-servil-st` measures the pinned fork commit; `$(cargo run --release -- build-against ..) --quick ...`, run from a scratch directory, measures the working tree. A full run is the default; `--quick` takes seconds.
- `CARGO_TARGET_DIR=/tmp/target` is a tmpfs build cache (rebuilt after a restart); `CARGO_HOME=/usr/local/cargo`. The toolchain is rustc 1.98.1 without the `rustfmt` component, so there is no formatting check in the guest.
- Commands for the user go on one line, with no `\` continuations.
- Never `sleep` in commands.
- Run long commands (builds, benchmark runs, package installs) without a timeout and let their output stream, so the user can watch progress and interrupt when they choose.
