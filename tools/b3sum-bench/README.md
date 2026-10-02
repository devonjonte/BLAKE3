# b3sum-bench

How long `b3sum` takes to hash files, from its start to its exit: the time
a person who runs it waits. It runs builds of `b3sum`, and its ways of
reading files, side by side on the same files, and writes a report to read
and a samples file to share and compare.

## Run it

From the fork's checkout, on Linux, macOS, or Windows:

    cd tools/b3sum-bench
    cargo build --release
    CONTENDERS=$(sh build-contenders.sh /tmp/b3c HEAD)
    ./target/release/b3sum-bench --files ~/b3sum-bench-files $CONTENDERS

A contender is `NAME=COMMAND`: a `b3sum` and its flags, the files appended
to it. `build-contenders.sh DIR COMMIT...` builds official BLAKE3's
`b3sum` 1.8.2 and this fork's at each commit, and prints their arguments.
Add your own, such as `read="/tmp/b3c/b3sum-abc1234 --no-mmap"`. The first
contender is the one the others are compared with.

`--files DIR` chooses where the input files live: put them on the storage
you care about. They are made once (1.3 GiB) and kept. `--quick` runs a
smaller set in seconds, as a check. Keep the machine otherwise idle while
it runs: the report says whether other programs kept it busy.

## What it measures

**Inputs.** Single files of 4 KiB, 64 KiB, 1 MiB, 16 MiB, 256 MiB, and
1 GiB, and a tree of 1000 files of 16 KiB passed together, as `b3sum
$(find src -type f)` passes them. The files' bytes are SplitMix64 output
(state `0x623373756d62656e ^ length.rotate_left(17) ^ index`, index 0 for
single files and 1-1000 for the tree), little-endian words; any machine
makes the same files.

**Page cache.** *Warm*: the files were read moments before, as when you
hash what you just wrote or downloaded. *Cold*: each file is evicted from
the page cache before each run, as when you hash files untouched since the
machine started: Linux with `posix_fadvise(DONTNEED)`, macOS with
`msync(MS_INVALIDATE)`, both without root. The report checks every cold
run's reads from storage and names any cell the page cache still served.
Cold runs are skipped on Windows and on filesystems kept in memory (tmpfs).
In a virtual machine the host's own cache may serve a guest's cold reads.

**Rounds.** Every contender runs once on every input, untimed, then 15
rounds of each (5 with `--quick`); in each round the contenders' order
rotates, so drift and each run's after-effects fall on all of them.

**Each run** is one new process, timed from just before it starts to its
exit, with the counts the operating system keeps for it: CPU time (all
threads), peak memory, bytes read from storage, and major page faults
(Linux and macOS), and on macOS cycles and instructions on performance and
efficiency cores. Peak memory counts a mapped file's pages: a 1 GiB file
hashed through a mapping shows about 1 GiB.

**Summaries.** A cell can run at two speeds (threads placed one way or
another, a clock that rose or did not); a single median would land on
either by chance. Each cell shows its speeds' medians and shares, and
`xN` compares fast speed with fast speed. Rates are bytes over wall time.

## Read it, share it, compare

`b3sum-bench-results/b3sum-bench.report.txt` holds the tables;
`b3sum-bench.samples.tsv` every run, with the machine, the filesystem, and
each contender's command, `--version`, and executable digest (BLAKE3), so
others can see exactly what ran. To compare two runs, or many of each:

    b3sum-bench compare OLD.samples.tsv... -- NEW.samples.tsv...

prints each cell's speeds side by side. A comparison says so when other
programs kept a CPU or more busy during either side's runs: such numbers
are no evidence of speed.
