# Devon's x86 assurance candidate

Intel i7-12700K, Linux, Rust 1.98.1, generic builds. Work starts from
John Servil's `8825450` candidate; ARM64/SME2 and Mac remain untested here.
The preserved review checkout remains at `3d02b04`.

## Queue execution capacity

The published benchmark audit reproduced the one-CPU queue hang. John
addressed it in `2cc0c00`, crediting that report. Independent review
confirms its criterion: the initialized pool has `cpus - 1` workers and
possibly an SME2 thread, so tasks are executable iff `cpus > 1 || sme2`.
Queues with no executor hash at delivery, retaining modes and order.

An independent equivalent fix passed default/pure tests and the x86
regression check before the upstream fix was discovered. Its patch and
logs remain outside the repo in `bench-hashes-validation/`; this candidate
adopts John's simpler boolean design and adds a supplemental assurance
check. The entire API suite runs in a fresh process restricted to the
first allowed Linux CPU, covering every mode, every shape, resubmission,
concurrent submitters and paused bursts. A 30-second parent deadline
bounds the child. This supplements the upstream one-CPU shape test.

Default tests pass with the upstream fix (77 library, 16 API including the
nested 15-test restricted suite, 1 one-CPU and 1 allocation test). The
supplemental test/dependency change passes `tools/perf_regress.py check`:
eight alternating pairs, initial slower cells dismissed by confirmation,
no confirmed regression. This diagnostic tool deletes temporary raw
samples; its full stdout/stderr logs are retained locally. Optimization
claims use separately retained raw old/new/new/old data and repeat controls.

## Two-chunk batch optimization

`83e7e74` batches 2048-byte x86 messages across existing SIMD kernels.
[The public evidence](devon-results/two-chunk-x86/README.md) establishes
roughly 2.0-2.1x throughput on a P core/default affinity and 1.75-1.78x
on an E core for batches of eight or more. Default/pure suites, published
vectors, independent alignment/mode tests, concurrency, guard pages and
ASan support correctness; TSan cannot start in this environment.

The candidate stays under review: retained frozen-workload runs show
slower queue cells (+7-16%) and variable after-idle cells despite passing
the diagnostic regression tool. Same-code build/repeat controls demonstrate
sensitivity; the observed costs remain open before promotion. The linked
record preserves these findings beside the target gain.

## Measurement scope

The instrument is Devon's audited bench-hashes at `bd3acd0`, with current
fork clocks shared across sides. Its workload-specific gate permits solo
comparisons while excluding correlated shared bootstrap bands from
inferential verdicts. Linux thread cycle counts are unavailable. Every
potentially hanging command uses an external process-group deadline.
Mac cold-code/layout variability remains open upstream; no cross-machine
regression-free or energy claim follows from this x86 work.
