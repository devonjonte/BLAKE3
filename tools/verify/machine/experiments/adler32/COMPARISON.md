# Adler-32 native comparison: declared procedure

Question: what do callers pay for the proved Ode checksum versus current stable
zlib, zlib-ng and libdeflate, using their ordinary native entry points?

## Frozen inputs

| Implementation | Release | Commit |
|---|---|---|
| Ode original, 171 bytes, proved | experiment | `2aa3d245305b494143223b341e564642a4eb2d20` |
| zlib | 1.4 | `99623ef7097352da7993ba614161fd6a311e046e` |
| zlib-ng | 2.3.3 | `12731092979c6d07f42da27da673a9f6c7b13586` |
| libdeflate | 1.26 | `92e6a0db9fa848d742f9eb286c92afc60f2c3dda` |
| clocks | bench-hashes | `5f99f456951ab36f7201decd8aa5e0249ec67bd1` |

The three library tags were the latest stable GitHub releases when this question
was declared. Build each with its CMake Release defaults, static libraries and no
LTO. Keep optimized implementations and runtime dispatch enabled. zlib-ng uses its
native API, with `WITH_NATIVE_INSTRUCTIONS=OFF` and runtime CPU detection on.
libdeflate recommends its default `-O2`; zlib and zlib-ng use their Release flags.
Preserve the actual compiler, flags, configuration and selected dispatch targets.

Each engine has an out-of-line Rust adapter with the same signature, taking a
pointer and length and returning u32. Each timed call goes through the same
indirect function-pointer boundary. Library adapters supply initial checksum 1.
There is no allocation, Python, dynamic loading, correctness comparison, or
per-engine dispatch in the timed loop. Public library entry/dispatch overhead and
adapter argument setup remain part of the measurement; no overhead is subtracted.
All libraries and all engines are linked in each executable, with LTO off.

Ode's linked bytes must equal the observed, proved object's bytes before any call.
All engines must pass fixed vectors and an independent scalar reference at
boundary lengths, four byte patterns and both alignments before collection.

## Workload and collection

Scope: one thread pinned to the same CPU, warmed, repeated one-shot checksum calls
on a prepared buffer, consuming each result. Lengths: 0, 1, 16, 64, 256, 1024, 4096,
5552, 65536 and 1048576 bytes. Patterns: all zero, all 255, sequential byte values,
and deterministic xorshift bytes. Addresses are 64-byte aligned or offset by one
byte: 80 cells per head-to-head question. The empty input has a nonnull pointer.

Each cell records 12 batches targeted at 5 ms through the unchanged shared clocks
library. Save wall time, calls, process CPU time, available thread cycles and
instructions, and load windows. Make absent counters explicit. Timing requires a
measurement machine and its exclusive bench-turn. All compilation finishes first.

For each competitor, take four Ode/competitor pairs, with explicit pre-Ode text
padding 0, 256, 1024 and 2048 bytes. Alternate which engine runs first. Rotate the
competitor order across rounds. Each pair is back-to-back. Add four Ode/Ode pairs,
one per layout. Use a single executable per layout for every engine, so the same
Ode image serves that layout's comparisons and controls. Preserve linked addresses
and disassembly, including the common adapters. ASLR stays at its normal setting.

A busy or unobserved run yields no verdict. Retry the complete pair at most twice,
preserving every attempt. After three attempts, stop the question with its partial
evidence. Never retry individual samples or cells to improve an answer.

## Analysis and limits

The Rust reader requires the current `ode-adler-samples-v2` contract. Historical
pilot samples retain their source-matched reader in their original commit.

Each run's cost is total wall time divided by total calls. Compare four pairs
using clocks' existing paired log-ratio test, 5% false-discovery rate over all 80
cells of that competitor/machine question, and 3% practical margin. Treat the
three competitor questions and the two machines separately. Same-code changes
remain findings to investigate before claiming a reliable comparison.

Print medians of the four per-run means, decimal GB/s, the paired comparison ratio
and verdict, and the minimum/maximum of the four paired Ode/competitor time ratios.
`median_old_new_milli` is the ratio of the displayed medians multiplied by 1000;
`pair_old_new_{min,max}_milli` give the paired range at the same scale. The judged
ratio is the geometric mean of the pairs' competitor/Ode ratios. Preserve raw
values and round only for display. Decimal places describe formatting, not a
confidence bound. Level means the rule found no qualifying change.

This measures warmed buffer calls, not cold calls, streaming updates, concurrent
callers, decompression throughput, or every CPU. Record environment limitations
and any missing cycle evidence beside the results. The compact Ode variant has a
different object and remains outside this proved-baseline comparison.
