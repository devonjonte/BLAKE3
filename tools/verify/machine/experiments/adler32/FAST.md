# Faster Adler-32 with a machine proof: active experiment

Goal: beat the strongest known implementations on the declared CPUs/workloads,
while keeping the seed-one contract and a checked theorem for the exact Ode code.
Tracker: https://github.com/servil-software-factory/BLAKE3/issues/377

The original 171-byte Ode implementation remains proved. **The optimized whole
checksum and its machine theorem remain open.** `raw4096.ode` is an assembled,
UNVERIFIED block-kernel hypothesis; executable validation and timing are recorded
with each candidate source pin.
`probe.c` is explicitly unverified native C, adapted
from the MIT-licensed libdeflate striped-VNNI algorithm to decide which design
would earn the work needed in Ode and its machine model.

## First probe, declared before collection

Hypotheses:
- Wider reduction intervals may reduce overhead. Keep lane counters bounded,
  then widen horizontal sums to 64 bits; normalize every 16384 bytes.
- A single accumulated prefix sum may replace four, with the same four additions
  per iteration, fewer live registers and less work combining the final sums.

Four probes: 256/512-bit vectors, each with one/four prefix accumulators. All use
16384-byte chunks and the same caller contract. Compile at -O3 without LTO, with
AVX-512 BW/VL/VNNI/DQ available. Keep the native libdeflate and zlib-ng dispatchers.
The extended contender set adds **ISA-L 2.32.1**, commit
`7c3479e0a9dac17f448603ec1ad64c7c625f530c`, its ordinary `isal_adler32` entry.

Use the existing adapter and clocks rules. Preparation requires the explicit
`--skip-proof` flag to include these probes; reports mark them UNVERIFIED. It also
needs NASM for ISA-L. Default preparation still admits only the proved Ode baseline
and the three earlier native libraries. `--validate` exercises every included
engine on fixed/reference inputs and read-only input against both guard edges.
A deliberate one-byte-overread mode must fault, so the guards show they can fail.

Cheap collection: `--probe ENGINE` takes 16 cells: deterministic random bytes at
0,1,16,64,256,4096,65536,1048576 bytes, aligned or offset by one. Other patterns and
reduction boundaries are validated before timing. Full `--collect ENGINE` retains
the 80-cell workload. Each current v3 sample file declares which workload it holds;
the reader requires exactly that cell set. Probe batches request 20 ms; full-workload
batches keep 5 ms. Calibration checks the clock after each call, so tiny checksums
produce shorter measured batches than that nominal budget. Require an observed
quiet load window; initial shorter-budget attempts correctly abstained and remain
in the evidence. Historical v2 data uses its pinned reader.

On EPYC 9275F and Xeon 6330: compare libdeflate against each of zlib-ng, ISA-L and
the four probes. Three paired runs per question, paddings 0,256,1024, alternating
order, competitor order rotated. Add three libdeflate/libdeflate pairs. Build all
binaries before timing. Use clocks' existing 5% FDR/3% margin over each question's
16 cells; report all times, ranges and missing counters. Busy pairs get at most
two whole-pair retries, with every attempt preserved. This is candidate selection,
not a claim to beat every implementation or a substitute for the full workload.

Promote a design only after inspecting its regressions and the native leaders.
An Ode implementation then needs its generated machine proof and the full paired
comparison, plus real libdeflate integration measurements. Instruction semantics
and proof assumptions remain explicit. The current x86 model's vector state is
128 bits; wide-vector/VNNI/mask support needs coordinated work with Sam. Her
current recommendation grows `wide/Wide.lean` for kernels, then unifies it with
the word-level model. Conditional caller proofs can already expose the kernel
contract as a visible theorem hypothesis.

## Targeted follow-up, declared November 13 before collection

Separate vector-width policy from algorithm gains. Libdeflate prefers its 256-bit
kernel on Ice Lake. Expose its existing `adler32_x86_avx512_vl512_vnni` and
`adler32_impl` symbols in a **copy** of the built static archive. Verify every
archive member's section contents, section headers and relocations unchanged.
Bind the copy privately; keep the ordinary public dispatcher as `libdeflate`
and name the direct existing kernel `libdeflate512`. Record the actual selected
pointer after validation, beside the 512-bit kernel pointer and symbol listing.
The forced-width control retains libdeflate's release flags (normally -O2).

Complete the preserved `REDUCE32` probe as `probe512-r32`: four prefix sums,
512-bit vectors, 16 KiB blocks, u32 reduction of A; u32 reduction of B only when
the block has at most 5552 bytes. Larger B sums retain the widened reduction.
Compare it with the unchanged `probe512` (-O3 for both). All native probes
remain UNVERIFIED. Before timing: fixed/reference vectors, all small lengths
0–257 at every byte alignment, all byte-mask tails against both read-only guard
edges, reduction boundaries, and a deliberate overread that must fault.

On both declared CPUs use four paired layouts (padding 0/256/1024/2048),
alternating order and rotating questions. Retain the 16-cell random probe
workload and 20 ms requested batches. Questions (old → new):

1. `libdeflate` → `libdeflate512` (existing width policy).
2. `libdeflate512` → `probe512` (same width, combined algorithm/compiler effects).
3. `libdeflate512` → `probe512-r32` (same width, new reductions).
4. `probe512` → `probe512-r32` (reduction change with matched flags).
5. `libdeflate` → `libdeflate` (same-code control).
6. `libdeflate512` → `libdeflate512` (same-code width control).

Judge each question's 16 cells together using the shared rule. Retain every
attempt; busy or missing-load pairs abstain, with at most two whole-pair retries.
Inspect all small-cell costs before choosing an Ode design. Sampling and flags
stay explicit; a native result supplies candidate evidence, separate from a
machine theorem. A fixed 4 KiB straight-line block kernel may simplify the proof
boundary. `raw4096.ode` now assembles through the existing source-kernel machinery;
its two printers agree. Mathematical raw/update bounds check in `Block_adler32`.
See `WIDE-FORMS.md` for exact assembled forms and open proof/image obligations.

## Alignment and raw-block probe, declared November 13 before collection

Two new UNVERIFIED implementations, sharing one alignment policy (`align.h`):

- `probe512-align` retains `probe512-r32`'s algorithm and reductions, adding a
  scalar byte peel to 64-byte alignment only when the original length exceeds
  65536. The peel starts at seed one and reads at most 63 bytes.
- `probe4096` calls the straight-line Ode `raw4096` kernel for complete 4096-byte
  blocks. Its C caller uses u32 modular reductions and the checked block law;
  remaining bytes use the existing `probe512-r32`, composed with the seed-one
  append formula. Small inputs tail-call that existing implementation. This
  combines unrolling, a kernel call and more frequent reductions; their complete
  caller cost is the question. The shared alignment peel applies above 65536.

Preparation verifies the generated assembly against Ode's existing printer.
It admits both new implementations only with explicit `--skip-proof`. Reports
pin the source, generated assembly, printer, C glue and actual build flags.
Native C probes remain -O3; libdeflate retains release defaults (-O2).

Before timing: existing fixed/reference/all-small/all-alignment/guard cases,
raw zero/one/255/ramp anchors, direct random weighted sums at every alignment,
4095/4096/4097 and 8191/8192/8193 boundaries, alignment threshold
65535/65536/65537/65600 at all 64 alignments, and canonical A=0 across a block
and a seed-one tail. Guard input stays read-only. A planted raw weighted-shift
fault must fail a fixed anchor; a one-byte overread must fault. Earlier five
native probe objects must retain their section bytes, headers and relocations.

Both declared CPUs, four paired layouts (0/256/1024/2048), 16-cell random probe,
20 ms requested batches; alternating pair order, rotating questions. Questions
(old → new):

1. `probe512-r32` → `probe512-align` (alignment policy, matched algorithm/flags).
2. `libdeflate512` → `probe512-align` (matched-width implementation).
3. `libdeflate` → `probe512-align` (public dispatcher).
4. `probe512-align` → `probe4096` (fixed-block kernel/caller design).
5. `libdeflate512` → `probe4096` (matched-width implementation).
6. `libdeflate` → `probe4096` (public dispatcher).
7. `libdeflate512` → `libdeflate512` (same-code control).
8. `probe512-align` → `probe512-align` (new same-code control).

Judge all 16 cells per question with the unchanged shared rule. Preserve all
attempts, including busy/unobserved abstentions; permit at most two whole-pair
retries. Inspect every small/unaligned cost. Neither a native pass nor the
checked natural-number bounds establish the optimized machine theorem. Full
80-cell, real integration and adverse/cold/after-work measurements remain later
gates for a promising, proved design.
