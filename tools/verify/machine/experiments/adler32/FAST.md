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

[Delivered result at `dd83b8e4`](https://github.com/devonjonte/bench-hashes/tree/data/2026-11-13/ode-adler32-alignment-raw4096):
128 quiet runs; both controls level on each CPU. The alignment peel fixes the
old offset-one Xeon 1 MiB cost. The fixed-block caller is level with LF512 at
4 KiB and loses several bulk cells; 16-byte costs remain in both designs.
Next isolate normalization frequency and tiny entry layout before choosing the
kernel to prove. Sam's explicit assumed-contract caller machinery is merged;
its use must keep the missing wide-kernel theorem visible. Static-image/read-only
overlap needs her contract decision (`WIDE-FORMS.md`).

## Caller costs and seed-one small calls, declared before collection

Three separate UNVERIFIED candidates keep the same input/seed contract:

- `probe4096-batch` changes the raw C caller's normalization frequency alone.
  Four raw4096 calls compose one 16 KiB update; A fits u32, B stays below 2^36
  and uses u64 until reduction. Remaining complete 4 KiB blocks retain the old
  reductions. The generated raw kernel stays identical.
- `probe4096-entry` changes entry layout alone: a small outer function tail-calls
  r32 for inputs below4096; the noinline large body keeps old reductions. This
  separates the observed six-register tiny prologue from kernel work.
- `probe512-small` adds a seed-one small path to the aligned probe. At most64 B
  use one exact masked vector. A needs no reduction; B needs none through22 B,
  the largest all-255 reduction-free length. Above64 B keep the aligned design.

Validate all16 engines before collection. Extend all-alignment tests through
16383/16384/16385 and32767/32768/32769; exercise canonical-zero sums after16 KiB,
read-only guards, and independent fixed all-255 checks at22/23 B. Plant a u32
truncation of the batched weighted sum and a wrong small-reduction threshold;
both must fail. Existing objects must retain their sections/headers/relocations.
Check mathematical update16384/seed22 bounds independently of machine behavior.

Both CPUs, four paired layouts (0/256/1024/2048), alternating sides and rotated
question order. Same v3 16-cell random probe,20 ms nominal batches, shared clocks
and judgment. Questions (old → new), all16 cells judged together per question:

1. `probe4096` → `probe4096-batch` (normalization frequency).
2. `probe4096` → `probe4096-entry` (entry layout).
3. `probe512-align` → `probe512-small` (seed-one small path).
4. `libdeflate512` → `probe4096-batch` (matched width).
5. `libdeflate512` → `probe512-small` (matched width).
6. `libdeflate` → `probe4096-batch` (public default).
7. `libdeflate` → `probe512-small` (public default).
8. `libdeflate512` → `libdeflate512` (same-code control).
9. `probe4096` → `probe4096` (raw caller same-code control).

Preserve busy/unobserved attempts; permit at most two whole-pair retries. All
small/unaligned cells stay visible. Separate candidate effects before combining
them. Neither these execution tests nor the natural-number bounds establish an
optimized machine theorem. Static-image and wide-model work still follow the
choice of a promising implementation.

## Cleanup placement and shared bulk, declared before collection

The caller/small experiment at4d519c5d leaves every batch-four versus old-raw
cell Level on both CPUs. Small specialization helps Xeon16/64 B, while EPYC's
16 B remains slightly slower than LF512 and offset-one4KiB becomes slower.
Two diagnostic changes follow those concrete findings:

- `probe4096-cleanup` moves `vzeroupper` from every raw block's return to the
  whole checksum's exit. The private word-only caller uses a derived Ode kernel
  with that instruction alone omitted (308 instructions/1898 B). Same per4096
  reductions, tails and peel. Preparation compares the two generated assemblies;
  inspection must find word-only code between calls and one final cleanup.
- `probe512-dispatch` keeps the seed-one small path and tail-calls the original,
  unchanged `probe512-align` body above64 B. This isolates the compiler's changed
  bulk body from the small source specialization; extra dispatch cost stays visible.

Both remain UNVERIFIED. The original kernel's emitted bytes and every earlier
native object must remain identical. Validate both raw packed returns directly,
all18 checksum engines, all small/critical alignments and read-only guards. A
wrong dispatched length must fail; restore and validate again. Record both linked
kernel bodies/tables and actual generated source/assembly. Cleanup placement's
performance belongs to this experiment; functional examples establish their own scope.

Both CPUs, four layouts, same16-cell v3 probe/20 ms requested batches and shared
judgment; alternating sides and rotating questions. Old → new:

1. `probe4096` → `probe4096-cleanup`.
2. `probe512-small` → `probe512-dispatch`.
3. `libdeflate512` → `probe4096-cleanup`.
4. `libdeflate512` → `probe512-dispatch`.
5. `libdeflate` → `probe4096-cleanup`.
6. `libdeflate` → `probe512-dispatch`.
7. `libdeflate512` → `libdeflate512` (same-code control).
8. `probe4096` → `probe4096` (same-code control).

Retain all cells and failed attempts, at most two whole-pair retries for load.
A winner still needs a checked optimized machine theorem, full matrix and real
caller/adverse/cold evidence. The arithmetic reduction for a later Ode caller is
checked separately in `WordReduce_adler32`: two16-bit folds and one conditional
subtraction reduce every value below2^36, with Lean's three standard axioms only.

## Compact fixed-count kernel, declared before collection

EPYC's delivered cleanup study leaves all16 old-versus-cleanup cells Level;
LF512's aligned64KiB stays about294 ns versus the raw caller's431 ns. A remaining
concrete difference is the unrolled body versus native compact loops. Test
`probe4096-loop`: the same source stripe/combination/reduction macros, replacing
16 expanded turns with a fixed16-turn runtime loop. Original per-block cleanup,
word caller, reductions, tails and peel stay unchanged. The caller object's text
must equal the baseline; only the raw callee relocation changes. The loop adds
counter initialization, pointer advance, counter subtraction and a backward
conditional jump. Record their exact forms and derive the source from the single
raw kernel. This changes instruction-cache footprint and branch scheduling together.

All19 engines, all raw packed returns, critical/all-small/all-alignment/reference/
read-only guards must validate first; a15-turn mutant must fail, restored passes.
Earlier native objects must keep exact sections. Capture linked loop text/tables,
source, both printer outputs and flag/provenance records before collection.

Five questions, both CPUs/four paired layouts, same v3 random16-cell/20ms requested
batches, alternating sides/rotating questions, same load/rule; at most two whole-
pair retries for load, preserve every attempt:

1. `probe4096` → `probe4096-loop`.
2. `libdeflate512` → `probe4096-loop`.
3. `libdeflate` → `probe4096-loop`.
4. `libdeflate512` → `libdeflate512` (control).
5. `probe4096` → `probe4096` (control).

This is another UNVERIFIED diagnostic, retaining the old raw caller's tiny costs.
The runtime loop needs coordinated finite-trace proof support; existing straight-
line kernel verification alone covers its own scope. No optimized theorem or
whole-checksum competitive tail claim follows from this experiment.
