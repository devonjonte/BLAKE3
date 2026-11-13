# Faster Adler-32 with a machine proof: active experiment

Goal: beat the strongest known implementations on the declared CPUs/workloads,
while keeping the seed-one contract and a checked theorem for the exact Ode code.
Tracker: https://github.com/servil-software-factory/BLAKE3/issues/377

The original 171-byte Ode implementation remains proved. **There is no optimized
Ode implementation yet.** `probe.c` is explicitly unverified native C, adapted
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
the reader requires exactly that cell set. Probe batches target 10 ms so the run
lasts long enough to observe machine load; full-workload batches keep 5 ms.
The first 5 ms probe attempts finished under a second and correctly received no
load verdict; those records are retained. Historical v2 data uses its pinned reader.

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
128 bits; wide-vector/VNNI/mask support needs coordinated work with Sam.
