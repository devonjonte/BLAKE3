# First outside user: Adler-32 in Ode

An experiment on Sam Shackleton's Ode at **9a1ff09ec5f5f0d75139f02a4f7c1f4c81104666**.
It implements Adler-32 (RFC 1950, section 8), the checksum used by zlib. Adler-32
detects accidental changes; it provides no cryptographic authentication.

The questions:

1. Can a small project outside BLAKE3 use the current language? Where does the
   experience ask its author to work around the tooling?
2. Can an observation tool show what source choices produce and what unrelated
   edits preserve, beside trustworthy measurements of their cost?

## What works

`adler32.ode` implements the checksum in one byte loop. No change to Ode's compiler
or language was needed. `adler32_compact.ode` computes the same checksum with the
two reductions spelled `a > MOD - 1` rather than `a >= MOD`.

`../../observe.py` uses Ode's own compiler and assembly/layout printers. It records
one function's isolated machine-code bytes and their hashes, static instruction
and branch counts, saved registers, and the compiler's frame layout. It preserves
the generated source, assembly and disassembly alongside a JSON report. The report
names the compiler commit, fingerprints the compiler files, and records tool versions.

At the pinned compiler:

| | `>= MOD` | `> MOD - 1` |
|---|---:|---:|
| Function text | 171 bytes | 167 bytes |
| Static instructions | 55 | 53 |
| Conditional branches | 3 | 3 |
| Saved registers | 5 | 5 |
| Frame reservation, besides the saved registers | 0 bytes | 0 bytes |

The five saved registers use 40 bytes below the entry stack pointer. The frame
reservation of zero is a compiler layout field, **not** a zero-stack claim.

The original's reductions lower to empty true branches and nonempty false
branches. The printer emits a conditional jump and a jump over the false branch.
The equivalent spelling gives a nonempty true branch and omits that extra jump.
The table establishes a structural difference. Hardware timings are separate.

A first pilot on an **EPYC 9275F** used four old/new pairs with distinct explicit
link paddings and alternating order. Both spellings passed the linked-byte check.
All sixteen runs (eight comparison runs and eight same-code control runs) were
quiet. The compact spelling read faster in nine of the 24 cells, with none slower.
For example, warm calls on 4 KiB took 10.8% less time on zero bytes, 19.2% less on
255 bytes, and 21.8% less on sequential bytes. Every same-code cell read level.
These are exploratory wall-time results on one machine. **Thread counters were
unavailable**, so the pilot supplies no cycle or speed-state evidence.

The samples, logs and commands are in
[data `2026-11-13/ode-adler32-pilot`](https://github.com/devonjonte/bench-hashes/tree/data/2026-11-13/ode-adler32-pilot).

## What has been checked

- Four fixed checksum vectors, including `Wikipedia` and `123456789`.
- Every one-byte message, plus zero, 255, sequential and seeded-random data at
  19 lengths, including 5552 and 65521 and their neighbors, against Python's zlib.
  Both implementations are checked.
- Read-only input at the beginning and end of a page between inaccessible pages,
  for both implementations. A deliberate one-byte overread faults at the guard.
- Exact isolated function bytes and frame layout under a repeated build, a comment
  edit, and an unrelated function inserted before or after the target. All match.
- Positive controls: changing the checksum seed changes the bytes and the answer;
  equivalent reduction spelling changes code structure while preserving answers.
- A misspelled target function produces a loud error from the observer.
- A changed linked instruction causes the benchmark's validation to fail before
  calling the checksum.
- The benchmark checks the **linked** function's bytes against the observation
  before it calls the function. Its tests check samples reading and abstention on
  busy load; unchanged synthetic pairs read level and planted +20% pairs read slower.

**Proof status:** `Spec_adler32.lean` states the intended contract and checks two
specification examples. No theorem yet connects the assembled checksum to that
contract. The tests above are executable evidence, not a correctness, memory-safety,
termination, constant-time or resource-bound proof. Input and length are public.

## Run the exercise

This first observer and workload adapter target **x86-64 Linux**. They need Python
3, Lean 4.34.1 (`lake` on PATH), a C assembler, GNU objcopy and ar, b3sum, and LLVM
objdump. The default disassembler is `llvm-objdump-21`; `OBJDUMP` names another LLVM
objdump executable. `CC` and `OBJCOPY` name executables too.

From `tools/verify/machine/` (output directories must be new):

```sh
python3 observe.py experiments/adler32/adler32.ode adler32 /absolute/path/observation
python3 experiments/adler32/test_adler32.py --out /absolute/path/tests
(cd lang && lake build Abi Spec_bytes && lake env lean ../experiments/adler32/Spec_adler32.lean)
```

The tests read no clock. The observer builds the language printer without building the
BLAKE3 proofs. Each external command has a timeout. Use a process-group supervisor
for a hard bound over the complete job.

## Measure on a dedicated machine

`bench.rs` is the first workload adapter, using bench-hashes' existing **clocks**
crate for timing, load, summaries and paired comparisons. It measures warm,
back-to-back checksum calls at eight lengths and three byte patterns, including
consumption of each result. Raw wall times, call counts, process CPU times and
available per-thread cycles/instructions are preserved. Missing counters are
explicit. Busy or unobserved load receives no comparison verdict.

Give the adapter a bench-hashes checkout at
**5f99f456951ab36f7201decd8aa5e0249ec67bd1**, with its clocks directory unchanged:

```sh
python3 experiments/adler32/prepare_bench.py /path/to/bench-hashes /path/to/observation /path/to/build
ODE_PADDING=256 cargo build --release --manifest-path /path/to/build/Cargo.toml
/path/to/build/target/release/ode-adler-observer --validate
# On a quiet measurement machine, pin each run of a pair to the same CPU:
taskset -c CPU /path/to/build/target/release/ode-adler-observer --collect > samples.tsv
```

`--validate` reads no clock. `ODE_PADDING` chooses 0 to 4096 bytes in multiples of
16 before the function, at build time; record the actual linked address too. Build
all executables before collecting. Use a fresh layout for each old/new pair,
alternating which side runs first; include same-code pairs. Once at least three
quiet pairs exist:

```sh
/path/to/build/target/release/ode-adler-observer --compare old1.tsv new1.tsv old2.tsv new2.tsv old3.tsv new3.tsv
```

This calls clocks' existing comparison rule. It is an exploratory pilot, not a
release gate or a reliability claim. Its scope is warmed scalar checksum calls on
one core. Cold calls, concurrent callers, other architectures, allocation, energy,
code/data cache misses and hardware latency models remain outside this exercise.

## What using Ode taught us

1. **A small non-BLAKE3 function works without extending the language.** All values
   are 64-bit words; the checksum's modulo operation is expressed by bounded sums
   and conditional subtraction. This keeps the first experiment within the language
   that exists.
2. **A structural report makes a source choice tangible.** Two equivalent comparison
   spellings expose the empty-branch printer case. An explicit report shows the cost
   instead of asking a programmer to discover it by inspecting assembly unaided.
3. **Per-function isolation is testable today.** The tested unrelated edits preserve
   exact function bytes. This is evidence for these transformations at this compiler,
   not a theorem about every future edit or linked placement.
4. **The first build needs project scaffolding.** We reused `odec.py` and `Lang.lean`
   directly. A reusable project command would remove knowledge of generated Lean
   modules and the lab's directory layout. The existing proof driver also expects
   contract modules registered in the lab and usability theorems in its shared file.
   Supplying a project's contracts and lemmas should become an ordinary project task.
5. **Choosing a missing function is silent in the existing printer.** It emits an
   empty selection. The observer detects that before assembly; the printer could own
   this diagnostic for every caller.
6. **Evidence has several kinds.** A checked contract definition, passing examples,
   a structural control and measured costs each establish something different. The
   report states its proof status explicitly so a user can see what remains open.

The next useful step is a machine-code theorem for this checksum, while recording
what its author has to supply. That will exercise the proof interface independently
of BLAKE3. Improving the branch printer is a separate candidate, weighed against the
existing functions' proofs and code before changing the shared compiler.
