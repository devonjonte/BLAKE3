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

`adler32.ode` implements the checksum in one byte loop, using Sam's original
parser and assembly printer. Proof-generator extensions are described below.
`adler32_compact.ode` computes the same checksum with the
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

## Checked machine-code theorem

**The original `adler32.ode` is now proved.** Its 171-byte assembled object is
byte-for-byte identical to the one tested and benchmarked above. The proof
annotations change no instructions. The compact variant remains tested only.

The generated theorem (`../../lang/Proof_adler32.lean`) is:

```lean
Proof_adler32.adler32_meets : ∀ (input n : BitVec 64) (bytes : List (BitVec 8)),
  Abi.Meets Code_adler32.prog 0x100000 (Adler32.contract input n bytes)
```

For every message and permitted entry state, the lifted instructions terminate
without a modeled fault, return the Adler-32 defined by the contract, preserve the
calling convention, and leave every byte outside the permitted stack area
unchanged. The contract grants 64 bytes of stack; the generated proof uses 40.
A usability theorem supplies a concrete nonempty input meeting the preconditions.
Input and length are public. There is no constant-time or exact execution-cost claim.

The compiler wrote the 272-line machine proof from the source and its annotations.
`Lemmas_adler32.lean` holds 133 lines of hand-written supporting lemmas: bounded
conditional subtraction equals reduction modulo 65521, one loop step preserves the
remaining-fold invariant, and the final words pack the specification's checksum.
The contract remains the same modular arithmetic as the initial experiment.

Three small proof-generator extensions were needed: a variant expression (`n - i`),
byte-load values in a read-only loop body, and normalization of a saved register
at stack offset zero. The assembly printer is unchanged. Existing `push`, `pad`
and `merge` proofs regenerate and check with these changes.

**Trust boundary:** this is a theorem on Ode's x86-64 model. The object-to-model
link still trusts LLVM objdump and the existing lifter. The theorem depends on
Lean's three standard axioms and 32 native `bv_decide` axioms, as printed in
`proof.log`. It therefore does not yet meet the independent-checker-only goal in
Sam's design. It makes no claim about every behavior of real processors beyond
the model's assumptions.

An audit regenerates the unchanged proof and rechecks it directly with Lean,
bypassing the target cache. Wrong seed, overread and wrong result-contract variants
are refused by the machine-code proof; an impossible contract is refused by the
usability theorem. Wrong-reduction and wrong-packing variants time out at 30 seconds
and receive **no verdict**. The first wrong-reduction attempt also timed out at
120 seconds. The original proof is restored and checked again. These timeouts
remain a diagnostic limitation; they are not reported as caught mutants.

## Run the exercise

This first observer and workload adapter target **x86-64 Linux**. They need Python
3, Lean 4.34.1 (`lake` on PATH), a C assembler, GNU objcopy and ar, b3sum, and LLVM
objdump. The default disassembler is `llvm-objdump-21`; `OBJDUMP` names another LLVM
objdump executable. `CC` and `OBJCOPY` name executables too.

From `tools/verify/machine/` (output directories must be new):

```sh
# Normal project build: compile, generate the machine proof, check it, then observe.
sh experiments/adler32/build.sh /absolute/path/checked-build
# Explicit development opt-out: the report remains marked unverified.
sh experiments/adler32/build.sh /absolute/path/unverified-build --skip-proof
python3 experiments/adler32/test_adler32.py --out /absolute/path/tests
```

The normal build stops on a failed proof before publishing its output directory.
It compares the observed object with the object lifted for the theorem before
marking the report checked. Build controls exercise success, explicit opt-out, and
a wrong seed that must fail the default build. The tests read no clock.

The low-level `observe.py SOURCE FUNCTION NEW_OUTPUT` command observes code
structure only and says so in its report. Each external command has a timeout.
Use a process-group supervisor for a hard bound over the complete job. After a
successful build, `python3 experiments/adler32/audit_proof.py NEW_OUTPUT` runs the
negative proof controls. Exit 2 means at least one timed out; the original source
and checked generated proof are restored last.

## Measure on a dedicated machine

`bench.rs` is the first workload adapter, using bench-hashes' existing **clocks**
crate for timing, load, summaries and paired comparisons. It compares the proved
Ode baseline with zlib 1.4, zlib-ng 2.3.3 and libdeflate 1.26 through the same native
adapter boundary. Ten lengths, four patterns and two alignments give 80 cells.
See [the declared comparison procedure](COMPARISON.md) for exact versions, build
settings, call overhead, paired controls and limits. Raw wall times, call counts,
process CPU times and available cycles/instructions are preserved. Missing counters
are explicit. Busy or unobserved load receives no comparison verdict.

Give the adapter a bench-hashes checkout at
**5f99f456951ab36f7201decd8aa5e0249ec67bd1**, with its clocks directory unchanged.
`/path/to/deps` contains clean checkouts named `zlib`, `zlib-ng` and `libdeflate` at
the commits declared in `COMPARISON.md`. Preparation needs CMake and builds the
libraries with their release defaults:

```sh
python3 experiments/adler32/prepare_bench.py /path/to/bench-hashes /path/to/checked-build /path/to/deps /path/to/build
ODE_PADDING=256 cargo build --release --manifest-path /path/to/build/Cargo.toml
/path/to/build/target/release/ode-adler-observer --validate
# On a quiet measurement machine, pin each run of a pair to the same CPU:
taskset -c CPU /path/to/build/target/release/ode-adler-observer --collect ode > ode.tsv
# Other engines: zlib, zlib-ng, libdeflate
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
release gate or a reliability claim. Its scope is warmed native checksum calls on
one core. Cold calls, concurrent callers, other architectures, allocation, energy,
code/data cache misses and hardware latency models remain outside this exercise.

## Reuse in a larger codebase

[The libdeflate integration experiment](REUSE.md) imports this project's proved
object into a real C compression/decompression library. Its two whole-buffer
checksum calls fit the seed-one contract. The experiment preserves the general
incremental checksum API and checks the final linked bytes before cross-testing
ordinary and substituted zlib-format streams.

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

The next proof-tool improvement is a faster, source-level diagnosis of the two
wrong variants whose proofs timed out. Proving the compact variant is separate:
it cannot inherit the original's theorem. Improving the branch printer is also
a separate candidate, weighed against existing functions' proofs and code before
changing the shared compiler.
