# Measured wide-vector forms and the proposed proof boundary

The [width/reduction experiment](https://github.com/devonjonte/bench-hashes/tree/data/2026-11-13/ode-adler32-width-reduction)
uses native C at `08b870ad`; every optimized candidate remains UNVERIFIED.
Most of the aligned Xeon gain is already in libdeflate's internal 512-bit
kernel. The new u32 reductions help 16/64/256-byte probe calls, while 16-byte
calls and unaligned bulk still lose. EPYC bulk is mostly level.

The next design must earn its proof/model work with stronger measurements.
This list costs that work; it requests no shared-model change yet.

## Actual forms in the measured `probe512_r32`

Both delivered hosts assembled the same forms in `code-0.txt`, function
`probe512_r32` at 0x48600 through its final return at 0x489f6 (1015 bytes).
Full bytes, compiler flags, symbols and addresses are in the evidence folder.
Operands below use Intel destination-first order. Register names mean a view
of the same architectural vector state; ZMM16–18 occur in the measured code.

| encoding | exact operand form | immediates / purpose |
|---|---|---|
| VEX.128 | `vpxor xmm, xmm, xmm` | zero; upper-state rule matters |
| EVEX.512 | `vmovdqa32 zmm, m512` | RIP-relative weights |
| EVEX.512 | `vmovdqa64 zmm, m512` | RIP-relative weights |
| EVEX.512 | `vmovdqa32 zmm, zmm` | register copy |
| EVEX.512 | `vmovdqa64 zmm, zmm` | register copy |
| EVEX.512 | `vpternlogd zmm, zmm, zmm, imm8` | 0xff; compiler builds all-ones |
| EVEX.512 | `vpabsb zmm, zmm` | all-ones bytes become byte 1 |
| EVEX.512 | `vmovdqu64 zmm, m512` | unaligned full input loads |
| EVEX.512 | `vpdpbusd zmm, zmm, zmm` | unsigned input bytes × signed weights, non-saturating dword accumulate |
| EVEX.512 | `vpaddd zmm, zmm, zmm` | lane sums / prefixes |
| EVEX.512 | `vpslld zmm, zmm, imm8` | 6, 7, 8 |
| EVEX.512 | `vpbroadcastd zmm, r32` | tail length |
| EVEX.512 | `vpmulld zmm, zmm, zmm` | tail prefix contribution |
| VEX | `kmovq k, r64` | tail byte mask |
| EVEX.512 | `vmovdqu8 zmm{k}{z}, m512` | mask-zeroing byte load; suppressed bytes must stay unread |
| EVEX.512 | `vpbroadcastb zmm, r32` | tail weight offset |
| EVEX.512 | `vpaddb zmm, zmm, zmm` | tail weights |
| EVEX.512 | `vextracti64x4 ymm, zmm, imm8` | 1 |
| VEX.256 | `vpaddd ymm, ymm, ymm` | horizontal fold |
| EVEX.256 | `vextracti64x2 xmm, ymm, imm8` | 1 |
| VEX.128 | `vpaddd xmm, xmm, xmm` | horizontal fold |
| VEX.128 | `vpshufd xmm, xmm, imm8` | 0x4e, 0x55 |
| VEX.128 | `vmovdqa xmm, xmm` | register copy |
| VEX.128 | `vmovd r32, xmm` | raw u32 sum |
| EVEX.512 | `vpmovzxdq zmm, ymm` | large-block weighted sum only |
| VEX.256 | `vpaddq ymm, ymm, ymm` | large-block horizontal fold |
| VEX.128 | `vpaddq xmm, xmm, xmm` | large-block horizontal fold |
| VEX.128 | `vpsrldq xmm, xmm, imm8` | 8 |
| VEX.128.W1 | `vmovq r64, xmm` | raw u64 sum |
| VEX | `vzeroupper` | implicit register effects |

These are C compiler choices, including its construction of constants. Ode can
choose a smaller set deliberately. Each retained form needs Sam's hardware
cross-check row and coherent register-view semantics. Existing legacy SSE
instructions retain their upper-vector bits; VEX/EVEX writes follow their
architectural zeroing rules. The mask-zeroing load needs exact readable bounds.

## Proposed fixed 4 KiB raw-sums kernel: hypothesis

Use the existing source `kernel` machinery with four prefix accumulators and
unroll its sixteen 256-byte turns. Its single argument addresses exactly 4096
read-only bytes, at any alignment. Return one u64:

- low 32 bits: raw byte sum A, at most `255 * 4096 = 1044480`;
- high 32 bits: raw position-weighted sum B, at most
  `255 * 4096 * 4097 / 2 = 2139617280`.

A word-level caller composes blocks using `Block_adler32`'s append law and
reduces between blocks. The kernel has no tail mask, variable-length branch,
wide weighted reduction or scalar modular division. It still needs tests of
unaligned loads and a competitive measurement, and its caller still needs
competitive small/tail handling. This kernel has yet to be implemented or timed.

Likely retained forms: full 512-bit input/constant loads, copies, `vpdpbusd`,
`vpaddd`, immediate `vpslld`, 512→256→128 extracts/folds, `vpshufd`, and `vmovd`.
The source can load byte-ones as data rather than inherit C's `vpternlogd` /
`vpabsb` pair. Scalar code packs the two raw u32 values into RAX. Exact forms
will come from that assembled source before model work begins.

## Existing machinery and image binding to settle with Sam

`lang/prove.py` already generates straight-line kernel proofs. Today its
contract has 128-bit `reads` / `writes` lists and its recipe contains hex-specific
simplifications. A scalar packed return needs an extension of this mechanism;
reuse it rather than build another compiler or proof generator.

`one/lift_one.py` already resolves a RIP-relative vector load's relocation
against `--object`, reads its 16 data bytes, and emits a constant vector operand
(`.c`). That places object-data interpretation in the existing lifter trust
boundary. A 64-byte extension must also bind the final linked read-only image,
including relocation resolution, to the constants used by the theorem. Checking
only function text bytes would leave this part of the artifact unchecked.

Recommended division: Devon owns the raw-sums candidate, algebra, caller and
artifact checks. Sam chooses the shared vector-state/cell/proof-generator design
and the image-binding contract. The original scalar Adler theorem uses no static
vector data and stays unchanged.

— Devon Jonte
