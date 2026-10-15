"""BLAKE3's 32-byte output of a message, as terms: the result a whole call
of `hash`, `keyed_hash`, or `derive_key` must compute.

lean/schedules.json holds, for each input length the whole-call proofs
use, the compressions BLAKE3 performs in order (lean/Schedule.lean's
`sched`); lean/ScheduleProofs.lean's `run_eq` proves that performing
them is the specification's output, for every key, mode, and input.
`hash32` performs them with lean_spec.compress, Lean's compression
function: an entry `[h, m, t, len, flags]` compresses chaining value `h`
(the key, -1, or entry `h`'s chaining value) with block `m` (input words
`m` to `m + 15`, zero past the input's end, or entries `l`'s and `r`'s
chaining values, `[l, r]`) at counter `t` and block length `len`, its
flags the mode's and `flags`, and the last entry's also ROOT."""
import functools
import json
import os
from z3 import BitVecVal
import lean_spec as spec

IV = [0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A, 0x510E527F, 0x9B05688C, 0x1F83D9AB, 0x5BE0CD19]
ROOT, KEYED_HASH, DERIVE_KEY_CONTEXT, DERIVE_KEY_MATERIAL = 8, 16, 32, 64


@functools.cache
def schedules():
    return json.load(open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "lean", "schedules.json")))


def w(x):
    return BitVecVal(x, 32)


def hash32(data, key=None, mode=0):
    """The 32-byte output of BLAKE3 over `data` (8-bit terms), as eight
    words: `hash` with no key; with `key` (eight 32-bit words) and
    `mode` its flag, `keyed_hash` (KEYED_HASH)."""
    entries = schedules().get(str(len(data)))
    assert entries is not None, f"no schedule for {len(data)} bytes: add the length to lean/emit.py's"
    key = [w(x) for x in IV] if key is None else key
    padded = data + [BitVecVal(0, 8)] * 64
    cvs = []
    for i, (h, m, t, n, flags) in enumerate(entries):
        block = spec.words(padded[4 * m:4 * m + 64]) if isinstance(m, int) else cvs[m[0]] + cvs[m[1]]
        last = ROOT if i == len(entries) - 1 else 0
        cvs.append(spec.compress(key if h == -1 else cvs[h], block, BitVecVal(t, 64), w(n), w(mode | flags | last))[:8])
    return cvs[-1]


def derive_key32(context, material):
    """`derive_key`'s 32-byte output: the context string's hash under
    DERIVE_KEY_CONTEXT is the key that hashes the material under
    DERIVE_KEY_MATERIAL."""
    ctx = hash32([BitVecVal(b, 8) for b in context.encode()], [w(x) for x in IV], DERIVE_KEY_CONTEXT)
    return hash32(material, ctx, DERIVE_KEY_MATERIAL)
