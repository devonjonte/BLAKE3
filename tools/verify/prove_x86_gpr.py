"""Proof of the general-register chunk-root kernel
(c/blake3_gpr_chunk_root_x86-64_unix.S, BLAKE3 #150), as assembled, equal
to the Lean specification's chunk root for `whole` whole blocks before the
last (0 to 15: every input of a chunk or less), every key, message byte,
last-block length and mode flags with bit 0 (CHUNK_START) clear, the
kernel's contract; no alignment promised for any pointer. The x86 model
(x86.py) also holds the memory contract and the callee-saved registers.

    python3 tools/verify/prove_x86_gpr.py [FILE.S] [WHOLE...]

Planted mutants it rejects (October 24): a rotation by 11 for 12, a
message word's and a key word's load from the wrong offset, CHUNK_END
dropped from the last block's flags, and rbx left unrestored.
"""
import os
import subprocess
import sys
import tempfile
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from z3 import BitVecVal, ZeroExt

import lean_spec as spec
import prove_x86
import x86
from aarch64 import Ptr, Region
from prove_hybrid import byte_symbols, same

CHUNK_START, CHUNK_END, ROOT = 1, 2, 8
SOURCE = sys.argv[1] if len(sys.argv) > 1 and sys.argv[1].endswith(".S") else os.path.join(prove_x86.ROOT_DIR, "c", "blake3_gpr_chunk_root_x86-64_unix.S")
counts = [int(a) for a in sys.argv[1:] if a.isdigit()] or list(range(16))

d = tempfile.mkdtemp()
obj = os.path.join(d, "gpr.o")
subprocess.run([prove_x86.CLANG, "-c", "--target=x86_64-linux-gnu", SOURCE, "-o", obj], check=True)
so = x86.link(obj)

for whole in counts:
    t0 = time.monotonic()
    key = byte_symbols("key", 32)
    blocks = byte_symbols("in", 64 * whole)
    last = byte_symbols("last", 64)
    last_len = prove_x86.u8("last_len")
    flags = prove_x86.u8("flags") & 0xFE
    packed = ZeroExt(56, flags) | (ZeroExt(56, last_len) << 8) | BitVecVal(whole << 16, 64)
    regions = {
        "in": Region("in", 64 * whole, False, lambda o, b=blocks: b[o]),
        "key": Region("key", 32, False, lambda o, b=key: b[o]),
        "last": Region("last", 64, False, lambda o, b=last: b[o]),
        "out": Region("out", 32, True, None),
    }
    args = [Ptr("in", 0), Ptr("key", 0), Ptr("last", 0), packed, Ptr("out", 0)]
    s = prove_x86.Setup(so, "blake3_gpr_chunk_root", regions, args, False)
    # The last block's length and the mode flags are public, as lengths
    # are: the kernel may branch on them (constant time holds for the data).
    s.m.lengths |= {"last_len", "flags"}
    f32 = ZeroExt(24, flags)
    prove_x86.d_row_facts(s.m, BitVecVal(0, 64), 1, [
        ZeroExt(24, last_len), BitVecVal(64, 32), f32 | (CHUNK_START | CHUNK_END | ROOT),
        f32 | CHUNK_START, f32, f32 | (CHUNK_END | ROOT),
    ])
    m = s.run()
    cv = spec.words(key)
    for b in range(whole):
        bf = f32 | CHUNK_START if b == 0 else f32
        cv = spec.compress(cv, spec.words(blocks[64 * b:64 * (b + 1)]), BitVecVal(0, 64), BitVecVal(64, 32), bf)[:8]
    lf = f32 | ((CHUNK_START if whole == 0 else 0) | CHUNK_END | ROOT)
    want = spec.compress(cv, spec.words(last), BitVecVal(0, 64), ZeroExt(24, last_len), lf)[:8]
    out = m.regions["out"]
    assert set(out.bytes) == set(range(32)), "the output is exactly its 32 bytes"
    got = spec.words([out.bytes[i] for i in range(32)])
    bad = [w for w in range(8) if not same(got[w], want[w])]
    assert not bad, f"whole={whole}: words {bad} differ from the specification"
    print(f"PROVED blake3_gpr_chunk_root whole={whole}: {m.steps} instructions, {time.monotonic() - t0:.1f} s", flush=True)
