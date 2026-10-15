"""Prove what a whole hash runs depends only on its input's length
(QUALITY.md, "Timing and secrets", the first condition), as compiled.

The compiled library's `hash` (through `rust/`'s `verify_hash`) runs on a
message of symbolic bytes, on each platform's kernels in turn. The run may
take no branch, select, address, or table index that depends on those
bytes: the executor stops at the first. So each length's run is one path,
the same for every message: the instructions and the addresses they touch
depend on the length alone. The process's state is the one a hash meets
after `initialize()`: the platform it detected recorded.

    pypy3 tools/verify/prove_timing.py [LENGTH...]
"""

import os
import re
import subprocess
import sys
import time

sys.path.insert(0, os.path.dirname(__file__))
from z3 import BitVec, BitVecVal
import aarch64
from aarch64 import Region, Ptr, Unproved
from prove_hybrid import byte_symbols
import prove_rust
import results
import whole
import lean_spec as spec

# Lengths: every length to two blocks, the chunk boundaries, and powers of
# two and their neighbours to 64 KiB.
LENGTHS = sorted(set(list(range(0, 130)) + [1023, 1024, 1025, 2047, 2048, 2049, 3071, 3072, 3073]
                     + [2 ** k + d for k in range(12, 17) for d in (-1, 0, 1)]))

# The platforms: the discriminant `initialize()` records for each
# (src/platform.rs: NEON 6, SME2 7), and the longest input each is proved to.
PLATFORMS = {"NEON": (6, 1 << 16), "SME2": (7, 1 << 16)}


def process_image(lib, platform):
    """The library as loaded: its file bytes, its relocated pointers, and
    `.bss`, zero but the platform `initialize()` recorded and std's feature
    cache."""
    sections = subprocess.run(["readelf", "-SW", lib.so], capture_output=True, text=True, check=True).stdout
    bss = re.search(r"\.bss\s+NOBITS\s+([0-9a-f]+)\s+[0-9a-f]+\s+([0-9a-f]+)", sections)
    end = int(bss.group(1), 16) + int(bss.group(2), 16)
    fixed = {lib.syms[lib.symbol("8platform8DETECTED")]: platform}
    # std's feature cache, initialised with every feature present: the
    # library asks it only for SHA-3 (neon_hybrid::sha3_detected), which
    # every Apple M-series core has.
    detect = lib.syms[lib.symbol("10std_detect6detect5cache5CACHE")]
    fixed.update({detect + i: 0xff for i in range(3 * 8)})
    pointers = {}
    for line in subprocess.run(["readelf", "-rW", lib.so], capture_output=True, text=True, check=True).stdout.splitlines():
        f = line.split()
        if len(f) >= 4 and f[2] == "R_AARCH64_RELATIVE":
            for i in range(8):
                pointers[int(f[0], 16) + i] = (Ptr("image", int(f[3], 16)), i)
        if len(f) == 4 and f[2] == "R_AARCH64_TLSDESC":
            # A descriptor of the library's own TLS: its resolver, then its
            # variable's offset from the thread pointer (past the 16-byte TCB).
            at, offset = int(f[0], 16), 16 + int(f[3], 16)
            for i in range(8):
                pointers[at + i] = (Ptr("tlsdesc", 0), i)
                fixed[at + 8 + i] = (offset >> (8 * i)) & 0xff
    image = lib.image
    def initial(o):
        if o in pointers:
            return pointers[o]
        return BitVecVal(fixed.get(o, image.get(o, 0)), 8)
    return end, initial


# The clock at a thread's first call and at its second: both after a pause
# (each call long after the one before) or both back to back (one tick
# after), at Apple's 24 MHz. The first call sets up the thread's state (the
# SME2 walk's scratch); the second finds it.
CLOCKS = {"after a pause": (10 ** 12, 2 * 10 ** 12), "back to back": (1, 2)}


def tls_block(lib):
    """A new thread's TLS block: the 16-byte TCB, then `.tdata`'s bytes,
    then `.tbss`, zero."""
    sections = subprocess.run(["readelf", "-SW", lib.so], capture_output=True, text=True, check=True).stdout
    tdata = re.search(r"\.tdata\s+PROGBITS\s+([0-9a-f]+)\s+[0-9a-f]+\s+([0-9a-f]+)", sections)
    tbss = re.search(r"\.tbss\s+NOBITS\s+[0-9a-f]+\s+[0-9a-f]+\s+([0-9a-f]+)", sections)
    start, size = int(tdata.group(1), 16), int(tdata.group(2), 16)
    image = lib.image
    return Region("tls", 16 + size + int(tbss.group(1), 16), True,
                  lambda o: BitVecVal(image.get(start + o - 16, 0) if 16 <= o < 16 + size else 0, 8), lo=16)


CONTEXT = "BLAKE3 2019-12-27 16:29:52 test vectors context"   # rust/src/lib.rs's, the test vectors'


def call_setup(call, n, msg, key):
    """`call`'s entry, its arguments, the regions they point at, and the
    result it must return, on message `msg` (and `key`, for keyed_hash)."""
    data = {"input": Region("input", n, False, lambda o: msg[o])}
    if call == "hash":
        return "verify_hash", [Ptr("input", 0), BitVecVal(n, 64), Ptr("out", 0)], data, whole.hash32(msg)
    if call == "keyed_hash":
        data["key"] = Region("key", 32, False, lambda o: key[o])
        return ("verify_keyed_hash", [Ptr("key", 0), Ptr("input", 0), BitVecVal(n, 64), Ptr("out", 0)], data,
                whole.hash32(msg, spec.words(key), whole.KEYED_HASH))
    if call == "derive_key":
        return "verify_derive_key", [Ptr("input", 0), BitVecVal(n, 64), Ptr("out", 0)], data, whole.derive_key32(CONTEXT, msg)
    # The Hasher, fed the message in two updates cut at its middle.
    return ("verify_hasher_split", [Ptr("input", 0), BitVecVal(n, 64), BitVecVal(n // 2, 64), Ptr("out", 0)], data,
            whole.hash32(msg))


def prove_length(lib, n, platform, clocks, call="hash"):
    """A thread's first two calls of `call` on `n` bytes, each on its own
    symbolic message (and key), each at its clock: each one path, the
    convention kept, and the standard's result for its message."""
    m = prove_rust.machine(lib, {})
    m.local = lib.syms
    # The assembly kernels by their proved statements, where the library's
    # bytes are the proved ones (prove_rust.proved_code): those proofs show
    # each returns its statement and takes a path set by lengths alone.
    m.contracts = {**prove_rust.sme2_contracts(lib), **prove_rust.hybrid_contracts(lib)}
    m.regions["tls"] = tls_block(lib)
    end, initial = process_image(lib, platform)
    for name in ("image", "text"):
        # Writable: the statics in .data and .bss are.
        m.regions[name] = Region(name, end, True, initial)
    steps = []
    for k, now in enumerate(clocks):
        message, key = byte_symbols(f"msg{k}_", n), byte_symbols(f"key{k}_", 32)
        entry, args, data, want = call_setup(call, n, message, key)
        m.regions.update(data)
        m.regions["out"] = Region("out", 32, True, None)
        # A fresh frame, its bytes indeterminate (compiled code copies
        # structures with their padding): one that steered the run would
        # stop it, and one in the result would fail the comparison.
        m.regions["stack"] = Region("stack", prove_rust.STACK, True, lambda o, k=k: BitVec(f"stack{k}_{o}", 8))
        fresh = prove_rust.machine(lib, {})
        m.x, m.v = fresh.x, fresh.v
        m.clock = {"cntvct_el0": now, "cntfrq_el0": 24_000_000}
        for i, a in enumerate(args):
            m.x[i] = a
        start = m.steps
        prove_rust.run(lib, m, entry)
        steps.append(m.steps - start)
        prove_rust.compare(m.regions["out"], 0, want)
    return steps


def one_length(lib, n, platform, clocks, call="hash"):
    first, second = prove_length(lib, n, platform, clocks, call)
    return f"one path each and the standard's result, {first} and {second} instructions"


# The calls proved, and the longest input each is proved to: hash to each
# platform's longest; the others, sharing its code past their first steps,
# to 4 KiB and its neighbours.
CALLS = {"hash": None, "keyed_hash": 4097, "derive_key": 4097, "Hasher in two updates": 4097}


def prove(lengths=()):
    """The whole-call cases at `lengths` (every length of LENGTHS when
    none), each call to its longest: the number that failed and the forms
    they ran. A passing run of every length is recorded (results.py)."""
    cases = [(f"{call}, {platform}, {n} bytes, {when}", one_length,
              (n, code, clocks, "Hasher" if call.startswith("Hasher") else call))
             for call, upto in CALLS.items()
             for platform, (code, longest) in PLATFORMS.items()
             for n in lengths or LENGTHS if n <= (upto or longest)
             for when, clocks in CLOCKS.items()]
    so = prove_rust.build()
    failed, ran = prove_rust.run_cases(so, cases)
    if not failed and not lengths:
        results.save_forms("timing", so, ran)
    return failed, ran


def main():
    failed, _ = prove([int(a) for a in sys.argv[1:]])
    sys.exit(1 if failed else 0)


if __name__ == "__main__":
    main()
