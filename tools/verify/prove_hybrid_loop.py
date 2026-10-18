"""The SME2 kernel with an integer lane (c/blake3_sme2_hybrid_aarch64.S,
18 chunks a group: 16 on SME2, 2 on the core's integer units), its block
loop proved once a pass, as prove_block_loop.py proves the plain SME2
kernel's. Each pass hashes one block of each SME2 chunk and two blocks of
one integer chunk: chunk 16 in passes 0 to 7, chunk 17 in passes 8 to 15,
so the loop is proved in two halves, each an induction over its passes.

    pypy3 tools/verify/prove_hybrid_loop.py
"""

import os
import sys

sys.path.insert(0, os.path.dirname(__file__))
from z3 import Array, BitVec, BitVecSort, BitVecVal, Concat, Extract, Select, ULE, UGE, ZeroExt, simplify
import aarch64
import induction
import prove_sme2
import prove_block_loop as pbl
from aarch64 import Ptr, Region, Unproved
from prove_hybrid import byte_symbols
import lean_spec as spec

HEAD = 0x208   # the block loop's head (blake3_sme2x2_hash_chunks_512_block)
EXIT = 0x2930  # after its last pass in the loop (pass 14): pass 15 follows
INT = (1, 2, 3, 4, 5, 6, 11, 16)   # the integer chunk's state, words 0-7 (w1-w6, w11, w16)


def setup(obj, groups=1):
    """A group of 18 chunks, each an array read at any offset; with
    groups = 2, more to come."""
    lanes = [Array(f"msg{l}", BitVecSort(64), BitVecSort(8)) for l in range(18)]
    key = byte_symbols("key", 32)
    regions = {}
    for l in range(18):
        r = Region(f"input{l}", 1024, False, (lambda a: lambda o: Select(a, aarch64.as_bv(o)))(lanes[l]))
        r.symbolic_initial = True
        regions[f"input{l}"] = r
    regions["key"] = Region("key", 32, False, lambda o: key[o])
    regions["out"] = Region("out", 32 * 18 * groups, True, None)
    table = Region("table", 8 * 18 * groups, False, None)
    for i in range(18 * groups):
        for j in range(8):
            table.bytes[8 * i + j] = (Ptr(f"input{i % 18}", 0), j)
    regions["table"] = table
    s = prove_sme2.HybridSetup(obj, regions)
    m = s.m
    counter = BitVec("counter", 64)
    flags, start, end = (BitVec(x, 8) for x in ("flags", "start", "end"))
    m.x[0], m.x[1], m.x[2] = Ptr("table", 0), Ptr("key", 0), counter
    m.x[3] = Concat(BitVec("junk", 32), BitVecVal(0, 8), end, start, flags)
    m.x[4], m.x[5] = Ptr("out", 0), BitVecVal(groups, 64)
    m.lengths = {"len_k"}
    m.assumptions = []
    return s, m, lanes, key, (counter, flags, start, end)


def comp(h, lane, off, counter, flags):
    return spec.compress(h, pbl.block_words(lane, off), counter, BitVecVal(64, 32), ZeroExt(24, flags))[:8]


def term_of_key(text, m):
    """A memory key (aarch64.key: an offset's normal form, printed) as a
    term again, its symbols the machine's length symbols."""
    import re
    from z3 import parse_smt2_string
    names = set(re.findall(r"[A-Za-z_][A-Za-z_0-9]*", text)) & set(m.lengths)
    decls = {n: BitVec(n, 64) for n in names}
    return parse_smt2_string(f"(assert (= {text} (_ bv0 64)))", decls=decls)[0].arg(0)


def stored(m, at):
    """The 8 words the output holds at byte `at`, whatever form its offsets
    take (the code computes them from the pass), or None."""
    out = m.regions["out"]
    found = {}
    for o, b in out.bytes.items():
        oo = BitVecVal(o, 64) if isinstance(o, int) else term_of_key(o, m)
        for j in range(32):
            if j not in found and (o == at + j if isinstance(o, int) else aarch64.holds(m, oo == at + j)):
                found[j] = b
                break
    if len(found) != 32:
        return None
    return spec.words([found[j] for j in range(32)])


def integer_state(m):
    return [Extract(31, 0, m.x[r]) if m.x[r].size() == 64 else m.x[r] for r in INT]


def half_a(obj, groups=1):
    """Passes 0 to 7: pass 0 checked as it runs, 1 to 7 by induction."""
    from z3 import BitVec as BV
    s, m, lanes, key, (counter, flags, start, end) = setup(obj, groups)
    s0 = induction.run_to(m, s.entry, HEAD)
    s1 = induction.run_to(induction.snapshot(s0), HEAD, HEAD)
    s2 = induction.run_to(induction.snapshot(s1), HEAD, HEAD)
    kw = spec.words(key)
    for l in range(16):
        pbl.compare(s0, [s0.v[i][l] for i in range(8)], kw, f"lane {l} entering the loop (the key)")
        pbl.compare(s1, [s1.v[i][l] for i in range(8)], comp(kw, lanes[l], 0, counter + l, flags | start), f"lane {l} after pass 0")
    c = comp(comp(kw, lanes[16], 0, counter + 16, flags | start), lanes[16], 64, counter + 16, flags)
    pbl.compare(s1, integer_state(s1), c, "chunk 16 after pass 0 (its blocks 0 and 1)")
    print("pass 0: each SME2 chunk's block 0 and chunk 16's blocks 0 and 1, under the key, with the start flag", flush=True)
    k = BV("len_k", 64)
    gen = pbl.BlockGeneralized(s1, s2, k)
    K = k + 1
    passes = 0
    while True:
        passes += 1
        mk = gen.machine(s1, k)
        mk.assumptions = [ULE(k, 6)]   # pass K = 1 + k, 1 to 7
        mk.lengths = {"len_k"}
        h = [[mk.v[i][l] for i in range(8)] for l in range(16)]
        hi = integer_state(mk)
        ends = induction.paths(mk, HEAD, {HEAD, EXIT})
        forget = set()
        import canon
        for e, _ in ends:
            canon.set_context(e.assumptions, e.lengths)
            forget.update(b for b in induction.mismatches(e, gen, k + 1)
                          if not (b[0] == "v" and b[1] < 8) and not (b[0] == "x" and b[1] in INT))
            canon.set_context([], set())
        print(f"  pass {passes}: {len(ends)} paths, {len(forget)} positions left unknown {sorted(map(str, forget))[:8]}", flush=True)
        if not forget:
            break
        for pos in forget:
            gen.forget(pos)
    for e, _ in ends:
        if e.stopped_at != HEAD:
            raise Unproved("half A leaves the loop")
        last = aarch64.holds(e, K == 7)
        if not last and not aarch64.holds(e, K != 7):
            raise Unproved("a path in half A leaves open whether its pass is chunk 16's last")
        for l in range(16):
            pbl.compare(e, [e.v[i][l] for i in range(8)], comp(h[l], lanes[l], 64 * K, counter + l, flags), f"lane {l} after pass K")
        c = comp(comp(hi, lanes[16], 128 * K, counter + 16, flags), lanes[16], 128 * K + 64, counter + 16, flags | end if last else flags)
        pbl.compare(e, integer_state(e), c, "chunk 16 after pass K (its blocks 2K and 2K + 1)")
        if last:
            got = stored(e, 32 * 16)
            if got is None:
                raise Unproved("pass 7 leaves chunk 16's chaining value unstored")
            pbl.compare(e, got, c, "chunk 16's chaining value, stored at pass 7")
    return gen, s1, f"half A: {len(ends)} paths of passes 1 to 7, each the standard's compressions (chunk 16 stored at pass 7)"


def main():
    obj = prove_sme2.assemble_hybrid()
    gen, s1, what = half_a(obj)
    print(what)


if __name__ == "__main__":
    main()
