"""The proofs reject wrong code: each mutant changes one instruction of a
proved kernel, and its proof must reject it. Internal checker errors stop
the run. The Arm mutations change decoded instructions; the x86 mutations
change source instructions and are assembled before proof.

    python3 tools/verify/mutants.py
"""

import os
from pathlib import Path
import subprocess
import sys
import tempfile

sys.path.insert(0, os.path.dirname(__file__))
import aarch64
import prove_hybrid
from aarch64 import Unproved


def mutants(code):
    """(description, mutated code) pairs: the first instance of each kind."""
    out = []
    def first(pred):
        return next(a for a, (m, ops) in sorted(code.items()) if pred(m, ops))
    def change(addr, mnem, ops, what):
        c = dict(code)
        c[addr] = (mnem, ops)
        out.append((f"{what} at {addr:#x}", c))
    a = first(lambda m, o: m == "ror")
    m, o = code[a]
    change(a, m, o[:2] + [f"#{(aarch64.imm(o[2]) + 1) % 32}"], "a rotation one bit off")
    a = first(lambda m, o: m == "eor" and o[0][0] == "w")
    change(a, "orr", code[a][1], "an eor made an orr")
    a = first(lambda m, o: m == "add" and o[0][0] == "w" and not o[2].startswith("#"))
    change(a, "eor", code[a][1], "an add made an eor")
    a = first(lambda m, o: m == "ldrb")
    m, o = code[a]
    base = o[1].strip("[]").split(",")
    off = aarch64.imm(base[1]) if len(base) > 1 else 0
    change(a, m, [o[0], f"[{base[0]}, #{off + 1}]"], "a schedule entry read from the next byte")
    a = first(lambda m, o: m == "orr" and o[0][0] == "w")
    change(a, "mov", [code[a][1][0], code[a][1][1]], "a flag left out")
    a = first(lambda m, o: m == "ldp" and o[2].startswith("[x2"))
    m, o = code[a]
    change(a, m, o[:2] + ["[x2, #32]"], "a key word read past the key")
    return out


def vector_mutants(code):
    out = []
    def first(pred):
        return next((a for a, (m, ops) in sorted(code.items()) if pred(m, ops)), None)
    def change(addr, mnem, ops, what):
        if addr is None:
            return
        c = dict(code)
        c[addr] = (mnem, ops)
        out.append((f"{what} at {addr:#x}", c))
    a = first(lambda m, o: m == "xar")
    if a is not None:
        m, o = code[a]
        change(a, m, o[:3] + [f"#{aarch64.imm(o[3]) + 1}"], "an xar rotation one bit off")
    a = first(lambda m, o: m == "sri")
    if a is not None:
        m, o = code[a]
        change(a, m, o[:2] + [f"#{aarch64.imm(o[2]) - 1}"], "an sri shift one bit off")
    a = first(lambda m, o: m == "add" and o[0].startswith("v"))
    if a is not None:
        m, o = code[a]
        change(a, "eor", [x.replace(".4s", ".16b") for x in o], "a vector add made an eor")
    a = first(lambda m, o: m == "zip1")
    if a is not None:
        change(a, "zip2", code[a][1], "a zip1 made a zip2")
    a = first(lambda m, o: m == "tbl")
    if a is not None:
        m, o = code[a]
        change(a, m, [o[0], o[1], o[0]], "a tbl through the wrong index table")
    a = first(lambda m, o: m == "lsr" and o[0][0] == "x" and o[1] == "x6")
    if a is not None:
        m, o = code[a]
        change(a, m, o[:2] + ["#9"], "the partial chunk's length field misread")
    return out


def sme_mutants(code):
    out = []
    def first(pred):
        return next((a for a, (m, ops) in sorted(code.items()) if pred(m, ops)), None)
    def change(addr, mnem, ops, what):
        if addr is None:
            return
        c = dict(code)
        c[addr] = (mnem, ops)
        out.append((f"{what} at {addr:#x}", c))
    a = first(lambda m, o: m == "xar")
    m, o = code[a]
    change(a, m, o[:3] + [f"#{aarch64.imm(o[3]) + 1}"], "an xar rotation one bit off")
    a = first(lambda m, o: m == "add" and o[0].startswith("z") and len(o) == 3)
    change(a, "eor", [x.replace(".s", ".d") for x in code[a][1]], "a vector add made an eor")
    a = first(lambda m, o: m == "mov" and "za0v.s[w13" in ", ".join(o))
    change(a, "mov", [code[a][1][0], code[a][1][1].replace("w13", "w12")], "a transpose reading the wrong slices")
    a = first(lambda m, o: m == "add" and len(o) == 4 and "/m" in o[1])
    change(a, "nop", [], "the counter's carry removed")
    a = first(lambda m, o: m == "st1w" and o[1] == "p2")
    change(a, "st1w", [code[a][1][0], "p0", code[a][1][2]], "a value stored with all sixteen lanes")
    a = first(lambda m, o: m == "index")
    if a is not None:
        m, o = code[a]
        change(a, m, o[:2] + ["#2"] if o[2].startswith("#") else o[:2] + ["w2"], "the counters' step changed")
    return out


def run(job):
    """One mutant's proof, in its own process (workers.py): the line saying
    whether the proof rejected it, and whether that is a failure."""
    label, code, prove = job
    if code is not None:
        aarch64.disassemble = lambda *a, **k: code
    try:
        prove()
        return f"{label}: PROVED (the proof is vacuous here)", True
    except Unproved as e:
        return f"{label}: rejected ({e})", False


def both_stored(sobj):
    """The SME2 chunk kernel's proof on the path that stores every value
    and on the one that stores a few: rejected if either fails."""
    import prove_sme2
    reasons = []
    for stored in (0, 3):
        try:
            prove_sme2.prove_chunks(sobj, 1, stored, False)
        except Unproved as e:
            reasons.append(f"storing {stored or 16}: {e}")
    if reasons:
        raise Unproved(reasons[0])


def jobs():
    """Every mutant, as (label, mutated code, the proof that must reject it)."""
    out = []
    obj = prove_hybrid.assemble()
    real = aarch64.disassemble
    base = real(obj, *[aarch64.symbols(obj)[n] for n in ("blake3_hybrid_c1", "blake3_hybrid_k1_end")])
    for what, code in mutants(base):
        out.append((f"c1 mutant, {what}", code, lambda: prove_hybrid.prove_c1(obj, 3, False)))
    syms = aarch64.symbols(obj)
    for name, prove in (("k2", lambda: prove_hybrid.prove_table(obj, "blake3_hybrid_k2", 2, 2, True)),
                        ("k7", lambda: prove_hybrid.prove_table(obj, "blake3_hybrid_k7", 7, 2, True)),
                        ("q3", lambda: prove_hybrid.prove_partial(obj, 3, 3))):
        base = real(obj, syms[f"blake3_hybrid_{name}"], syms[f"blake3_hybrid_{name}_end"])
        for what, code in vector_mutants(base):
            out.append((f"{name} mutant, {what}", code, prove))
    import prove_sme2
    sobj = prove_sme2.assemble()
    ssyms = aarch64.symbols(sobj)
    sbase = real(sobj, ssyms["blake3_sme2_hash16_chunks_512"], ssyms["blake3_sme2_text_end"], llvm=True)
    for what, code in sme_mutants(sbase):
        out.append((f"SME2 chunks mutant, {what}", code, lambda: both_stored(sobj)))
    # The induction over the SME2 extended-output kernel's group loop
    # (prove_sme2.prove_xof_every): its counter and pointer steps, which only
    # the step from one group to the next sees.
    xof = (ssyms["blake3_sme2_xof16_512"], min(v for v in ssyms.values() if v > ssyms["blake3_sme2_xof16_512"]))
    for what, reg, imm, new in (("the group loop's counter step", "x2", "#0x10", "#0x11"),
                                ("the group loop's pointer step", "x4", "#0x400", "#0x3c0")):
        a = next(a for a, (m, o) in sorted(sbase.items())
                 if xof[0] <= a < xof[1] and m == "add" and o == [reg, reg, imm])
        code = dict(sbase)
        code[a] = ("add", [reg, reg, new])
        out.append((f"induction mutant, {what} at {a:#x}", code, lambda: prove_sme2.prove_xof_every(sobj)))
    # Independent input bytes make a wrong parent-group stride observable.
    parents = ssyms["blake3_sme2_hash16_parents_512"]
    parents_end = min(v for v in ssyms.values() if v > parents)
    for what, reg, before, after in (("input stride", "x9", 1024, 512), ("output stride", "x4", 512, 256)):
        found = [a for a, (m, o) in sbase.items() if parents <= a < parents_end
                 and m == "add" and o[:2] == [reg, reg] and aarch64.imm(o[2]) == before]
        assert len(found) == 1, (what, found)
        a = found[0]
        code = dict(sbase)
        code[a] = ("add", [reg, reg, f"#{after}"])
        out.append((f"parent-group mutant, {what} at {a:#x}", code, lambda: prove_sme2.prove_parents_every(sobj)))
    # The message kernel's block loop (prove_block_loop): its next block's
    # offset off by 8, which only the step from one pass to the next sees,
    # and a rotation after the loop, which only the composed proof sees.
    import prove_block_loop
    msgs = ssyms["blake3_sme2_hash16_messages_512"]
    msgs_end = min(v for v in ssyms.values() if v > msgs)
    step_at = next(a for a, (m, o) in sorted(sbase.items()) if msgs <= a < msgs_end and m == "add" and o == ["x9", "x9", "#0x40"])
    after = [a for a, (m, o) in sorted(sbase.items()) if prove_block_loop.EXIT <= a < msgs_end and m == "xar"]
    m_, o_ = sbase[after[len(after) // 2]]
    for what, a, ins, prove in (("the block loop's offset step", step_at, ("add", ["x9", "x9", "#0x48"]), prove_block_loop.prove),
                                ("a rotation after the block loop", after[len(after) // 2], (m_, o_[:-1] + [f"#{int(o_[-1].lstrip('#'), 0) % 31 + 1}"]), prove_block_loop.prove_one_group)):
        code = dict(sbase)
        code[a] = ins
        out.append((f"block-loop mutant, {what} at {a:#x}", code, lambda prove=prove: prove(sobj)))
    # The kernel with an integer lane (prove_hybrid_loop): the integer
    # chunk's pointer step in the loop and its table index, which the
    # loop's halves see; and the group loop's counter step, which only the
    # induction over groups sees (from the unmutated kernel's halves, proved
    # here before any mutant runs).
    import prove_hybrid_loop as hl
    hobj = prove_sme2.assemble_hybrid()
    hsyms = aarch64.symbols(hobj)
    hbase = real(hobj, hsyms["blake3_sme2x2_hash_chunks_512"], prove_sme2.text_end(hobj), llvm=True)
    def halves():
        gen_a, s1, _ = hl.half_a(hobj)
        return gen_a, hl.half_b(hobj, gen_a, s1)[0]
    loop = [a for a in sorted(hbase) if hl.HEAD <= a < hl.EXIT]
    find = lambda m, o: next(a for a in loop if hbase[a] == (m, o))
    good = halves()
    for what, a, ins, prove in (("the integer chunk's pointer step", find("add", ["x27", "x27", "#0x40"]), ("add", ["x27", "x27", "#0x48"]), lambda: hl.half_a(hobj)),
                                ("the integer chunk's table index", find("add", ["x30", "x30", "#0x10"]), ("add", ["x30", "x30", "#0x11"]), halves),
                                ("the group loop's counter step", next(a for a in sorted(hbase) if hbase[a] == ("add", ["x2", "x2", "#0x12"])), ("add", ["x2", "x2", "#0x11"]), lambda: hl.prove_every(hobj, *good))):
        code = dict(hbase)
        code[a] = ins
        out.append((f"integer-lane mutant, {what} at {a:#x}", code, prove))
    return out



def x86_positive(_):
    """The precise domain used by the mutants, in a fresh worker."""
    import prove_x86 as p
    import prove_x86_loop as loop
    return loop.prove(p.assemble("avx2", False), "avx2", False, 1, True, p.ENTRY_STACKS[0])


def x86_mutant_jobs():
    """Assembled AVX2 mutants; reuse the existing rejection runner."""
    import prove_x86 as p
    import prove_x86_loop as loop
    source = Path(p.ROOT_DIR, "c/blake3_avx2_x86-64_unix.S").read_text()
    edits = [
        ("input-stride", "        add     rdi, 64\n", "        add     rdi, 56\n"),
        ("output-stride", "        add     rbx, 256\n", "        add     rbx, 224\n"),
        ("counter-direction", "        vpaddd  ymm1, ymm0, ymmword ptr [rsp+0x240]\n",
         "        vpsubd  ymm1, ymm0, ymmword ptr [rsp+0x240]\n"),
        ("tail-output-stride", "        add     rbx, 128\n", "        add     rbx, 96\n"),
        ("nonterminating", "        sub     rsi, 8\n", "        add     rsi, 8\n        sub     rsi, 8\n"),
        ("input-overread", "        vpbroadcastd ymm7, dword ptr [rcx+0x1C]\n        mov     r8, qword ptr [rdi]\n",
         "        vpbroadcastd ymm7, dword ptr [rcx+0x1C]\n        mov     r8, qword ptr [rdi]\n        vmovdqu xmm15, xmmword ptr [r8+64]\n"),
    ]
    root = Path(tempfile.mkdtemp(prefix="x86-proof-mutants-"))
    out = []
    for label, before, after in edits:
        assert source.count(before) == 1, (label, source.count(before))
        src, obj = root / (label + ".S"), root / (label + ".o")
        src.write_text(source.replace(before, after))
        subprocess.run([p.CLANG, "-c", "--target=x86_64-linux-gnu", str(src), "-o", str(obj)], check=True)
        so = p.x86.link(str(obj))
        def prove(so=so, label=label):
            try:
                return loop.prove(so, "avx2", False, 1, True, p.ENTRY_STACKS[0])
            except Unproved as error:
                if label == "nonterminating":
                    assert str(error).startswith("back edge leaves the next iteration"), str(error)
                raise
        out.append((f"assembled AVX2 mutant, {label}", None, prove))
    return out


def x86_memory_positive(_):
    """The unmodified kernels at the memory mutants' entry alignment."""
    import prove_x86 as p
    return (p.prove_compress(p.assemble("sse41", False), "sse41", False, False, p.ENTRY_STACKS[0]),
            p.prove_hash_many(p.assemble("avx2", False), "avx2", False, 8, 1, True, p.ENTRY_STACKS[0]))


def x86_memory_mutant_jobs():
    """Assembled x86 mutants for the ABI/alignment/trace memory contract."""
    import prove_x86 as p
    edits = [
        ("caller-stack write", "sse41", "compress",
         "_blake3_compress_in_place_sse41:\n",
         "_blake3_compress_in_place_sse41:\n        mov     qword ptr [rsp+120], 0\n",
         "outside"),
        ("aligned load of an unaligned buffer", "sse41", "compress",
         "_blake3_compress_in_place_sse41:\n        _CET_ENDBR\n        movups  xmm0, xmmword ptr [rdi]\n",
         "_blake3_compress_in_place_sse41:\n        _CET_ENDBR\n        movaps  xmm0, xmmword ptr [rdi]\n",
         "alignment"),
        ("secret-derived prefetch address", "sse41", "compress",
         "_blake3_compress_in_place_sse41:\n",
         "_blake3_compress_in_place_sse41:\n        mov     eax, dword ptr [rdi]\n        prefetcht0 [rax]\n",
         "no pointer"),
        ("masked store", "avx2", "hash_many",
         "        vmovups ymmword ptr [rbx], ymm12\n",
         "        vpxor ymm15, ymm15, ymm15\n        vpmaskmovd ymmword ptr [rbx], ymm15, ymm12\n",
         "unmodelled vector store"),
    ]
    root = Path(tempfile.mkdtemp(prefix="x86-memory-mutants-"))
    out = []
    for label, isa, kind, before, after, reason in edits:
        source = Path(p.ROOT_DIR, f"c/blake3_{isa}_x86-64_unix.S").read_text()
        assert source.count(before) == 1, (label, source.count(before))
        src, obj = root / (label.replace(" ", "-") + ".S"), root / (label.replace(" ", "-") + ".o")
        src.write_text(source.replace(before, after))
        subprocess.run([p.CLANG, "-c", "--target=x86_64-linux-gnu", str(src), "-o", str(obj)], check=True)
        so = p.x86.link(str(obj))
        def prove(so=so, isa=isa, kind=kind, reason=reason):
            try:
                if kind == "compress":
                    return p.prove_compress(so, isa, False, False, p.ENTRY_STACKS[0])
                return p.prove_hash_many(so, isa, False, 8, 1, True, p.ENTRY_STACKS[0])
            except Unproved as error:
                assert reason in str(error), str(error)
                raise
        out.append((f"x86 memory mutant, {label}", None, prove))
    return out


def main():
    import workers
    failures = 0
    # Forked workers inherit each job (its code and its proof's closure);
    # only the line comes back.
    for line, failed in workers.each(run, jobs(), 16):
        print(line, flush=True)
        failures += failed
    # Fresh workers release each proof's memo tables. Keep the x86 pool
    # at two processes, as in the all-count matrix.
    for result in workers.each(x86_positive, [None], 1):
        print(f"AVX2 mutant-domain positive control: proved {result}", flush=True)
    for line, failed in workers.each(run, x86_mutant_jobs(), 2):
        print(line, flush=True)
        failures += failed
    for result in workers.each(x86_memory_positive, [None], 1):
        print(f"x86 memory-mutant positive controls: proved {result}", flush=True)
    for line, failed in workers.each(run, x86_memory_mutant_jobs(), 2):
        print(line, flush=True)
        failures += failed
    sys.exit(1 if failures else 0)


if __name__ == "__main__":
    main()
