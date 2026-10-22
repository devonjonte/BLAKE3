"""Check the x86-64 model against the CPU: every register-only instruction
form the x86-64 kernels use (its mnemonic, register widths, and
immediates as they occur), executed natively on random register states
and by the model (x86.py), must agree bit for bit. Needs an x86-64 CPU
(CI's); the AVX-512 forms need AVX-512, and are reported skipped without.

    python3 tools/verify/cross_check_x86.py

For Intel SDE, assemble the test functions natively first, then execute
only the prepared functions under emulation (SDE need not follow the
compiler and disassembler subprocesses):

    python3 tools/verify/cross_check_x86.py --prepare DIR
    sde64 -skx -- python3 tools/verify/cross_check_x86.py --prepared DIR

Loads, stores, branches, and the general registers' few instructions are
not checked here: the proofs check every address against its region, and
their models are a few lines each.
"""

import ctypes
import json
import os
import random
import re
import shutil
import subprocess
import sys
import tempfile

sys.path.insert(0, os.path.dirname(__file__))
from z3 import BitVecVal
import x86
import aarch64

FILES = ("sse41", "avx2", "avx512", "partial")


def forms(code):
    """Each register-only vector form, registers renamed: vectors to
    xmm/ymm/zmm 0-3 by first use, masks to k1-k2, general registers to
    r8d-r11d / r8-r11."""
    seen = {}
    for mnem, ops, _ in code.values():
        if not any(x86.is_vreg(x86.strip_mask(o)[0]) for o in ops):
            continue
        if any("[" in o for o in ops):
            continue
        vec, gpr, msk = {}, {}, {}

        def rename(mt):
            r = mt.group(0)
            if re.match(r"[xyz]mm\d+$", r):
                n = vec.setdefault(int(r[3:]), len(vec))
                return f"{r[:3]}{n}"
            if re.match(r"k\d$", r):
                return f"k{msk.setdefault(r, len(msk) + 1)}"
            base, bits = x86.SUB[r]
            n = gpr.setdefault(base, len(gpr))
            return {64: f"r{8 + n}", 32: f"r{8 + n}d"}[bits]
        text = re.sub(r"\b([xyz]mm\d+|k\d|r[a-z0-9]+|e[a-z]{2})\b",
                      lambda mt: rename(mt) if (re.match(r"[xyz]mm\d+$|k\d$", mt.group(0)) or mt.group(0) in x86.SUB) else mt.group(0),
                      ", ".join(ops))
        if max(list(vec.values()) + [0]) > 3 or len(gpr) > 4 or len(msk) > 2:
            continue
        if mnem in ("blendvps", "blendvpd", "pblendvb"):
            # The mask is xmm0 by definition; the disassembler prints it
            # as a third operand, which the assembler rejects. The model
            # takes the two-operand form (selector xmm0).
            text = ", ".join(text.split(", ")[:2])
        seen.setdefault((mnem, text), None)
    return list(seen)


def wide(text):
    return "zmm" in text or "k1" in text


def build(form_list, avx512):
    """One function per form: r8-r11 from xs, zmm/ymm 0-3 from vs (and k1,
    k2 from xs' low halves), the instruction, everything stored back."""
    d = tempfile.mkdtemp()
    src = [".intel_syntax noprefix", ".text"]
    for i, (mnem, text) in enumerate(form_list):
        load = (["vmovdqu32 zmm%d, [rsi + %d]" % (j, 64 * j) for j in range(4)] + ["kmovw k1, r8d", "kmovw k2, r9d"]
                if avx512 else ["vmovdqu ymm%d, [rsi + %d]" % (j, 64 * j) for j in range(4)])
        store = (["vmovdqu32 [rsi + %d], zmm%d" % (64 * j, j) for j in range(4)] if avx512
                 else ["vmovdqu [rsi + %d], ymm%d" % (64 * j, j) for j in range(4)])
        src += [f".global f{i}", f"f{i}:", "  mov r8, [rdi]", "  mov r9, [rdi + 8]", "  mov r10, [rdi + 16]",
                "  mov r11, [rdi + 24]"] + ["  " + x for x in load] + [f"  {mnem} {text}"] + ["  " + x for x in store] + [
                "  mov [rdi], r8", "  mov [rdi + 8], r9", "  mov [rdi + 16], r10", "  mov [rdi + 24], r11",
                "  vzeroupper", "  ret"]
    path = os.path.join(d, "forms.S")
    with open(path, "w") as f:
        f.write("\n".join(src) + "\n")
    lib = os.path.join(d, "forms.so")
    subprocess.run(["cc", "-shared", path, "-o", lib], check=True)
    return ctypes.CDLL(lib)


def model(mnem, text, xs, vs, avx512):
    m = x86.Machine({}, {})
    for r in x86.GPR:
        m.x[r] = BitVecVal(0, 64)
    for i, x in enumerate(xs):
        m.x[f"r{8 + i}"] = BitVecVal(x, 64)
    for i in range(32):
        m.v[i] = [BitVecVal(0, 32)] * 16
    for i in range(4):
        m.v[i] = [BitVecVal(vs[16 * i + l], 32) for l in range(16)] if avx512 else \
            [BitVecVal(vs[16 * i + l], 32) for l in range(8)] + [BitVecVal(0, 32)] * 8
    if avx512:
        m.k[1], m.k[2] = BitVecVal(xs[0] & 0xFFFF, 16), BitVecVal(xs[1] & 0xFFFF, 16)
    x86.step(m, 0, mnem, x86.split(text), 0)
    lanes = 16 if avx512 else 8
    return ([aarch64.concrete(m.x[f"r{8 + i}"]) for i in range(4)],
            [aarch64.concrete(m.v[i][l]) if l < lanes else vs[16 * i + l] for i in range(4) for l in range(16)])


def build_features(d):
    # CPUID and XGETBV describe the executing CPU, including under Intel
    # SDE; /proc/cpuinfo describes the host even when instructions emulate.
    src, so = os.path.join(d, "features.c"), os.path.join(d, "features.so")
    with open(src, "w") as f:
        f.write('int has_avx512(void) { __builtin_cpu_init(); return '
                '__builtin_cpu_supports("avx512f") && __builtin_cpu_supports("avx512vl"); }\n')
    subprocess.run(["cc", "-shared", "-fPIC", src, "-o", so], check=True)
    return so


def has_avx512():
    with tempfile.TemporaryDirectory() as d:
        return bool(ctypes.CDLL(build_features(d)).has_avx512())


def kernel_forms(isa):
    import prove_x86
    so = prove_x86.assemble(isa, False)
    return forms(x86.disassemble(so, x86.sections(so)[".text"][0], x86.text_end(so)))


def prepare(d):
    os.makedirs(d, exist_ok=True)
    manifest = {}
    for isa in FILES:
        fl = kernel_forms(isa)
        lib = build(fl, True)
        shutil.copyfile(lib._name, os.path.join(d, isa + ".so"))
        manifest[isa] = fl
    build_features(d)
    with open(os.path.join(d, "forms.json"), "w") as f:
        json.dump(manifest, f)
    print(f"Prepared {sum(map(len, manifest.values()))} instruction forms in {d}; execution requires AVX-512F and AVX-512VL.")


def main():
    args = sys.argv[1:]
    assert not args or (len(args) == 2 and args[0] in ("--prepare", "--prepared")), "usage: cross_check_x86.py [--prepare DIR | --prepared DIR]"
    if args and args[0] == "--prepare":
        prepare(os.path.abspath(args[1]))
        return
    prepared = os.path.abspath(args[1]) if args else None
    if prepared:
        avx512 = bool(ctypes.CDLL(os.path.join(prepared, "features.so")).has_avx512())
        assert avx512, "prepared instruction forms require AVX-512F and AVX-512VL (use Intel SDE or a capable CPU)"
        with open(os.path.join(prepared, "forms.json")) as f:
            manifest = json.load(f)
        assert set(manifest) == set(FILES), "prepare the current kernel forms again"
    else:
        avx512 = has_avx512()
    rounds = 200
    random.seed(0)
    total, skipped, bad = 0, 0, 0
    for isa in FILES:
        fl = manifest[isa] if prepared else kernel_forms(isa)
        if any(wide(t) for _, t in fl) and not avx512:
            # AVX-512VL forms can use xmm/ymm without a mask. Keep each
            # file together: its narrow forms may also require AVX-512.
            skipped += len(fl)
            continue
        lib = ctypes.CDLL(os.path.join(prepared, isa + ".so")) if prepared else build(fl, avx512)
        for i, (mnem, text) in enumerate(fl):
            f = getattr(lib, f"f{i}")
            for _ in range(rounds):
                xs = [random.getrandbits(64) for _ in range(4)]
                vs = [random.getrandbits(32) for _ in range(64)]
                if mnem in ("vpermt2d", "vpermi2d"):
                    # Index lanes in range, as the kernels' tables are.
                    k = 1 if mnem == "vpermt2d" else 0
                    vs[16 * k:16 * k + 16] = [random.getrandbits(5) for _ in range(16)]
                cx, cv = (ctypes.c_uint64 * 4)(*xs), (ctypes.c_uint32 * 64)(*vs)
                f(cx, cv)
                mx, mv = model(mnem, text, xs, vs, avx512)
                if list(cx) != mx or list(cv) != mv:
                    print(f"MISMATCH: {mnem} {text}: cpu {list(cx)} {list(cv)[:16]}, model {mx} {mv[:16]}")
                    bad += 1
                    break
            total += 1
    print(f"{total} instruction forms, {rounds} random states each: {'all agree' if not bad else f'{bad} disagree'}"
          + (f"; {skipped} forms skipped (no AVX-512 here)" if skipped else ""))
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
