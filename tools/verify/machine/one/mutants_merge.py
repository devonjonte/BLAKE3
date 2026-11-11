#!/usr/bin/env python3
"""Does the proof of `CvStack::merge` notice a changed instruction? One instruction of `merge` is changed
(in Merge.lean's table and in Code.lean's lemma alike) and `lake build MergeWhole` must fail.
usage: mutants_merge.py [--jobs N]"""
import argparse, concurrent.futures, pathlib, shutil, subprocess, sys, tempfile
here = pathlib.Path(__file__).resolve().parent
MUTANTS = [
    (".lea .r13 .rax 0xFFFFFFFFFFFFFFFE", ".lea .r13 .rax 0xFFFFFFFFFFFFFFFD", "the lower value from the wrong slot"),
    (".lea .rdi .rax 0xFFFFFFFFFFFFFFFF", ".lea .rdi .rax 0xFFFFFFFFFFFFFFFE", "the upper value from the lower slot"),
    (".shl64 .r13 5", ".shl64 .r13 4", "slots of sixteen bytes"),
    (".storev false .r13 0x10 1", ".storev false .r13 0x10 0", "the result's first half stored twice"),
    (".or 8 (.reg .rcx) (.imm 0x4)", ".or 8 (.reg .rcx) (.imm 0x0)", "no PARENT flag"),
    (".mov 32 (.reg .rdx) (.imm 0x40)", ".mov 32 (.reg .rdx) (.imm 0x20)", "a block length of 32"),
    (".xor 32 (.reg .rcx) (.reg .rcx)", ".or 32 (.reg .rcx) (.reg .rcx)", "the counter not cleared"),
    (".dec64 .r15", ".dec64 .rax", "the turns never counted down"),
    (".sub 64 (.reg .r15) (.reg .rdx)", ".add 64 (.reg .r15) (.reg .rdx)", "len + target turns"),
    (".pop .r12, 0x401B2", ".pop .r13, 0x401B2", "R12 not restored"),
    (".mov 8 (.mem .rsp 0xE0) (.imm 0x40)", ".mov 8 (.mem .rsp 0xE0) (.imm 0x41)", "a byte of the node's copy the kernel never reads"),
]
def one(job):
    old, new, what = job
    d = pathlib.Path(tempfile.mkdtemp(prefix="merge-mutant-"))
    for f in here.glob("*.lean"): shutil.copy(f, d / f.name)
    shutil.copy(here / "lean-toolchain", d / "lean-toolchain")
    lake = (here / "lakefile.toml").read_text()
    for rel in ('path = "../../lean"', 'srcDir = "../alg"'):
        if rel in lake:
            key, val = rel.split(" = "); lake = lake.replace(rel, f'{key} = "{(here / val.strip(chr(34))).resolve()}"')
    (d / "lakefile.toml").write_text(lake)
    for name in ("Merge.lean", "Code.lean"):
        t = (d / name).read_text(); assert t.count(old) == 1, (name, old); (d / name).write_text(t.replace(old, new))
    try:
        r = subprocess.run(["lake", "build", "MergeWhole"], cwd=d, capture_output=True, text=True, timeout=1500)
        log = r.stdout + r.stderr
        verdict = "ACCEPTED" if r.returncode == 0 else "malformed" if "error: Code.lean" in log else "rejected"
    except subprocess.TimeoutExpired:
        verdict = "rejected (no proof in 25 minutes)"
    shutil.rmtree(d)
    return verdict, what, f"{old} -> {new}"
def main():
    p = argparse.ArgumentParser(); p.add_argument("--jobs", type=int, default=3); a = p.parse_args()
    counts = {}
    with concurrent.futures.ThreadPoolExecutor(a.jobs) as pool:
        for verdict, what, change in pool.map(one, MUTANTS):
            counts[verdict] = counts.get(verdict, 0) + 1
            print(f"{verdict}\t{what}\t{change}", flush=True)
    print(f"{len(MUTANTS)} changed instructions: " + ", ".join(f"{v} {k}" for k, v in sorted(counts.items())))
main()
