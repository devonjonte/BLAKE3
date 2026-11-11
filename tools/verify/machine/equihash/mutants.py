#!/usr/bin/env python3
"""Does the proof notice a changed instruction? One instruction of the compiled `Params::new` is
changed (in Code.lean's table and its lemma alike) and `lake build` must fail.
usage: mutants.py [--jobs N]"""
import argparse, concurrent.futures, pathlib, shutil, subprocess, tempfile
here = pathlib.Path(__file__).resolve().parent
MUTANTS = [
    (".and 32 (.reg .rax) (.imm 0x7)", ".and 32 (.reg .rax) (.imm 0x3)", "n a multiple of 4, not 8"),
    (".cmp 32 (.reg .rdx) (.imm 0x3)", ".cmp 32 (.reg .rdx) (.imm 0x4)", "k >= 4, not 3"),
    (".cmp 32 (.reg .rsi) (.imm 0x200)", ".cmp 32 (.reg .rsi) (.imm 0x201)", "n <= 513"),
    (".add 32 (.reg .rax) (.imm 0xFFFFFFFFFFFFFFF8)", ".add 32 (.reg .rax) (.imm 0xFFFFFFFFFFFFFFF9)", "collision bits from 7"),
    (".cmp 32 (.reg .rax) (.imm 0x10)", ".cmp 32 (.reg .rax) (.imm 0x11)", "collision bits up to 25"),
    (".lea32 .r8 .rcx 0x1", ".lea32 .r8 .rcx 0x2", "divides by k + 2"),
    (".test 32 (.reg .rdx) (.reg .rdx)", ".test 32 (.reg .rax) (.reg .rax)", "tests the quotient, not the remainder"),
    (".mov 32 (.mem .rdi 0x4) (.reg .rsi)", ".mov 32 (.mem .rdi 0x4) (.reg .rcx)", "stores k where n goes"),
    (".mov 32 (.reg .r8) (.imm 0x1)", ".mov 32 (.reg .r8) (.imm 0x2)", "a tag of 2"),
    (".jcc .ae 0x1D97", ".jcc .a 0x1D97", "k = n let through to the division"),
    (".xor 32 (.reg .rdx) (.reg .rdx)", ".xor 32 (.reg .rcx) (.reg .rcx)", "EDX not cleared before the division"),
]

def one(job):
    old, new, what = job
    with tempfile.TemporaryDirectory() as d:
        work = pathlib.Path(d) / "m"
        shutil.copytree(here, work, ignore=shutil.ignore_patterns(".lake", "build*.log"))
        text = (work / "Code.lean").read_text()
        if text.count(old) != 2:
            return "malformed", what, f"{old}: {text.count(old)} occurrences"
        (work / "Code.lean").write_text(text.replace(old, new))
        try:
            r = subprocess.run(["lake", "build"], cwd=work, capture_output=True, text=True, timeout=600)
        except subprocess.TimeoutExpired:
            return "rejected (time limit)", what, f"{old} -> {new}"
        bad = r.returncode != 0 or "sorryAx" in r.stdout
        return ("rejected" if bad else "ACCEPTED"), what, f"{old} -> {new}"

def main():
    p = argparse.ArgumentParser(); p.add_argument("--jobs", type=int, default=4); a = p.parse_args()
    counts = {}
    with concurrent.futures.ThreadPoolExecutor(a.jobs) as pool:
        for verdict, what, change in pool.map(one, MUTANTS):
            counts[verdict] = counts.get(verdict, 0) + 1
            print(f"{verdict}\t{what}\t{change}", flush=True)
    print(f"{len(MUTANTS)} changed instructions: " + ", ".join(f"{v} {k}" for k, v in sorted(counts.items())))

main()
