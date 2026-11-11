#!/usr/bin/env python3
"""Audit of the compiler's proof of `merge`: does a wrong program, or a wrong contract, fail?

First a control: an unchanged copy must be ACCEPTED (a copy that cannot build proves nothing).
Then, each in its own copy of this folder:
  - instructions changed one at a time in the lifter's rows, the proof text left as generated for
    the right code: Lean must reject it;
  - clauses of the source changed one at a time, the proof generated again from the changed source
    (the assembly is the same): the generator or Lean must reject it.
usage: mutants_fn.py [JOBS]   (after ./prove_fn.sh; run from this folder)"""
import os, shutil, subprocess, sys, tempfile, time
from concurrent.futures import ThreadPoolExecutor

here = os.path.dirname(os.path.abspath(__file__))
jobs = int(sys.argv[1]) if len(sys.argv) > 1 else 4
ROWS, SRC = "Lifted_merge.lean.rows", "hasher.ode"
code = [
    ("the PARENT flag is another bit", ".or 64 (.reg .rax) (.imm 0x4)", ".or 64 (.reg .rax) (.imm 0x8)", 1),
    ("the cell is one too high", ".sub 64 (.reg .rcx) (.imm 0x2)", ".sub 64 (.reg .rcx) (.imm 0x1)", 1),
    ("a value is 16 bytes, not 32", ".shl64 .rcx 5", ".shl64 .rcx 4", 1),
    ("the values start at 16, not 32", ".add 64 (.reg .rax) (.imm 0x20)", ".add 64 (.reg .rax) (.imm 0x10)", 1),
    ("the second half of a copy goes over the first", ".storev false .rcx 0x10 0", ".storev false .rcx 0x0 0", 1),
    ("the block's length is 32", ".mov 64 (.reg .rdx) (.imm 0x40)", ".mov 64 (.reg .rdx) (.imm 0x20)", 1),
    ("the counter is 1", ".mov 64 (.reg .rcx) (.imm 0x0)", ".mov 64 (.reg .rcx) (.imm 0x1)", 1),
    ("the length goes down by two", ".sub 64 (.reg .rax) (.imm 0x1)", ".sub 64 (.reg .rax) (.imm 0x2)", 1),
    ("the length is stored 8 bytes up", ".mov 64 (.mem .rcx 0x0) (.reg .rax)", ".mov 64 (.mem .rcx 0x8) (.reg .rax)", 1),
    ("the frame is 8 bytes smaller", ".sub 64 (.reg .rsp) (.imm 0x78)", ".sub 64 (.reg .rsp) (.imm 0x70)", 1),
    ("a caller's register comes back in another", ".pop .r14", ".pop .r13", 1),
    ("the kernel's first argument is the block", ".lea .rdi .rsp 0x40", ".lea .rdi .rsp 0x0", 1),
    ("the second kernel call's flags come from another slot", ".mov 64 (.reg .r8) (.mem .rsp 0x60)", ".mov 64 (.reg .r8) (.mem .rsp 0x68)", 2),
    ("the result is not the length", ".mov 64 (.reg .rax) (.reg .r15)", ".mov 64 (.reg .rax) (.reg .r14)", 3),
]
clause = [
    ("no `requires target >= 1` (then the trap can be reached)", "  requires target >= 1\n", ""),
    ("no `requires flags < 256` (then the two kernels read different flags)", "  requires flags < 256\n", ""),
    ("the result claimed is merged without the PARENT flag", "Stack.merged(k0, k1, low8(flags | PARENT), target, es0)) by Stack.merged_exit", "Stack.merged(k0, k1, low8(flags), target, es0)) by Stack.merged_exit"),
    ("the stack's region is said to be 1000 bytes", "region st[1792], key[32]", "region st[1000], key[32]"),
    ("the invariant forgets the key's second half", "    invariant vec[key + 16] == k1\n", ""),
    ("the invariant says pf is the flags alone", "    invariant pf == flags | PARENT\n", "    invariant pf == flags\n"),
    ("the loop is said to end with the stack as it began", "ensures  Stack.holds(st, result, Stack.merged(k0, k1, low8(flags | PARENT), target, es0)) by Stack.merged_exit", "ensures  Stack.holds(st, result, es0)"),
]


def nth_replace(text, old, new, n):
    at = -1
    for _ in range(n):
        at = text.index(old, at + 1)
    return text[:at] + new + text[at + len(old):]


def run(kind, what, old, new, n=1):
    parent = os.path.dirname(here)
    d = tempfile.mkdtemp(prefix="mut-merge-", dir=parent)     # beside this folder, so ../one is the same
    start = time.time()
    try:
        w = os.path.join(d, "w")
        shutil.copytree(here, w, symlinks=True, ignore=shutil.ignore_patterns("mut-*", "*.o"))
        os.symlink(os.path.join("..", "one"), os.path.join(d, "one"))     # the copy is one level deeper: its ../one is this
        if kind == "control":
            # a line added to the code's file, so the copy checks the proof again and does not answer from what was built
            with open(os.path.join(w, "Code_merge.lean"), "a") as f: f.write("\n-- the control's copy\n")
        if kind == "code":
            t = open(os.path.join(w, ROWS)).read(); assert old in t, old
            with open(os.path.join(w, ROWS), "w") as f: f.write(nth_replace(t, old, new, n))
            g = subprocess.run([sys.executable, "gen_code.py", "merge", ROWS, "Code_merge.lean"], cwd=w, capture_output=True, text=True)
        elif kind == "clause":
            t = open(os.path.join(w, SRC)).read(); assert t.count(old) == 1, old
            with open(os.path.join(w, SRC), "w") as f: f.write(t.replace(old, new))
            g = subprocess.run([sys.executable, "prove_fn.py", SRC, "merge", ROWS, "merge.layout", "Proof_merge.lean"], cwd=w, capture_output=True, text=True)
            if g.returncode != 0:
                return kind, what, "REJECTED by the generator", time.time() - start, (g.stderr.strip().splitlines() or [""])[-1][:110]
        try:
            r = subprocess.run(["lake", "build", "Proof_merge"], cwd=w, capture_output=True, text=True, timeout=900)
        except subprocess.TimeoutExpired:
            return kind, what, "NO VERDICT in 900 s", time.time() - start, ""
        out = r.stdout + r.stderr
        ok = r.returncode == 0 and "sorry" not in out
        first = next((l for l in out.splitlines() if "error" in l), "")[:110]
        return kind, what, "ACCEPTED" if ok else "REJECTED", time.time() - start, first
    finally:
        shutil.rmtree(d, ignore_errors=True)


k, w, verdict, secs, _ = run("control", "the unchanged copy", "", "")
print(f"control: {verdict} in {secs:.0f} s", flush=True)
if verdict != "ACCEPTED":
    raise SystemExit("the control failed: the audit proves nothing")
todo = [("code", *m) for m in code] + [("clause", *m, 1) for m in clause]
bad = 0
with ThreadPoolExecutor(jobs) as pool:
    for kind, what, verdict, secs, first in pool.map(lambda m: run(*m), todo):
        print(f"{verdict:<26} {secs:5.0f} s  {kind}: {what}" + (f"   [{first}]" if first else ""), flush=True)
        bad += verdict == "ACCEPTED"
n_rej = len(todo) - bad
print(f"{n_rej} of {len(todo)} not accepted ({len(code)} changed instructions, {len(clause)} changed clauses); {bad} accepted")
