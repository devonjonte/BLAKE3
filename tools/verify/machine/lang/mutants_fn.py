#!/usr/bin/env python3
"""Audit of the compiler's proof of `merge`: does a wrong program, a wrong statement, or a missing invariant fail?

First a control: an unchanged copy, made to check the proof again, must be ACCEPTED (a copy that cannot
build proves nothing). Then, each in its own copy of this folder:
  - code: instructions changed one at a time in the lifter's rows, the proof text left as generated
    for the right code (`entry`: the same for the checked entry's instructions);
  - statement: the Lean statement a reader reads (Spec_merge.lean, Spec_stack.lean) changed to claim
    something false, the proof text left as it is;
  - clause: what the source gives the prover changed, and the proof generated again.
Each must be rejected, by Lean or by the generator, within the time limit.
usage: mutants_fn.py [JOBS]   (after ./prove_fn.sh; run from this folder)"""
import os, re, shutil, signal, subprocess, sys, tempfile, time
from concurrent.futures import ThreadPoolExecutor

here = os.path.dirname(os.path.abspath(__file__))
jobs = int(sys.argv[1]) if len(sys.argv) > 1 else 4
ROWS, ROWS2, SRC = "Lifted_merge.lean.rows", "Lifted_merge_checked.lean.rows", "hasher.ode"
LIMIT = 600     # seconds a check may take; the right proof takes about 100
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
entry = [
    ("the checked entry lets flags of 256 through", ".cmp 64 (.reg .rdx) (.imm 0x100)", ".cmp 64 (.reg .rdx) (.imm 0x101)"),
    ("the checked entry tests another argument", ".cmp 64 (.reg .r8) (.imm 0x1)", ".cmp 64 (.reg .rcx) (.imm 0x1)"),
    ("the checked entry refuses with 0", ".mov 64 (.reg .rax) (.imm 0xFFFFFFFFFFFFFFFF)", ".mov 64 (.reg .rax) (.imm 0x0)"),
    ("the checked entry jumps past the function's first instruction", ".jmp 0x60000", ".jmp 0x60001"),
]
statement = [
    ("the stack claimed is merged to target + 1", "Spec_merge.lean", "Stack.layout.turns st cvs (Merge.result k flags target cvs)", "Stack.layout.turns st cvs (Merge.result k flags (target + 1#64) cvs)"),
    ("`Merge.result` is the specification's merge to one value more", "Spec_merge.lean", "⟨flags.setWidth 32⟩ target.toNat cvs", "⟨flags.setWidth 32⟩ (target.toNat + 1) cvs"),
    ("the result is said to be one more than the count", "Spec_merge.lean", "result.toNat = (Merge.result k flags target cvs).length", "result.toNat = (Merge.result k flags target cvs).length + 1"),
    ("the stack is said to be left as it is", "Spec_merge.lean", "Stack.layout.turns st cvs (Merge.result k flags target cvs)", "Stack.layout.keeps st cvs"),
    ("168 bytes of stack are said to be enough", "Spec_merge.lean", "stack := 256#64", "stack := 168#64"),
    ("no `1 ≤ target` is asked (then a turn would read below the stack's first value)", "Spec_merge.lean", "1#64 ≤ target ∧ flags < 256#64", "flags < 256#64"),
    ("no `flags < 256` is asked (then the two kernels read different flags)", "Spec_merge.lean", "1#64 ≤ target ∧ flags < 256#64", "1#64 ≤ target"),
    ("the key is not mentioned", "Spec_merge.lean", "reads := [Cv.layout.keeps key k]", "reads := []"),
    ("the arguments are in another order", "Spec_merge.lean", "args := [st, key, flags, plat, target]", "args := [key, st, flags, plat, target]"),
    ("the stack is said to take 1000 bytes", "Spec_stack.lean", "⟨1792#64, Stack.At⟩", "⟨1000#64, Stack.At⟩"),
    ("the stack's values are said to be 16 bytes apart", "Spec_stack.lean", "st + 32#64 * BitVec.ofNat 64 cvs.length", "st + 16#64 * BitVec.ofNat 64 cvs.length"),
    ("a chaining value's second half is said to be at byte 8", "Spec_stack.lean", "Vec m (a + 16#64) v1", "Vec m (a + 8#64) v1"),
]
# what the source gives the prover: the line holding the first text is dropped (None) or the text replaced
clause = [
    ("the invariant forgets the count", "invariant len == Stack.count(now)", None),
    ("the invariant forgets what is left to merge", "invariant Merge.result(k, flags, target, now)", None),
    ("the invariant forgets the key", "invariant Cv.At(key, k)", None),
    ("the invariant says pf is the flags alone", "invariant pf == flags | PARENT", "invariant pf == flags"),
    ("the loop is said to end with another lemma's conclusion", "leave by Merge.exit", "leave by Stack.At.cells"),
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
        shutil.copytree(snapshot, w, symlinks=True)
        os.symlink(os.path.join("..", "one"), os.path.join(d, "one"))     # the copy is one level deeper: its ../one is this
        if kind == "control":
            # a line added to the proof's file, so the copy checks the proof again and does not answer from what was built
            with open(os.path.join(w, "Proof_merge.lean"), "a") as f: f.write("\n-- the control's copy\n")
        if kind == "statement":
            fname, old = old
            s = open(os.path.join(w, fname)).read(); assert s.count(old) >= 1, old
            with open(os.path.join(w, fname), "w") as f: f.write(s.replace(old, new, 1))
        if kind == "code":
            t = open(os.path.join(w, ROWS)).read(); assert old in t, old
            with open(os.path.join(w, ROWS), "w") as f: f.write(nth_replace(t, old, new, n))
            g = subprocess.run([sys.executable, "gen_code.py", "merge", ROWS, "Code_merge.lean", ROWS2], cwd=w, capture_output=True, text=True)
        elif kind == "entry":
            t = open(os.path.join(w, ROWS2)).read(); assert old in t, old
            with open(os.path.join(w, ROWS2), "w") as f: f.write(t.replace(old, new, 1))
            g = subprocess.run([sys.executable, "gen_code.py", "merge", ROWS, "Code_merge.lean", ROWS2], cwd=w, capture_output=True, text=True)
        elif kind == "clause":
            lines = open(os.path.join(w, SRC)).read().split("\n")
            at = [i for i, l in enumerate(lines) if old in l]; assert len(at) == 1, old
            if new is None: del lines[at[0]]
            else: lines[at[0]] = lines[at[0]].replace(old, new)
            with open(os.path.join(w, SRC), "w") as f: f.write("\n".join(lines))
            g = subprocess.run([sys.executable, "prove_fn.py", SRC, "merge", ROWS, "merge.layout", "Proof_merge.lean"], cwd=w, capture_output=True, text=True)
            if g.returncode != 0:
                return kind, what, "REJECTED by the generator", time.time() - start, (g.stderr.strip().splitlines() or [""])[-1][:110]
        # first the quick answer: run the function on its examples and compare with the contract
        tried = "the examples were not run"
        b = subprocess.run(["lake", "build", "Code_merge", "Example_merge", "Checks", "TrySem", "HasherOde"], cwd=w, capture_output=True, text=True)
        if b.returncode == 0:
            tr = subprocess.run([sys.executable, "try_fn.py", SRC, "merge", ROWS], cwd=w, capture_output=True, text=True)
            # what differs from the unchanged version's answers, example by example (BASE is the control's)
            now = classes(tr.stdout)
            if kind == "control":
                BASE.update(now)
            diff = [line for i, (c, line) in sorted(now.items()) if BASE.get(i, (c,))[0] != c] + [f"example {i}: no longer answered" for i in sorted(BASE) if i not in now]
            tried = diff[0] if diff else "every example answers as for the unchanged version"
        else:
            tried = "the statement no longer fits the examples or the lemmas (it does not build)"
        tried_secs = time.time() - start
        # its own process group, so a check that runs out of time is stopped with its children (lake's lean)
        pr = subprocess.Popen(["lake", "build", "Proof_merge", "Checked_merge"], cwd=w, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, start_new_session=True)
        try:
            out, _ = pr.communicate(timeout=LIMIT)
        except subprocess.TimeoutExpired:
            os.killpg(pr.pid, signal.SIGKILL); pr.communicate()
            return kind, what, f"NO VERDICT in {LIMIT} s", time.time() - start, f"tried in {tried_secs:.0f} s: {tried}"
        ok = pr.returncode == 0 and "sorry" not in out
        return kind, what, "ACCEPTED" if ok else "REJECTED", time.time() - start, f"tried in {tried_secs:.0f} s: {tried}"
    finally:
        shutil.rmtree(d, ignore_errors=True)


BASE = {}
def classes(out):
    """example number -> (meets | refuted | not an example | no verdict, its line)"""
    r = {}
    for l in out.splitlines():
        m = re.match(r"example (\d+): (.*)", l)
        if m:
            c = "meets" if m.group(2).startswith("meets") else "refuted" if "REFUTED" in l else "not an example" if "NOT AN EXAMPLE" in l else "no verdict"
            r[int(m.group(1))] = (c, l)
    return r


# one copy of this folder as it is now: every check starts from it, whatever is edited here meanwhile
snap_dir = tempfile.mkdtemp(prefix="mut-merge-snap-", dir=os.path.dirname(here))
snapshot = os.path.join(snap_dir, "w")
shutil.copytree(here, snapshot, symlinks=True, ignore=shutil.ignore_patterns("mut-*", "*.o"))
import atexit; atexit.register(lambda: shutil.rmtree(snap_dir, ignore_errors=True))
k, w, verdict, secs, _ = run("control", "the unchanged copy", "", "")
print(f"control: {verdict} in {secs:.0f} s ({_})", flush=True)
if verdict != "ACCEPTED" or secs < 20:
    raise SystemExit("the control failed (or answered without checking): the audit proves nothing")
todo = [("code", *m) for m in code] + [("entry", *m, 1) for m in entry] + [("statement", what, (fname, old), new, 1) for what, fname, old, new in statement] + [("clause", *m, 1) for m in clause]
tally, blame = {}, {}
with ThreadPoolExecutor(jobs) as pool:
    for kind, what, verdict, secs, first in pool.map(lambda m: run(*m), todo):
        print(f"{verdict:<10} {secs:4.0f} s  {kind}: {what}\n{'':17}{first}", flush=True)
        key = "accepted" if verdict == "ACCEPTED" else "no verdict" if verdict.startswith("NO") else "rejected"
        tally[key] = tally.get(key, 0) + 1
        blame[kind] = blame.get(kind, []) + ["compiler" if "the code the compiler made is wrong" in first else "source or contract" if "the source or the contract is wrong" in first
                                              else "no longer an example" if "NOT AN EXAMPLE" in first else "does not build" if "does not build" in first else "not refuted"]
print(f"{len(code)} changed instructions, {len(entry)} changed instructions of the checked entry, {len(statement)} false statements and {len(clause)} changed clauses: " + ", ".join(f"{n} {k}" for k, n in sorted(tally.items())))
print("what trying the examples said of each kind (before any proof was checked):")
for kind, vs in blame.items():
    print(f"  {kind}: " + ", ".join(f"{vs.count(v)} {v}" for v in sorted(set(vs))))
