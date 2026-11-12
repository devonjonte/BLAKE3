#!/usr/bin/env python3
"""Does a function's generated proof notice a missing instruction? For any function proved by prove_fn.sh.

    mutants_code.py NAME [JOBS]

One instruction at a time is replaced by a no-op in the lifter's rows (Lifted_NAME.lean.rows), the
program is written again from the rows (as prove_fn.sh wrote it) and `lake build Proof_NAME` must fail;
before that the function is tried on its contract's examples, which says at once whether the examples
see the change. The control: an unchanged copy, forced to check again, must be accepted.

An instruction whose removal the proof accepts is one the contract does not need: dead code, or a claim
the contract does not make. Each is printed, to be looked at."""
import os, re, shutil, signal, subprocess, sys, tempfile, time
from concurrent.futures import ThreadPoolExecutor
import odec

here = os.path.dirname(os.path.abspath(__file__))
name = sys.argv[1]
jobs = int(sys.argv[2]) if len(sys.argv) > 2 else 6
SRC, ROWS = "hasher.ode", f"Lifted_{name}.lean.rows"
LIMIT = 900
rows = [l.rstrip("\n").split("\t") for l in open(os.path.join(here, ROWS))]
clauses = odec.contracts_of(open(os.path.join(here, SRC)).read())[0][name]
CNAME = re.match(r"[\w.]+", next(r for w, r in clauses["head"] if w == "meets")).group(0)
EX = "Example_" + CNAME.split(".")[0].lower()
# the options prove_fn.sh gave gen_code.py: the checked entry's rows, the callees' code
more = [f"Lifted_{name}_checked.lean.rows"] if os.path.exists(os.path.join(here, f"Lifted_{name}_checked.lean.rows")) else []
codes = list(dict.fromkeys(odec.own[c["callee"]]["code"] for c in clauses.get("calls", [])))
codes.sort(key=lambda n: "import KCode" not in open(os.path.join(here, f"Code_{n}.lean")).read())
withs = [x for n in codes for x in ("--with", n + ("+k" if "import KCode" in open(os.path.join(here, f"Code_{n}.lean")).read() else ""))]
targets = [f"Proof_{name}"]

snap_dir = tempfile.mkdtemp(prefix="mut-code-snap-", dir=os.path.dirname(here))
snapshot = os.path.join(snap_dir, "w")
shutil.copytree(here, snapshot, symlinks=True, ignore=shutil.ignore_patterns("mut-*", "swap-*", "*.o"))
import atexit; atexit.register(lambda: shutil.rmtree(snap_dir, ignore_errors=True))


def run(k):
    """k = None: the control. Otherwise the k-th instruction becomes a no-op."""
    d = tempfile.mkdtemp(prefix="mut-code-", dir=os.path.dirname(here))
    start = time.time()
    try:
        w = os.path.join(d, "w")
        shutil.copytree(snapshot, w, symlinks=True)
        for dep in ("one", "spec"):
            os.symlink(os.path.join("..", dep), os.path.join(d, dep))      # the copy is one level deeper
        if k is None:
            with open(os.path.join(w, f"Proof_{name}.lean"), "a") as f: f.write("\n-- the control's copy\n")
            what = "the unchanged copy"
        else:
            at, nxt, ins = rows[k]
            what = f"0x{at}: {ins}"
            with open(os.path.join(w, ROWS), "w") as f:
                f.write("".join("\t".join(r if i != k else [at, nxt, ".nop"]) + "\n" for i, r in enumerate(rows)))
            g = subprocess.run([sys.executable, "gen_code.py", name, ROWS, f"Code_{name}.lean"] + more + withs, cwd=w, capture_output=True, text=True)
            assert g.returncode == 0, g.stderr
        tried = "no examples"
        if os.path.exists(os.path.join(w, EX + ".lean")):
            b = subprocess.run(["lake", "build", f"Code_{name}", EX, "Checks", "TrySem", "HasherOde"], cwd=w, capture_output=True, text=True)
            if b.returncode == 0:
                tr = subprocess.run([sys.executable, "try_fn.py", SRC, name, ROWS], cwd=w, capture_output=True, text=True)
                bad = [l for l in tr.stdout.splitlines() if "REFUTED" in l or "NO VERDICT" in l]
                tried = ("the examples: " + bad[0][:150]) if bad else "the examples see nothing"
            else:
                tried = "the examples do not build"
        pr = subprocess.Popen(["lake", "build"] + targets, cwd=w, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, start_new_session=True)
        try:
            out, _ = pr.communicate(timeout=LIMIT)
        except subprocess.TimeoutExpired:
            os.killpg(pr.pid, signal.SIGKILL); pr.communicate()
            return k, what, "NO VERDICT", time.time() - start, tried
        ok = pr.returncode == 0 and not re.search(r"error|sorry", out)
        return k, what, "ACCEPTED" if ok else "rejected", time.time() - start, tried
    finally:
        shutil.rmtree(d, ignore_errors=True)


_, what, verdict, secs, tried = run(None)
print(f"control: {verdict} in {secs:.0f} s ({tried})", flush=True)
if verdict != "ACCEPTED" or secs < 5:
    raise SystemExit("the control failed (or answered without checking): the audit proves nothing")
tally, seen = {}, {}
with ThreadPoolExecutor(jobs) as pool:
    for k, what, verdict, secs, tried in pool.map(run, range(len(rows))):
        tally[verdict] = tally.get(verdict, 0) + 1
        key = "refuted by an example" if "REFUTED" in tried or "NO VERDICT" in tried else "not seen by the examples"
        seen[key] = seen.get(key, 0) + 1
        print(f"{verdict:<10} {secs:4.0f} s  {what}\n{'':17}{tried}", flush=True)
print(f"{name}: {len(rows)} instructions, each in turn made a no-op: " + ", ".join(f"{n} {k}" for k, n in sorted(tally.items())) +
      "; " + ", ".join(f"{n} {k}" for k, n in sorted(seen.items())))
