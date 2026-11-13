#!/usr/bin/env python3
"""Does a function's generated proof notice a missing instruction? For any function proved by prove_fn.sh.

    [SOURCE=FILE.ode ODEMOD=Module] mutants_code.py NAME [JOBS]      (as prove_fn.sh: hasher.ode and HasherOde unless said)
    LIMIT=SECONDS: the time one copy may take (900 unless said; `hashl` asked of every change needs more)

One instruction at a time is replaced by a no-op in the lifter's rows (Lifted_NAME.lean.rows) and the
program is written again from the rows (as prove_fn.sh wrote it). The changed function is first tried on
its contract's examples: one that refutes it settles it in seconds, and the proof is not asked (FULL=1 asks
the proof of every change all the same: how many the theorem refuses by itself, minutes more). Where the
examples see nothing, `lake build Proof_NAME` must fail. The control: an unchanged copy, forced to check
again, must be accepted.

An instruction whose removal the proof accepts is one the contract does not need: dead code, or a claim
the contract does not make. Each is printed, to be looked at."""
import os, re, shutil, signal, subprocess, sys, tempfile, time
from concurrent.futures import ThreadPoolExecutor
import odec

here = os.path.dirname(os.path.abspath(__file__))
name = sys.argv[1]
jobs = int(sys.argv[2]) if len(sys.argv) > 2 else 12
FULL = os.environ.get("FULL") == "1"
SRC, ROWS = os.path.abspath(os.path.join(here, os.environ.get("SOURCE", "hasher.ode"))), f"Lifted_{name}.lean.rows"
ODEMOD = os.environ.get("ODEMOD", "HasherOde")
LIMIT = int(os.environ.get("LIMIT", "900"))  # seconds for one copy; a proof that calls many needs more
rows = [l.rstrip("\n").split("\t") for l in open(os.path.join(here, ROWS))]
clauses = odec.contracts_of(open(SRC).read())[0][name]
CNAME = re.match(r"[\w.]+", next(r for w, r in clauses["head"] if w == "meets")).group(0)
EX = "Example_" + CNAME.split(".")[0].lower()
# the options prove_fn.sh gave gen_code.py: the checked entry's rows, the callees' code
more = [f"Lifted_{name}_checked.lean.rows"] if os.path.exists(os.path.join(here, f"Lifted_{name}_checked.lean.rows")) else []
import fn_args
withs = fn_args.code_args(SRC, name, here)
targets = [f"Proof_{name}"]

snap_dir = tempfile.mkdtemp(prefix="mut-code-snap-", dir=os.path.dirname(here))
snapshot = os.path.join(snap_dir, "w")
# A proof's compiled form is hundreds of megabytes: the copies take only those this function's proof imports
# (its callees' theorems), not every function's.
def proofs_under(mod, seen):
    """The proofs a module imports, and theirs: a callee's theorem rests on its own callees' theorems."""
    path = os.path.join(here, mod + ".lean")
    if os.path.exists(path):
        for imp in re.findall(r"^import (\w+)", open(path).read(), re.M):
            if imp not in seen:
                seen.add(imp); proofs_under(imp, seen)
    return seen
KEEP = {m for m in proofs_under(f"Proof_{name}", set()) if m.startswith("Proof_")}
def unneeded(_, names):
    big = [n for n in names if re.match(r"(Proof|Direct|Checked|Meets)_", n) and not n.endswith(".lean") and n.split(".")[0] not in KEEP]
    return set(big) | set(shutil.ignore_patterns("mut-*", "swap-*", "par-*", "*.o")(_, names))
shutil.copytree(here, snapshot, symlinks=True, ignore=unneeded)
# The source as Lean reads it, written again from the source: a module left by an earlier run may be of
# another source (the examples then do not run, and say so only in a line nobody reads).
subprocess.run([sys.executable, "odec.py", SRC, ODEMOD + ".lean"], cwd=snapshot, check=True, capture_output=True)
import atexit; atexit.register(lambda: shutil.rmtree(snap_dir, ignore_errors=True))


running, copies = set(), set()   # the process groups of the commands under way; the copies not yet removed
stopping = False


def call(args, cwd, limit=None):
    """Run a command in a session of its own, known to `stopped`: (exit status or None at the limit, output)."""
    if stopping:
        return 1, "stopped"
    pr = subprocess.Popen(args, cwd=cwd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, start_new_session=True)
    running.add(pr.pid)
    try:
        out, _ = pr.communicate(timeout=limit)
        return pr.returncode, out
    except subprocess.TimeoutExpired:
        os.killpg(pr.pid, signal.SIGKILL); pr.communicate()
        return None, ""
    finally:
        running.discard(pr.pid)


def run(k):
    if stopping:
        return k, "", "stopped", 0, ""
    """k = None: the control. Otherwise the k-th instruction becomes a no-op."""
    d = tempfile.mkdtemp(prefix="mut-code-", dir=os.path.dirname(here))
    copies.add(d)
    start = time.time()
    try:
        w = os.path.join(d, "w")
        shutil.copytree(snapshot, w, symlinks=True)
        for dep in ("one", "spec", "experiments"):
            os.symlink(os.path.join("..", dep), os.path.join(d, dep))      # the copy is one level deeper
        if k is None:
            with open(os.path.join(w, f"Proof_{name}.lean"), "a") as f: f.write("\n-- the control's copy\n")
            what = "the unchanged copy"
        else:
            at, nxt, ins = rows[k]
            what = f"0x{at}: {ins}"
            with open(os.path.join(w, ROWS), "w") as f:
                f.write("".join("\t".join(r if i != k else [at, nxt, ".nop"]) + "\n" for i, r in enumerate(rows)))
            rc, out = call([sys.executable, "gen_code.py", name, ROWS, f"Code_{name}.lean"] + more + withs, w)
            assert rc == 0 or stopping, out
        tried = "no examples"
        if os.path.exists(os.path.join(w, EX + ".lean")):
            rc, _ = call(["lake", "build", f"Code_{name}"] + [f"Code_{s}" for s in fn_args.standins(SRC, name)] + [EX, "Checks", "TrySem", ODEMOD], w)
            if rc == 0:
                _, tried_out = call([sys.executable, "try_fn.py", SRC, name, ROWS], w)
                bad = [l for l in tried_out.splitlines() if "REFUTED" in l or "NO VERDICT" in l]
                ran = re.search(r"^tried: (\d+) meet", tried_out, re.M)
                if not bad and not (ran and int(ran.group(1)) > 0) and not stopping:
                    tried = "the examples DID NOT RUN: " + " ".join(tried_out.split())[-200:]
                    return k, what, "NO VERDICT", time.time() - start, tried
                tried = ("the examples: " + bad[0][:150]) if bad else "the examples see nothing"
                if bad and k is not None and not FULL:
                    return k, what, "refuted", time.time() - start, tried
            elif not stopping:
                return k, what, "NO VERDICT", time.time() - start, "the examples DO NOT BUILD"
        rc, out = call(["lake", "build"] + targets, w, LIMIT)
        if rc is None:
            return k, what, "NO VERDICT", time.time() - start, tried
        ok = rc == 0 and not re.search(r"error|sorry", out)
        return k, what, "ACCEPTED" if ok else "rejected", time.time() - start, tried
    finally:
        shutil.rmtree(d, ignore_errors=True)
        copies.discard(d)


def stopped(signum, frame):
    """Stopped from outside: the commands under way (each a session of its own) go too, and the copies."""
    global stopping
    stopping = True
    for pid in list(running):
        try: os.killpg(pid, signal.SIGKILL)
        except ProcessLookupError: pass
    for _ in range(3):                      # a build just killed may still be writing: look again
        time.sleep(1)
        for d in list(copies):
            shutil.rmtree(d, ignore_errors=True)
    os._exit(143)


signal.signal(signal.SIGTERM, stopped)
signal.signal(signal.SIGINT, stopped)
tally, seen = {}, {}
with ThreadPoolExecutor(jobs) as pool:
    # the control runs beside the changes (it is the longest: the whole proof, accepted); its line comes first
    for k, what, verdict, secs, tried in pool.map(run, [None] + list(range(len(rows)))):
        if k is None:
            print(f"control: {verdict} in {secs:.0f} s ({tried.replace('the examples see nothing', 'the examples meet the contract')})", flush=True)
            if verdict != "ACCEPTED" or secs < 5:
                pool.shutdown(wait=False, cancel_futures=True)
                raise SystemExit("the control failed (or answered without checking): the audit proves nothing")
            continue
        tally[verdict] = tally.get(verdict, 0) + 1
        key = "refuted by an example" if "REFUTED" in tried or "NO VERDICT" in tried else "not seen by the examples"
        seen[key] = seen.get(key, 0) + 1
        print(f"{verdict:<10} {secs:4.0f} s  {what}\n{'':17}{tried}", flush=True)
WORDS = {"refuted": "refuted by an example (the proof not asked)", "rejected": "rejected by the proof"}
print(f"{name}: {len(rows)} instructions, each in turn made a no-op: " + ", ".join(f"{n} {WORDS.get(k, k)}" for k, n in sorted(tally.items())) +
      ("; " + ", ".join(f"{n} {k}" for k, n in sorted(seen.items())) if FULL else ""))
