#!/usr/bin/env python3
"""Everything the language's compiler proves, from the source to checked theorems, side by side.

    python3 prove_all.py            (prove_all.sh runs this; AUDIT=1 adds the audits)

What is checked, and what each label means, is said at the top of prove_all.sh. This is how it is run:

  - Each chain below (a function's proof, then its audit) runs in a copy of lang/ of its own, so chains run
    at once; JOBS chains at a time (a quarter of the processors unless said). A copy leaves out every
    proof's compiled form (hundreds of megabytes each), so a chain checks again whatever it rests on.
  - A copy holds the generated files as the tree has them (Code_*.lean, Proof_*.lean, Checked_*.lean); a
    chain writes its own function's again from the source. So a chain that calls another function by its
    contract uses that function's files as committed, and the last step compares every file a chain wrote
    with the tree's: "generated" fails if one differs (then a chain may have rested on a stale file).
  - The AArch64 steps (arm/) run in place, one after another, after the others have ended: arm/ is on
    another Lean version (the one Google's model is on), and both build the specification's package, each
    for its own version, in the same folder; side by side they overwrite each other's files (seen: "failed
    to read file .../HexText.olean, incompatible header"). levels-model runs in place.
  - SERIAL=1: every step in place, one after another, as before (for a machine short of memory, and the
    fallback where "generated" differs because another assembler lays the code out differently).

Output: the lines prove_all.sh always printed, in the same order, then "all checked" or the count."""
import filecmp, os, re, shutil, subprocess, sys, tempfile, threading, time
from concurrent.futures import ThreadPoolExecutor

HERE = os.path.dirname(os.path.abspath(__file__))
AUDIT = os.environ.get("AUDIT", "0") == "1"
SERIAL = os.environ.get("SERIAL", "0") == "1"
JOBS = int(os.environ.get("JOBS") or max(1, (os.cpu_count() or 4) // 4))
AJ = os.environ.get("AUDIT_JOBS", "16")                     # mutants at once inside one audit
# merge's audit asks the proof of every one of its 35 changes (false statements among them): all at once where there are processors
AJ_ALL = os.environ.get("AUDIT_JOBS") or str(max(16, min(36, (os.cpu_count() or 4) // 2)))
os.environ.setdefault("OBJDUMP", "llvm-objdump")
LV = "SOURCE=../levels/levels.ode ODEMOD=LevelsOde "
hexaudit = "1" if AUDIT else "0"


def fn(name, base, levels=False):
    return f"{LV if levels else ''}./prove_fn.sh {name} {base}"


def audit(name, levels=False):
    return f"{LV if levels else ''}python3 mutants_code.py {name} {AJ}"


# (label, folder, command, is it an audit). A chain: steps that share a copy of lang/, in order.
# A step with no label is a chain's preparation (what a later step of the chain reads), not reported.
CHAINS = [
    [("hex", "lang", f"MUTANTS={hexaudit} ./prove.sh", False)],
    [("merge", "lang", fn("merge", "0x60000"), False), ("audit-merge", "lang", f"python3 mutants_fn.py {AJ_ALL}", True)],
    [("push", "lang", fn("push", "0x70000"), False), ("audit-push", "lang", audit("push"), True)],
    [("merge_sse", "lang", fn("merge_sse", "0x90000"), False)],
    [("add-and-swap", "lang", "./swap.sh", False), ("audit-add", "lang", audit("add"), True)],
    [("merge_steps", "lang", fn("merge_steps", "0xA0000"), False), ("audit-steps", "lang", audit("merge_steps"), True)],
    [("levels-model", "levels", "python3 model.py 3000", False)],
    [("ladd", "lang", fn("ladd", "0xB0000", True), False), ("audit-ladd", "lang", audit("ladd", True), True)],
    [("lroot", "lang", fn("lroot", "0xC0000", True), False), ("audit-lroot", "lang", audit("lroot", True), True)],
    [("node_out", "lang", fn("node_out", "0xD0000", True), False), ("audit-node_out", "lang", audit("node_out", True), True)],
    [("pad", "lang", fn("pad", "0xE0000", True), False), ("audit-pad", "lang", audit("pad", True), True)],
    [("chunk_node", "lang", fn("chunk_node", "0xF0000", True), False), ("audit-chunk_node", "lang", audit("chunk_node", True), True)],
    [("hashl", "lang", fn("hashl", "0x40000", True), False),
     ("hash-bytes", "lang", 'lake build Meets_hashl_bytes > hashbytes.log 2>&1 && ! grep -q -E "error|sorry" hashbytes.log && grep -q "hashl_meets_bytes. depends on axioms" hashbytes.log', False),
     ("audit-hashl", "lang", audit("hashl", True), True)],
    [("adler32", "lang", "SOURCE=../experiments/adler32/adler32.ode ODEMOD=AdlerOde ./prove_fn.sh adler32 0x100000", False)],
    [("any-machine", "lang", 'lake build Meets_hex_bytes Meets_push_bytes Meets_merge_bytes UsableBytes > any.log 2>&1 && ! grep -q -E "error|sorry" any.log && [ "$(grep -c "_meets_bytes. depends on axioms" any.log)" = 4 ] && grep -q "usable_bytes. depends on axioms" any.log', False)],
    [(None, "lang", fn("push", "0x70000") + " && " + fn("merge", "0x60000"), False),
     ("direct", "lang", 'python3 direct_fn.py push Push.contract Push.byteContract 64 StackAsBytes Cv.opens Stack.opens && python3 direct_fn.py merge Merge.contract Merge.byteContract 256 MergeAsBytes Cv.opens Stack.opens Merge.merged_eq && lake build Direct_push Direct_merge > direct.log 2>&1 && ! grep -q -E "error|sorry" direct.log && grep -q "Direct_push.push_meets. depends on axioms" direct.log && grep -q "Direct_merge.merge_meets. depends on axioms" direct.log', False)],
    [(None, "lang", "python3 odec.py hasher.ode HasherOde.lean", False),
     ("hash-tried", "lang", 'lake build TrySem HasherOde HashContract > /dev/null 2>&1; lake env lean HashTry.lean > hashtry.log 2>&1 && grep -q "104 examples meet it, 0 do not" hashtry.log && grep -q "holds on 104" hashtry.log', False)],
    [("hex_neon", "arm", f"MUTANTS={hexaudit} ./prove_arm.sh", False), ("push-aarch64", "arm", f"MUTANTS={hexaudit} ./prove_arm_fn.sh", False)],
    [("audit-spec", "lang", f"python3 mutants_spec.py {AJ}", True)],
    [(None, "lang", "python3 odec.py hasher.ode HasherOde.lean", True), ("audit-hash", "lang", "python3 mutants_hash.py", True)],
]
ORDER = ["hex", "merge", "push", "merge_sse", "add-and-swap", "merge_steps", "levels-model", "ladd", "lroot", "node_out", "pad", "chunk_node", "hashl", "hash-bytes", "adler32",
         "any-machine", "direct", "hash-tried", "hex_neon", "push-aarch64",
         "audit-merge", "audit-push", "audit-add", "audit-steps", "audit-ladd", "audit-lroot", "audit-node_out", "audit-pad", "audit-chunk_node", "audit-hashl",
         "audit-spec", "audit-hash"]
GENERATED = re.compile(r"(Code|Proof|Checked)_\w+\.lean$")


def lab_copy(dest):
    """A copy of lang/ at dest/w, with the folders it reaches beside it; no proof's compiled form."""
    def unneeded(_, names):
        big = [n for n in names if re.match(r"(Proof|Direct|Checked|Meets)_", n) and not n.endswith(".lean")]
        return set(big) | set(shutil.ignore_patterns("mut-*", "swap-*", "par-*", "*.o", "prove_all.*.log")(_, names))
    shutil.copytree(os.path.join(HERE, "lang"), os.path.join(dest, "w"), symlinks=True, ignore=unneeded)
    for dep in ("one", "spec", "levels", "alg", "experiments"):
        os.symlink(os.path.join("..", dep), os.path.join(dest, dep))


results, differs, lock = {}, [], threading.Lock()
arm_lock = threading.Lock()


def run_step(label, cwd, command):
    start = time.time()
    with open(os.path.join(HERE, f"prove_all.{label or 'prepare'}.log"), "a" if label is None else "w") as log:
        ok = subprocess.run(command, shell=True, cwd=cwd, stdout=log, stderr=subprocess.STDOUT, stdin=subprocess.DEVNULL).returncode == 0
    return ok, time.time() - start


def run_chain(chain):
    chain = [s for s in chain if AUDIT or not s[3]]
    if not chain: return
    folder = chain[0][1]
    copy = None
    if folder == "lang" and not SERIAL:
        copy = tempfile.mkdtemp(prefix="par-", dir=HERE)
        lab_copy(copy)
        cwd = os.path.join(copy, "w")
    else:
        cwd = os.path.join(HERE, folder)
    guard = arm_lock if folder == "arm" else threading.Lock()
    try:
        with guard:
            alive = True
            for label, _, command, _ in chain:
                if alive:
                    ok, secs = run_step(label, cwd, command)
                    if not ok and copy:
                        # the copy goes with the chain: what Lean said in it stays, beside the step's own log
                        for f in sorted(os.listdir(cwd)):
                            if f.endswith(".build.log"):
                                shutil.copy(os.path.join(cwd, f), os.path.join(HERE, f"prove_all.{label or 'prepare'}.{f}"))
                else:
                    ok, secs = False, 0.0
                    with open(os.path.join(HERE, f"prove_all.{label or 'prepare'}.log"), "w") as log:
                        log.write("not run: the step before it in its chain did not pass\n")
                alive = alive and ok
                if label:
                    with lock: results[label] = (ok, secs, folder)
        if copy:
            # what the chain wrote of the generated files, beside the tree's
            for name in sorted(os.listdir(cwd)):
                mine, tree = os.path.join(cwd, name), os.path.join(HERE, "lang", name)
                if GENERATED.match(name) and os.path.exists(tree) and not filecmp.cmp(mine, tree, shallow=False):
                    with lock: differs.append(f"{name} ({chain[-1][0]})")
    finally:
        if copy and os.environ.get("KEEP") != "1": shutil.rmtree(copy, ignore_errors=True)


def main():
    start = time.time()
    if not SERIAL:
        # what every chain rests on, built once in place, so that each copy starts with it
        pre = subprocess.run("lake build Kernels AbiCall Checks TrySem StackLemmas BytesLemmas Lang Sem", shell=True, cwd=os.path.join(HERE, "lang"),
                             capture_output=True, text=True, stdin=subprocess.DEVNULL)
        if pre.returncode != 0:
            print("the common libraries do not build:\n" + (pre.stdout + pre.stderr)[-2000:]); return 1
    arm = [c for c in CHAINS if c[0][1] == "arm"]
    with ThreadPoolExecutor(1 if SERIAL else JOBS) as pool:
        list(pool.map(run_chain, [c for c in CHAINS if c not in arm]))
    for c in arm: run_chain(c)
    fails = 0
    for label in ORDER:
        if label not in results: continue
        ok, secs, folder = results[label]
        fails += not ok
        print(f"{label:<28} {folder + '/':<12} {secs:4.0f} s   {'checked' if ok else f'NOT checked (prove_all.{label}.log)'}")
        if label.startswith("audit-"):
            with open(os.path.join(HERE, f"prove_all.{label}.log")) as f:
                last = [l.rstrip("\n") for l in f if re.search(r"rejected|refuted by an example", l)]
            print("    " + (last[-1] if last else ""))
    if not SERIAL:
        if differs:
            fails += 1
            print("generated                    lang/           -     NOT checked: written again from the source, these differ from the tree's: " + ", ".join(sorted(differs)))
        else:
            print("generated                    lang/           -     checked: every generated file a chain wrote is the tree's")
    print(f"in {time.time() - start:.0f} s, {1 if SERIAL else JOBS} chain(s) at a time")
    print("all checked" if fails == 0 else f"{fails} NOT checked")
    return 0 if fails == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
