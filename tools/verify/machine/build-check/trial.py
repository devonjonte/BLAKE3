#!/usr/bin/env python3
"""The independent-checker trial, step 2 (on the workhorse).

    trial.py WORKDIR ARMLAB

Exports theorems of the AArch64 lab with lean4export and has nanoda (an independent checker of Lean
proofs, in Rust) check them, permitting Lean's three axioms and nothing else. Prints one line a case:
the export's size and time, the checker's exit and time. Every command runs under a time limit in its
own process group.
"""
import json, os, signal, subprocess, sys, time
from pathlib import Path

W, LAB = Path(sys.argv[1]), Path(sys.argv[2])
EXPORT = W / "lean4export/.lake/build/bin/lean4export"
NANODA = W / "nanoda/target/release/nanoda_bin"
ENV = dict(os.environ, PATH=os.path.expanduser("~/.elan/bin") + ":" + os.environ["PATH"])
THREE = ["propext", "Classical.choice", "Quot.sound"]


def run(cmd, cwd, limit, stdout=None):
    t = time.time()
    p = subprocess.Popen(cmd, cwd=cwd, env=ENV, stdin=subprocess.DEVNULL, stdout=stdout or subprocess.PIPE,
                         stderr=subprocess.PIPE if stdout else subprocess.STDOUT, start_new_session=True)
    try:
        out, err = p.communicate(timeout=limit)
        rc = p.returncode
    except subprocess.TimeoutExpired:
        os.killpg(p.pid, signal.SIGKILL)
        out, err = p.communicate()
        rc = "time limit"
    text = (out or b"") + (err or b"")
    return rc, time.time() - t, text.decode(errors="replace")


def export(name, module, const):
    out = W / f"{name}.ndjson"
    with open(out, "wb") as f:
        rc, secs, text = run(["lake", "env", str(EXPORT), module, "--", const], LAB, 900, stdout=f)
    lines = sum(1 for _ in open(out, "rb"))
    print(f"export {name}: rc={rc} {secs:.1f} s, {out.stat().st_size} bytes, {lines} lines {text.strip()[:300]}", flush=True)
    return out


def check(name, path, threads, axioms=THREE, hard=True):
    cfg = W / f"{name}-{threads}.json"
    with open(cfg, "w") as f:
        json.dump({"export_file_path": str(path), "use_stdin": False, "num_threads": threads,
                   "permitted_axioms": axioms, "unpermitted_axiom_hard_error": hard,
                   "nat_extension": True, "string_extension": True, "print_success_message": True}, f)
    rc, secs, text = run(["/usr/bin/time", "-f", "maxrss_kb=%M", str(NANODA), str(cfg)], W, 1800)
    print(f"check {name} threads={threads}: rc={rc} {secs:.1f} s: {' | '.join(text.strip().splitlines())[:600]}", flush=True)
    return rc


if __name__ == "__main__":
    a = export("push_arm_meets", "PushBytes", "push_arm_meets")
    check("push_arm_meets", a, 1)
    check("push_arm_meets", a, 16)
    check("push_arm_meets", a, 64)
    b = export("hex_neon_meets", "HexNeonBytes", "hex_neon_meets")
    check("hex_neon_meets", b, 16)
    print("done", flush=True)
