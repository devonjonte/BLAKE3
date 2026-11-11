#!/usr/bin/env python3
"""Does the generated proof of `hex` notice a changed instruction? One instruction is changed in
Code_hex.lean (the table and its lemma alike) and `lake build Proof_hex` must fail.
usage: mutants_hex.py [--jobs N]"""
import argparse, concurrent.futures, pathlib, shutil, subprocess, tempfile
here = pathlib.Path(__file__).resolve().parent
MUTANTS = [  # (address, old, new, what)
    ("5002E", ".psrlw 2 4", ".psrlw 2 3", "the high bits shifted by three"),
    ("50033", ".pand 2 (.x 5)", ".pand 2 (.x 6)", "the high bits masked with nines"),
    ("50037", ".pand 0 (.x 5)", ".pand 0 (.x 7)", "the low bits masked with 39s"),
    ("5003F", ".punpcklbw 3 (.x 0)", ".punpckhbw 3 (.x 0)", "the high eight bytes twice"),
    ("50009", "0x0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F#128", "0x0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F07#128", "one byte's mask is 7"),
    ("50011", "0x09090909090909090909090909090909#128", "0x0909090909090909090909090909090A#128", "one byte's ten is a digit"),
    ("50019", "0x27272727272727272727272727272727#128", "0x27272727272727272727272727272707#128", "one byte's letters are capitals"),
    ("50021", "0x30303030303030303030303030303030#128", "0x30303030303030303030303030303031#128", "one byte's zero is '1'"),
    ("50000", ".movv false 0 (.m .rsi 0x0)", ".movv false 0 (.m .rsi 0x1)", "the hash read from its second byte"),
    ("50004", ".movv false 1 (.m .rsi 0x10)", ".movv false 1 (.m .rsi 0x0)", "the first half twice"),
]

def one(job):
    at, old, new, what = job
    with tempfile.TemporaryDirectory(dir=here.parent) as d:
        work = pathlib.Path(d) / "m"
        shutil.copytree(here, work, ignore=shutil.ignore_patterns(".lake", "bench", "*.log"))
        (pathlib.Path(d) / "one").symlink_to((here.parent / "one").resolve())     # the machine model, by its relative path
        text = (work / "Code_hex.lean").read_text()
        if at is not None:
            lines = [l for l in text.split("\n") if f"0x{at}," in l or f"at_{at} " in l]
            if len(lines) != 2 or any(old not in l for l in lines):
                return "malformed", what, f"{at}: {old}"
            for l in lines:
                text = text.replace(l, l.replace(old, new))
            (work / "Code_hex.lean").write_text(text)
        try:
            r = subprocess.run(["lake", "build", "Proof_hex"], cwd=work, capture_output=True, text=True, timeout=900)
        except subprocess.TimeoutExpired:
            return "rejected (time limit)", what, f"{at}: {old} -> {new}"
        bad = r.returncode != 0 or "sorryAx" in r.stdout
        return ("rejected" if bad else "ACCEPTED"), what, f"{at}: {old} -> {new}"

def main():
    p = argparse.ArgumentParser(); p.add_argument("--jobs", type=int, default=3); a = p.parse_args()
    # The control: the unchanged copy must build, or "rejected" means nothing.
    control = one((None, "", "", "the unchanged code"))
    assert control[0] == "ACCEPTED", f"the unchanged proof does not build in a copy: {control}"
    print("control: the unchanged code is accepted", flush=True)
    counts = {}
    with concurrent.futures.ThreadPoolExecutor(a.jobs) as pool:
        for verdict, what, change in pool.map(one, MUTANTS):
            counts[verdict] = counts.get(verdict, 0) + 1
            print(f"{verdict}\t{what}\t{change}", flush=True)
    print(f"{len(MUTANTS)} changed instructions: " + ", ".join(f"{v} {k}" for k, v in sorted(counts.items())))

main()
