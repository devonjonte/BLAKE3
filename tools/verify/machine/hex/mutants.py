#!/usr/bin/env python3
"""Does the proof of `to_hex` notice a changed instruction? One instruction of Code.lean is changed
(its table row and its lemma alike) and the build must fail. usage: mutants.py [--jobs N]"""
import argparse, concurrent.futures, pathlib, re, shutil, subprocess, sys, tempfile

here = pathlib.Path(__file__).resolve().parent
FILES = ["Bytes.lean", "Attr.lean", "X86.lean", "ByteLemmas.lean", "Regions.lean", "Code.lean", "Hex.lean", "lakefile.toml", "lean-toolchain"]

def mutants(text):
    out = []
    for at, ins, nxt in re.findall(r"^  \((0x[0-9A-F]+), (.+?), (0x[0-9A-F]+)\)[, ] ", text, re.M):
        new = []
        m = re.search(r"0x([0-9A-F]+)\)$", ins)          # a displacement or an immediate: one bit of it
        if m: new.append(ins[:m.start(1)] + f"{int(m.group(1), 16) ^ 1:X})")
        m = re.fullmatch(r"(\.shr \d+ \(.+\)) (\d+)", ins)
        if m: new.append(f"{m.group(1)} {int(m.group(2)) + 1}")
        if ".mems .rsp .rcx 2" in ins: new.append(ins.replace(".mems .rsp .rcx 2", ".mems .rsp .rcx 1"))
        if "(.memi .r8 .rdx)" in ins: new.append(ins.replace("(.memi .r8 .rdx)", "(.memi .rdi .rdx)"))
        if "(.reg .r8)" in ins and ins.startswith(".mov 8"): new.append(ins.replace("(.reg .r8)", "(.reg .rdi)"))
        if ins.startswith(".and "): new.append(".or " + ins[5:])
        if ins.startswith(".add 64"): new.append(ins.replace("(.imm 0x2)", "(.imm 0x4)"))
        m = re.fullmatch(r"\.loadv (\d) (.+)", ins)
        if m: new.append(f".loadv {(int(m.group(1)) + 1) % 3} {m.group(2)}")
        m = re.fullmatch(r"\.storev (.+) (\d)", ins)
        if m: new.append(f".storev {m.group(1)} {(int(m.group(2)) + 1) % 3}")
        if ins.startswith(".jcc .ne"): new.append(ins.replace(".ne", ".e"))
        if ins == ".mov 64 (.reg .rax) (.reg .rdi)": new.append(".mov 64 (.reg .rax) (.reg .rsi)")
        for n in new:
            if n == ins: continue
            changed = text.replace(f"({at}, {ins}, {nxt})", f"({at}, {n}, {nxt})").replace(
                f"prog T {at} = some ({ins}, {nxt})", f"prog T {at} = some ({n}, {nxt})")
            assert changed.count(n) >= 2, n
            out.append((f"{at}: {ins} -> {n}", changed))
    return out

def one(job):
    what, text = job
    d = pathlib.Path(tempfile.mkdtemp(prefix="hex-mutant-"))
    for f in FILES: shutil.copy(here / f, d / f)
    (d / "Code.lean").write_text(text)
    try:
        r = subprocess.run(["lake", "build", "Hex"], cwd=d, capture_output=True, text=True, timeout=600)
        log = r.stdout + r.stderr
        verdict = "ACCEPTED" if r.returncode == 0 else "malformed" if "error: Code.lean" in log else "rejected"
    except subprocess.TimeoutExpired:
        verdict = "rejected (no proof in ten minutes)"
    shutil.rmtree(d)
    return what, verdict

def main():
    p = argparse.ArgumentParser(); p.add_argument("--jobs", type=int, default=3); a = p.parse_args()
    jobs = mutants((here / "Code.lean").read_text()); counts = {}
    with concurrent.futures.ThreadPoolExecutor(a.jobs) as pool:
        for what, verdict in pool.map(one, jobs):
            counts[verdict] = counts.get(verdict, 0) + 1
            print(f"{verdict}\t{what}", flush=True)
    print(f"{len(jobs)} changed instructions: " + ", ".join(f"{v} {k}" for k, v in sorted(counts.items())))
    sys.exit(1 if counts.get("ACCEPTED") or counts.get("malformed") else 0)

main()
