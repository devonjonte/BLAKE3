#!/usr/bin/env python3
"""Does the proof of `hex` notice a changed instruction or a false statement? One instruction is changed in
Code_hex.lean (the table and its lemma alike), or one line of what is claimed (Spec_hex.lean, Spec_bytes.lean,
the theorem's own line), and `lake build Meets_hex` must fail. The control: the unchanged copy, built afresh,
must be accepted.
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

STATEMENTS = [  # (file, old, new, what)
    ("../spec/HexText.lean", "[char (b >>> 4), char (b &&& 15#8)]", "[char (b &&& 15#8), char (b >>> 4)]", "a byte's low four bits come first"),
    ("../spec/HexText.lean", "then n + 0x30#8 else n + 0x57#8", "then n + 0x30#8 else n + 0x37#8", "the letters are capitals"),
    ("../spec/HexText.lean", "if n < 10#8 then", "if n < 11#8 then", "ten is written as a digit"),
    ("Spec_hex.lean", "(Bytes.layout 64).fills out (Hex.text hash)", "(Bytes.layout 64).fills out (Hex.text hash.reverse)", "the hash is written backwards"),
    ("Spec_hex.lean", "(Bytes.layout 64).fills out (Hex.text hash)", "(Bytes.layout 63).fills out (Hex.text hash)", "only 63 bytes may change"),
    ("Spec_hex.lean", "reads := [(Bytes.layout 32).keeps inp hash]", "reads := [(Bytes.layout 31).keeps inp hash]", "the hash is 31 bytes"),
    ("Spec_hex.lean", "args := [out, inp]", "args := [inp, out]", "the arguments the other way round"),
    ("Spec_hex.lean", "returns := fun _ => True", "returns := fun r => r = 0#64", "it returns zero"),
    ("Meets_hex.lean", "Abi.MeetsQuietly Code_hex.prog 0x50000", "Abi.MeetsQuietly Code_hex.prog 0x50004", "it is entered at its second instruction"),
    ("Meets_hex.lean", "(fun hash : List (BitVec 8) => Hex.contract out inp hash)", "(fun hash : List (BitVec 8) => Hex.contract out (inp + (hash.headD 0#8).zeroExtend 64) hash)", "the hash's place depends on the hash"),
    ("Spec_bytes.lean", "m (a + BitVec.ofNat 64 i) = some bs[i]", "m (a + BitVec.ofNat 64 (i + 1)) = some bs[i]", "bytes are in memory one place later"),
]

def one(job):
    if len(job) == 4 and job[0] is not None and job[0].endswith(".lean"):
        return statement(job)
    at, old, new, what = job
    with tempfile.TemporaryDirectory(dir=here.parent) as d:
        work = pathlib.Path(d) / "m"
        shutil.copytree(here, work, ignore=shutil.ignore_patterns(".lake", "bench", "*.log"))
        (pathlib.Path(d) / "one").symlink_to((here.parent / "one").resolve())     # the machine model, by its relative path
        (pathlib.Path(d) / "spec").symlink_to((here.parent / "spec").resolve())   # and the shared specification
        text = (work / "Code_hex.lean").read_text()
        if at is not None:
            lines = [l for l in text.split("\n") if f"0x{at}," in l or f"at_{at} " in l]
            if len(lines) != 2 or any(old not in l for l in lines):
                return "malformed", what, f"{at}: {old}"
            for l in lines:
                text = text.replace(l, l.replace(old, new))
            (work / "Code_hex.lean").write_text(text)
        try:
            r = subprocess.run(["lake", "build", "Meets_hex"], cwd=work, capture_output=True, text=True, timeout=900)
        except subprocess.TimeoutExpired:
            return "rejected (time limit)", what, f"{at}: {old} -> {new}"
        bad = r.returncode != 0 or "sorryAx" in r.stdout
        return ("rejected" if bad else "ACCEPTED"), what, f"{at}: {old} -> {new}"

def statement(job):
    file, old, new, what = job
    with tempfile.TemporaryDirectory(dir=here.parent) as d:
        work = pathlib.Path(d) / "m"
        shutil.copytree(here, work, ignore=shutil.ignore_patterns(".lake", "bench", "*.log"))
        (pathlib.Path(d) / "one").symlink_to((here.parent / "one").resolve())
        if file.startswith("../spec/"):      # a change of the shared specification: in a copy of it, never in place
            shutil.copytree(here.parent / "spec", pathlib.Path(d) / "spec", ignore=shutil.ignore_patterns(".lake"))
        else:
            (pathlib.Path(d) / "spec").symlink_to((here.parent / "spec").resolve())
        text = (work / file).read_text()
        if file.startswith("../spec/"):      # without the specification's own example, so that the machine proof is what must object
            text = text[:text.index("/-- For example")]
        if text.count(old) != 1:
            return "malformed", what, f"{file}: {old}"
        (work / file).write_text(text.replace(old, new))
        try:
            r = subprocess.run(["lake", "build", "Meets_hex"], cwd=work, capture_output=True, text=True, timeout=900)
        except subprocess.TimeoutExpired:
            return "rejected (time limit)", what, f"{file}: {old} -> {new}"
        bad = r.returncode != 0 or "sorryAx" in r.stdout
        return ("rejected" if bad else "ACCEPTED"), what, f"{file}: {new}"

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
    counts = {}
    with concurrent.futures.ThreadPoolExecutor(a.jobs) as pool:
        for verdict, what, change in pool.map(one, STATEMENTS):
            counts[verdict] = counts.get(verdict, 0) + 1
            print(f"{verdict}\t{what}\t{change}", flush=True)
    print(f"{len(STATEMENTS)} false statements: " + ", ".join(f"{v} {k}" for k, v in sorted(counts.items())))

main()
