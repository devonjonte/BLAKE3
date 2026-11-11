#!/usr/bin/env python3
"""Do the generated proofs notice a wrong program?

  code:   one instruction of a compiled function is changed (in Code_NAME.lean, table and lemma alike);
  rust:   the printed Rust is changed before rustc sees it (a wrong printer, or a wrong compiler), and
          make.py runs again on what rustc makes of it.
Every such change must make the build fail, except the ones marked `same`, which compute the same
function and must pass. usage: mutants.py --objdump PATH [--jobs N]"""
import argparse, concurrent.futures, pathlib, re, shutil, subprocess, sys, tempfile

here = pathlib.Path(__file__).resolve().parent
FILES = ["Bytes.lean", "Fold.lean", "Rule.lean", "Lang.lean", "Attr.lean", "X86.lean", "MemX.lean", "Run.lean",
         "make.py", "lean-toolchain"]

def code_mutants(text):
    """(description, new text) for one changed instruction each."""
    out = []
    rows = re.findall(r"^  \((0x[0-9A-F]+), (.+?), (0x[0-9A-F]+)\)[, ] ", text, re.M)
    for at, ins, nxt in rows:
        new = []
        m = re.fullmatch(r"\.(rol32 \.\w+|shl \d+ \(.+\)|shr \d+ \(.+\)) (\d+)", ins)
        if m: new.append(f".{m.group(1)} {int(m.group(2)) + 1}")
        for a, b in (("and", "or"), ("or", "xor"), ("xor", "add"), ("add", "xor")):
            if ins.startswith(f".{a} "): new.append(f".{b} " + ins[len(a) + 2:])
        m = re.fullmatch(r"(\..+ \(\.imm 0x)([0-9A-F]+)\)", ins)
        if m: new.append(f"{m.group(1)}{int(m.group(2), 16) ^ 0x10:X})")
        m = re.fullmatch(r"(\.lea32 .+ 0x)([0-9A-F]+)", ins)
        if m: new.append(f"{m.group(1)}{int(m.group(2), 16) ^ 0x10:X}")
        m = re.fullmatch(r"\.jcc \.(e|ne) (0x[0-9A-F]+)", ins)
        if m: new.append(f".jcc .{'ne' if m.group(1) == 'e' else 'e'} {m.group(2)}")
        if ins.startswith(".mov 32 (.memi"): new.append(ins.replace("(.reg .rax)", "(.reg .rdx)"))
        if ins.startswith(".mov 32 (.reg") and "(.memi" in ins: new.append(ins.replace(".mov 32", ".xor 32"))
        if ins == ".not 32 (.reg .rax)": new.append(".not 32 (.reg .rdx)")
        if ins in (".pop .rbp", ".push .rbp"): new.append(ins.replace("rbp", "rbx"))
        for n in new:
            if n != ins:
                changed = text.replace(f"({at}, {ins}, {nxt})", f"({at}, {n}, {nxt})").replace(
                    f"prog {at} = some ({ins}, {nxt})", f"prog {at} = some ({n}, {nxt})")
                assert changed.count(n) >= 2, n
                out.append((f"{at}: {ins} -> {n}", changed))
    return out

RUST = [  # (function, old, new, must the proof still pass?)
    ("rotxor", "a.rotate_left(5)", "a.rotate_left(6)", False),
    ("rotxor", "(a.rotate_left(5) ^ w)", "(w ^ a.rotate_left(5))", True),
    ("rotxor", "*word = a;", "*word = w;", False),
    ("addrot", "a.wrapping_add(w)", "a.wrapping_sub(w)", False),
    ("addrot", "a.wrapping_add(w)", "w.wrapping_add(a)", True),
    ("mix", "252645135u32", "252645134u32", False),
    ("mix", "(w >> 3)", "(w >> 2)", False),
    ("sum", "a.wrapping_add(w)", "a.wrapping_add(w) | 1", False),
    ("quarter", "2654435769u32", "2654435768u32", False),
    ("quarter", ".rotate_left(16)", ".rotate_right(16)", True),
    ("blend", "(a & w)", "(a | w)", False),
    ("invert", "(!a.wrapping_add(w.rotate_left(1)))", "a.wrapping_add(w.rotate_left(1))", False),
    ("shift", "(a >> 3)", "(a << 3)", False),
    ("shift", "for word in words.iter_mut()", "for word in words.iter_mut().skip(1)", False),
    ("sum", "for word in words.iter_mut()", "for word in words.iter_mut().rev()", False),
]

# Changed instructions that compute the same function, and why.
SAME = {
    ("Mix", ".or 32 (.reg .r9) (.reg .rdx) -> .xor 32 (.reg .r9) (.reg .rdx)"):
        "R9 holds bits of 0xF0F0F0F0 only and EDX bits of 0x0F0F0F0F only: or and xor agree",
}

def fresh(names, extra):
    d = pathlib.Path(tempfile.mkdtemp(prefix="gen-mutant-"))
    for f in FILES + extra: shutil.copy(here / f, d / f)
    return d

def build(d, target):
    r = subprocess.run(["lake", "build", target], cwd=d, capture_output=True, text=True)
    return r.returncode == 0, r.stdout + r.stderr

def one_code(job):
    cap, what, text = job
    d = fresh([cap], [f"Code_{cap}.lean", f"Proof_{cap}.lean", "lakefile.toml"])
    (d / f"Code_{cap}.lean").write_text(text)
    ok, log = build(d, f"Proof_{cap}")
    listing = f"Code_{cap}.lean" in log and "error" in log.split(f"Proof_{cap}.lean")[0]
    shutil.rmtree(d)
    return cap, what, ("ACCEPTED" if ok else "malformed" if listing else "rejected")

def one_rust(job, objdump):
    name, old, new, same = job
    d = fresh([], ["gen.rs", "lakefile.toml"])
    src = (d / "gen.rs").read_text()
    a = src.index(f"pub fn {name}("); b = src.index("\n}\n", a)
    assert src[a:b].count(old) == 1, (name, old)
    (d / "mutant.rs").write_text(src[:a] + src[a:b].replace(old, new) + src[b:])
    r = subprocess.run([sys.executable, "make.py", "--objdump", objdump, "--rust", "mutant.rs"], cwd=d, capture_output=True, text=True)
    if r.returncode != 0:
        verdict = "rejected (make.py cannot read the loop: " + (r.stderr.strip().splitlines() or ["?"])[-1][:60] + ")"
    else:
        ok, _ = build(d, f"Proof_{name.capitalize()}")
        verdict = "accepted" if ok else "rejected"
    shutil.rmtree(d)
    right = verdict.startswith("accepted") == same
    return name, f"{old} -> {new}", verdict + (" (the same function)" if same else ""), right

def main():
    p = argparse.ArgumentParser(); p.add_argument("--objdump", required=True); p.add_argument("--jobs", type=int, default=4)
    a = p.parse_args()
    jobs = []
    for f in sorted(here.glob("Code_*.lean")):
        cap = f.stem[5:]
        jobs += [(cap, what, text) for what, text in code_mutants(f.read_text())]
    bad = 0
    with concurrent.futures.ThreadPoolExecutor(a.jobs) as pool:
        counts = {}
        for cap, what, verdict in pool.map(one_code, jobs):
            counts[verdict] = counts.get(verdict, 0) + 1
            why = SAME.get((cap, what.split(": ", 1)[1]))
            if verdict == "ACCEPTED" and why: verdict = "accepted, the same function"
            counts[verdict] = counts.get(verdict, 0) + 1
            if verdict != "rejected": print(f"{verdict}\t{cap}\t{what}" + (f"\t({why})" if why else ""), flush=True)
        print(f"code: {len(jobs)} changed instructions: " + ", ".join(f"{v} {k}" for k, v in sorted(counts.items())), flush=True)
        bad += counts.get("ACCEPTED", 0) + counts.get("malformed", 0)
        for name, what, verdict, right in pool.map(lambda j: one_rust(j, a.objdump), RUST):
            print(f"{'ok ' if right else 'WRONG'}\t{verdict}\t{name}\t{what}", flush=True); bad += not right
    print("every wrong program was rejected" if not bad else f"{bad} WRONG")
    sys.exit(1 if bad else 0)

main()
