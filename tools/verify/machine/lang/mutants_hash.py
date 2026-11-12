#!/usr/bin/env python3
"""Do the examples of `hash` (HashTry.lean) notice a wrong source? In a copy of this folder one line of
`hash` in hasher.ode is changed, the source is read again, and the examples (nine lengths, three
platforms) are run. A wrong source must fail some; the control, the unchanged source, must meet all.
This audits a test, not a proof: `hash` has no theorem yet.

usage: mutants_hash.py"""
import pathlib, shutil, subprocess, sys, tempfile
here = pathlib.Path(__file__).resolve().parent
MUT = [("the last block of a lone chunk is not marked the root", "    if slen == 0 { f = f | ROOT }                // one chunk alone is the root\n", "    if slen == 1 { f = f | ROOT }\n"),
       ("the last block is not marked the chunk's end", "    f = flags | first | CHUNK_END\n", "    f = flags | first\n"),
       ("a parent is merged while the count is odd", "  while tc & 1 == 0 {\n    slen = slen - 1\n    top = cv_at(st, slen)\n    parent_to(t, top, t, pf)\n    tc = tc >> 1", "  while tc & 1 == 1 {\n    slen = slen - 1\n    top = cv_at(st, slen)\n    parent_to(t, top, t, pf)\n    tc = tc >> 1"),
       ("the counter does not advance by the chunks done", "    counter = counter + n\n", "    counter = counter + 1\n")]
refuted = 0
for what, old, new in [("nothing (the control)", None, None)] + MUT:
    with tempfile.TemporaryDirectory(dir=here.parent, prefix="mut-hash-") as d:
        d = pathlib.Path(d); work = d / "m"
        shutil.copytree(here, work, symlinks=True, ignore=shutil.ignore_patterns("mut-*", "swap-*", "*.o", "*.log"))
        (d / "one").symlink_to((here.parent / "one").resolve()); (d / "spec").symlink_to((here.parent / "spec").resolve())
        src = (work / "hasher.ode").read_text()
        if old is not None:
            assert src.count(old) == 1, what
            (work / "hasher.ode").write_text(src.replace(old, new))
        subprocess.run([sys.executable, "odec.py", "hasher.ode", "HasherOde.lean"], cwd=work, capture_output=True, text=True, check=True)
        t = (work / "HashTry.lean").read_text()
        a = t.index("def lengths : List Nat :="); b = t.index("end Try")
        (work / "HashTry.lean").write_text(t[:a] + "def lengths : List Nat := [0, 1, 64, 65, 1024, 1025, 2049, 4097, 8193]\n\n" + t[b:])
        subprocess.run(["lake", "build", "HasherOde", "TrySem", "HashContract"], cwd=work, capture_output=True, text=True, timeout=900)
        r = subprocess.run(["lake", "env", "lean", "HashTry.lean"], cwd=work, capture_output=True, text=True, timeout=900)
        line = [l for l in (r.stdout + r.stderr).split("\n") if "examples meet it" in l]
        if not line:
            sys.exit(f"{what}: the examples gave no answer: " + (r.stdout + r.stderr)[-300:])
        fails = int(line[0].split("examples meet it, ")[1].split(" ")[0])
        if old is None:
            if fails != 0:
                sys.exit("the control failed: the unchanged source does not meet its examples in a copy")
            print("control: the unchanged source meets all 27 examples", flush=True)
        else:
            refuted += fails > 0
            print(("refuted by " + str(fails) + " of 27 examples" if fails else "NOT REFUTED") + "\t" + what, flush=True)
print(f"{len(MUT)} wrong sources: {refuted} refuted by an example")
sys.exit(0 if refuted == len(MUT) else 1)
