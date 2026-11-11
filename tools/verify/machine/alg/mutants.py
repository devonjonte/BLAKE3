#!/usr/bin/env python3
"""Does the proof notice a wrong algorithm? Each mutant changes one of the definitions the theorems are
about (the merge, the fold, the count of one bits, the push) and the build must fail."""
import pathlib, shutil, subprocess, sys, tempfile
here = pathlib.Path(__file__).resolve().parent
MUTANTS = [
    ("the merge's parent takes its children the other way round",
     "mergeTo target ((parentNode key mode second top).cv :: below)", "mergeTo target ((parentNode key mode top second).cv :: below)"),
    ("the final fold's parent takes its children the other way round",
     "st.foldl (fun nd cv => parentNode key mode cv nd.cv) node", "st.foldl (fun nd cv => parentNode key mode nd.cv cv) node"),
    ("the merge stops one value early", "if target < below.length + 2 then", "if target + 1 < below.length + 2 then"),
    ("the merge goes one value too far", "if target < below.length + 2 then", "if target ≤ below.length + 2 then"),
    ("the count of one bits forgets the lowest", "if n = 0 then 0 else n % 2 + ones (n / 2)", "if n = 0 then 0 else ones (n / 2)"),
    ("a push merges to the bits of the next count", "(chunks[n]!).cv :: mergeTo key mode (ones n) (pushed n)", "(chunks[n]!).cv :: mergeTo key mode (ones (n + 1)) (pushed n)"),
    ("a push of a subtree merges to one value more", "Pushes (sub key mode chunks m (2 ^ a) :: mergeTo key mode (ones m) st) (m + 2 ^ a)",
     "Pushes (sub key mode chunks m (2 ^ a) :: mergeTo key mode (ones m + 1) st) (m + 2 ^ a)"),
    ("a pushed subtree's size need not divide the count", "Pushes st m → 2 ^ a ∣ m →", "Pushes st m → 2 ^ a ∣ m + 1 →"),
]
src = (here / "Stack.lean").read_text()
lake = (here / "lakefile.toml").read_text()
c2sp = (here / lake.split('path = "')[1].split('"')[0]).resolve()
rejected = 0
for what, old, new in MUTANTS:
    assert src.count(old) == 1, old
    d = pathlib.Path(tempfile.mkdtemp(prefix="alg-mutant-"))
    (d / "Stack.lean").write_text(src.replace(old, new))
    (d / "lakefile.toml").write_text(lake.replace(lake.split('path = "')[1].split('"')[0], str(c2sp)))
    shutil.copy(here / "lean-toolchain", d / "lean-toolchain")
    r = subprocess.run(["lake", "build"], cwd=d, capture_output=True, text=True)
    shutil.rmtree(d)
    rejected += r.returncode != 0
    print(("rejected" if r.returncode else "ACCEPTED") + "\t" + what, flush=True)
print(f"{rejected} of {len(MUTANTS)} rejected")
sys.exit(0 if rejected == len(MUTANTS) else 1)
