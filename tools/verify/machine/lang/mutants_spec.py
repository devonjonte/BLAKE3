#!/usr/bin/env python3
"""Are the contracts that name no machine (../spec) pinned by the proofs? Each false statement is made in a
copy of ../spec, never in place; Lean must then refuse `push_meets_bytes`, `merge_meets_bytes` and
`add_meets_bytes` (Meets_push_bytes, Meets_merge_bytes). The control: the unchanged copy, checked afresh,
must be accepted. Each verdict names the file whose check failed first.

usage: mutants_spec.py [JOBS]"""
import concurrent.futures, pathlib, re, shutil, subprocess, sys, tempfile

here = pathlib.Path(__file__).resolve().parent
jobs = int(sys.argv[1]) if len(sys.argv) > 1 else 4
TARGETS = ["Meets_push_bytes", "Meets_merge_bytes"]

STATEMENTS = [
    ("the count is said to come after the 24 unused bytes", "StackBytes.lean",
     "b = Bytes.le64 cvs.length ++ unused ++ cvs.reverse.flatMap Cv.bytes ++ after",
     "b = unused ++ Bytes.le64 cvs.length ++ cvs.reverse.flatMap Cv.bytes ++ after"),
    ("the values are said to be the newest first", "StackBytes.lean",
     "b = Bytes.le64 cvs.length ++ unused ++ cvs.reverse.flatMap Cv.bytes ++ after",
     "b = Bytes.le64 cvs.length ++ unused ++ cvs.flatMap Cv.bytes ++ after"),
    ("16 bytes are said to be unused before the values", "StackBytes.lean", "unused.length = 24 ∧", "unused.length = 16 ∧"),
    ("the stack is said to take 1000 bytes", "StackBytes.lean", "⟨1792, Stack.Holds⟩", "⟨1000, Stack.Holds⟩"),
    ("56 values are said to fit", "StackBytes.lean", "cvs.length ≤ 55 ∧ b.length = 1792", "cvs.length ≤ 56 ∧ b.length = 1792"),
    ("a word's bytes are said to be the highest first", "StackBytes.lean",
     "(List.range 4).map fun i => w.toBitVec.extractLsb' (8 * i) 8", "(List.range 4).map fun i => w.toBitVec.extractLsb' (24 - 8 * i) 8"),
    ("the count's bytes are said to be the highest first", "StackBytes.lean",
     "(List.range 8).map fun i => (BitVec.ofNat 64 n).extractLsb' (8 * i) 8", "(List.range 8).map fun i => (BitVec.ofNat 64 n).extractLsb' (56 - 8 * i) 8"),
    ("a chaining value is said to take 31 bytes", "StackBytes.lean", "⟨32, fun b cv => b = Cv.bytes cv⟩", "⟨31, fun b cv => b = Cv.bytes cv⟩"),
    ("push is said to leave the stack as it was", "PushContract.lean",
     "updates := [Stack.byteLayout.turns st cvs (new :: cvs)]", "updates := [Stack.byteLayout.keeps st cvs]"),
    ("push is said to take a stack of any size", "PushContract.lean", "accepts := cvs.length < 55", "accepts := True"),
    ("push's arguments are said to be the other way round", "PushContract.lean", "args := [st, cv]", "args := [cv, st]"),
    ("merge is said to merge to one value more", "MergeContract.lean",
     "Blake3.mergeTo k ⟨flags.setWidth 32⟩ target.toNat cvs", "Blake3.mergeTo k ⟨flags.setWidth 32⟩ (target.toNat + 1) cvs"),
    ("merge is said to need no `1 ≤ target`", "MergeContract.lean",
     "  accepts := 1#64 ≤ target ∧ flags < 256#64\n  reads := [Cv.byteLayout.keeps key k]\n", "  accepts := flags < 256#64\n  reads := [Cv.byteLayout.keeps key k]\n"),
    ("add is said to return one more than the count", "MergeContract.lean",
     "returns := fun result => result.toNat = (Merge.merged k flags target (new :: cvs)).length",
     "returns := fun result => result.toNat = (Merge.merged k flags target (new :: cvs)).length + 1"),
    ("a piece that is kept is said to hold anything afterwards", "Contract.lean",
     "Piece := ⟨a, l.size, (l.holds · v), (l.holds · v)⟩", "Piece := ⟨a, l.size, (l.holds · v), fun _ => False⟩"),
]


def check(job):
    what, file, old, new = job
    with tempfile.TemporaryDirectory(dir=here.parent, prefix="mut-spec-") as d:
        d = pathlib.Path(d)
        work = d / "m"
        shutil.copytree(here, work, ignore=shutil.ignore_patterns(".lake", "bench", "*.log", "mut-*", "swap-*", "*.o", "lake-manifest.json"))
        (d / "one").symlink_to((here.parent / "one").resolve())
        copy = d / "spec"
        shutil.copytree(here.parent / "spec", copy, ignore=shutil.ignore_patterns(".lake", "lake-manifest.json"))
        conf = (copy / "lakefile.toml").read_text()      # the copy is one level deeper: name what it requires by where it is
        for line in re.findall(r'^(?:path|srcDir) = "(\.\.[^"]*)"$', conf, re.M):
            conf = conf.replace(f'"{line}"', f'"{(here.parent / "spec" / line).resolve()}"')
        (copy / "lakefile.toml").write_text(conf)
        if old is not None:
            text = (copy / file).read_text()
            if text.count(old) != 1:
                return "MALFORMED", what, ""
            (copy / file).write_text(text.replace(old, new))
        try:
            r = subprocess.run(["lake", "build"] + TARGETS, cwd=work, capture_output=True, text=True, timeout=1500)
        except subprocess.TimeoutExpired:
            return "rejected", what, "(time limit)"
        out = r.stdout + r.stderr
        if r.returncode == 0 and "sorryAx" not in out and all(f"'{t}' depends on axioms" in out for t in ("push_meets_bytes", "merge_meets_bytes", "add_meets_bytes")):
            return "ACCEPTED", what, ""
        first = re.search(r"error: (?:\S*/)?([A-Za-z_0-9]+\.lean):\d+", out)
        return "rejected", what, f"(first refused in {first.group(1)})" if first else "(the build failed)"


verdict, what, where = check(("the unchanged specification, in a copy", None, None, None))
print(f"control: the unchanged specification, in a copy, is {verdict}", flush=True)
if verdict != "ACCEPTED":
    sys.exit("the control failed: the audit proves nothing")
tally = {}
with concurrent.futures.ThreadPoolExecutor(jobs) as pool:
    for verdict, what, where in pool.map(check, STATEMENTS):
        tally[verdict] = tally.get(verdict, 0) + 1
        print(f"{verdict}\t{what} {where}", flush=True)
print(f"{len(STATEMENTS)} false statements of the contracts that name no machine: " + ", ".join(f"{n} {k}" for k, n in sorted(tally.items())))
sys.exit(0 if set(tally) == {"rejected"} else 1)
