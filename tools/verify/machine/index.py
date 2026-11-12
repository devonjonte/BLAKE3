#!/usr/bin/env python3
"""An index of what is proved: one row a theorem, its numbers asked of Lean.

    python3 index.py x86 > index-x86.md      (in lang/, after ./prove_all.sh or the folder's own scripts)
    python3 index.py arm > index-arm.md      (in arm/)
    python3 index.py join index-x86.md index-arm.md > INDEX.md

For each theorem: what it says (a sentence, written here), the contract it is about, how many lines a
reader must read to know what it says and in how many files (`#reading_list`: the definitions its statement
depends on, through every definition those use), and the axioms its proof rests on beyond Lean's three
(`propext`, `Classical.choice`, `Quot.sound`). The sentences are a person's; the numbers are Lean's."""
import re, subprocess, sys

X86 = [  # (module, theorem, contract and where, what it says)
    ("Meets_hex_bytes", "hex_meets_bytes", "`Hex.byteContract` (spec/HexContract.lean)",
     "the kernel `hex`, as assembled, writes the hexadecimal of the 32 bytes read and changes nothing else; an observer of time and cache sees the same whatever they are"),
    ("Meets_push_bytes", "push_meets_bytes", "`Push.byteContract` (spec/PushContract.lean)",
     "`push`, as assembled, puts a chaining value on the stack"),
    ("Meets_merge_bytes", "merge_meets_bytes", "`Merge.byteContract` (spec/MergeContract.lean)",
     "`merge`, as assembled, turns the stack into the specification's `mergeTo` of it and returns its count"),
    ("Meets_merge_bytes", "add_meets_bytes", "`Add.byteContract` (spec/MergeContract.lean)",
     "`add` (push, then merge, each by its contract) turns the stack into the merge of the stack with the new value"),
    ("Checked_merge", "Checked_merge.merge_checked_meets", "`(Merge.contract …).checked` (lang/Abi.lean, lang/Spec_merge.lean)",
     "`merge`'s checked entry does as `merge` where the arguments are accepted and otherwise returns the refusal, memory as it was"),
    ("Proof_merge_sse", "Proof_merge_sse.merge_sse_meets", "`Merge.contract` (lang/Spec_merge.lean)",
     "a second `merge`, on the SSE4.1 kernel alone, meets the same contract"),
    ("Proof_merge_steps", "Proof_merge_steps.merge_steps_meets", "`MergeSteps.contract` (lang/Spec_mergesteps.lean)",
     "a loop that calls `merge` by its contract, one value a turn, does what `merge` does"),
    ("Proof_ladd", "Proof_ladd.ladd_meets", "`Ladd.contract` (lang/Spec_ladd.lean)",
     "`ladd` (the tree's levels, another design than the stack: levels/), as assembled, turns the levels of the tree over some chunks into the levels over those and one more"),
    ("Proof_lroot", "Proof_lroot.lroot_meets", "`Lroot.contract` (lang/Spec_lroot.lean)",
     "`lroot`, as assembled, writes the first eight words of the specification's output for the tree over the levels' chunks, and leaves the levels as they are"),
    ("AddTree", "Add.keeps_the_tree", "no code: `Add.contract`'s result and the specification's tree (alg/Stack.lean)",
     "on the tree's stack for `m` chunks, what `add` leaves is the tree's stack for `m + 1`"),
]
ARM = [
    ("HexNeonBytes", "hex_neon_meets", "`Hex.byteContract` (spec/HexContract.lean)",
     "the kernel `hex_neon`, as assembled, writes the hexadecimal of the 32 bytes read and changes nothing else"),
    ("Quiet_hex_neon", "hex_neon_quiet", "arm/Observer.lean",
     "two machines that differ only in what memory holds and in the vector registers show an observer the same while `hex_neon`'s words run"),
    ("Quiet_hex_neon", "hex_neon_observed", "arm/Observer.lean",
     "the observer has an account of every instruction of `hex_neon`, from any state: the theorem above is not about two runs both unobserved"),
    ("PushBytes", "push_arm_meets", "`Push.byteContract` (spec/PushContract.lean)",
     "`push`, printed for AArch64 from the same source function and assembled, puts a chaining value on the stack"),
]
STANDARD = {"propext", "Classical.choice", "Quot.sound"}


def rows(table, machine):
    mods = sorted({m for m, *_ in table})
    src = "import ReadingList\n" + "".join(f"import {m}\n" for m in mods) + "".join(f"#reading_list {t}\n#print axioms {t}\n" for _, t, *_ in table)
    with open("index_tmp.lean", "w") as f:
        f.write(src)
    b = subprocess.run(["lake", "build", "ReadingList"] + mods, capture_output=True, text=True, timeout=3600)
    if b.returncode != 0:
        sys.exit("the theorems' modules do not build:\n" + (b.stdout + b.stderr)[-2000:])
    r = subprocess.run(["lake", "env", "lean", "index_tmp.lean"], capture_output=True, text=True, timeout=1200)
    out = r.stdout + r.stderr
    if r.returncode != 0:
        sys.exit("Lean did not accept the index:\n" + out[-2000:])
    for _, thm, contract, says in table:
        m = re.search(r"To know what `" + re.escape(thm) + r"` says, read (\d+) definitions \((\d+) lines\) in (\d+) files", out)
        a = re.search(r"'" + re.escape(thm) + r"' depends on axioms: \[(.*?)\]", out, re.S)
        if not (m and a):
            sys.exit(f"no numbers for {thm}")
        axioms = [x.strip() for x in a.group(1).split(",") if x.strip()]
        extra = [x for x in axioms if x not in STANDARD]
        kinds = sorted({"bv_decide" if "bv_decide" in x else x for x in extra})
        where = "none" if contract.startswith("no code") else machine
        print(f"| `{thm}` | {where} | {says} | {contract} | {int(m.group(2)):,} in {m.group(3)} files | {len(extra)}" + (f" ({', '.join(kinds)})" if extra else "") + " |")


if sys.argv[1] == "x86":
    rows(X86, "x86-64, the model written here")
elif sys.argv[1] == "arm":
    rows(ARM, "AArch64, Google DeepMind's model")
else:
    print("# What is proved: an index\n")
    print("Written by `index.py`. One row a theorem: what it says (a person's sentence), the contract it is about, what a reader")
    print("must read to know what it says (`#reading_list`: the definitions its statement depends on, through every definition")
    print("those use), and the axioms its proof rests on beyond Lean's three. The numbers are Lean's.\n")
    print("| theorem | code and machine | what it says | the contract | lines to read | axioms beyond Lean's three |")
    print("|---|---|---|---|---|---|")
    for path in sys.argv[2:]:
        sys.stdout.write(open(path).read())
