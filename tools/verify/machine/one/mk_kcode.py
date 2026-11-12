"""Sse.lean and Avx.lean (the lifter's tables of the two one-block kernels) -> KCode.lean: the two
kernels as one program, and one lemma an address (attribute kcode_at). usage: mk_kcode.py"""
import re
rows = []
for f in ("Sse.lean", "Avx.lean"):
    for line in open(f):
        m = re.match(r"^\s+\((0x[0-9A-F]+), (.*), (0x[0-9A-F]+)\),?\s+--", line)
        if m: rows.append((m.group(1)[2:], m.group(2), m.group(3)[2:]))
t = ["import Sse", "import Avx", "import Attr", "",
     "/-! The two one-block compression kernels as one program, and one lemma an instruction. Written by mk_kcode.py",
     "from the lifter's tables. A function that calls the kernels is proved in a program that has these. -/", "",
     "set_option maxRecDepth 1000000", "namespace KCode", "open X86", "",
     "def table : List (Nat × Instr × Nat) := Sse.table ++ Avx.table", "",
     "def prog (pc : Nat) : Option (Instr × Nat) := table.lookup pc", ""]
t += [f"@[kcode_at] theorem at_{a} : prog 0x{a} = some ({ins}, 0x{n}) := rfl" for a, ins, n in rows]
t += ["", "end KCode", ""]
with open("KCode.lean", "w") as f: f.write("\n".join(t))
print(len(rows), "instructions")
