#!/usr/bin/env python3
"""The instructions of the proved programs (this folder's Code.lean and gen/'s Code_*.lean), each once,
with its bytes, as a Lean list for Cross.lean. usage: mk_cross_table.py OUT.lean CODE.lean..."""
import re, sys
seen, rows = set(), []
for path in sys.argv[2:]:
    for ins, raw in re.findall(r"^  \(0x[0-9A-F]+, (.+?), 0x[0-9A-F]+\)[, ] +-- ((?:[0-9a-f]{2} )+)", open(path).read(), re.M):
        b = raw.replace(" ", "")
        if b in seen or "(.imm T)" in ins: continue
        seen.add(b); rows.append((ins, b))
with open(sys.argv[1], "w") as f:
    f.write("import X86\nopen X86\n\n/-! Written by mk_cross_table.py: every instruction of the proved programs, once, with its bytes. -/\n\n"
            "def crossTable : List (Instr × String) := [\n" + ",\n".join(f'  ({i}, "{b}")' for i, b in rows) + "\n]\n")
print(len(rows), "distinct instructions")
