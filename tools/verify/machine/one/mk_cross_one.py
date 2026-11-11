#!/usr/bin/env python3
"""Every instruction of the programs proved on Machine.lean (both one-block kernels, the two parent
functions, merge), once, with its bytes, as a Lean list for CrossOne.lean."""
import re, sys
seen, rows = set(), []
for path in sys.argv[2:]:
    for ins, raw in re.findall(r"^  \(0x[0-9A-F]+, (.+?), 0x[0-9A-F]+\),?  -- ((?:[0-9a-f]{2} )+)", open(path).read(), re.M):
        b = raw.replace(" ", "")
        if b in seen: continue
        seen.add(b); rows.append((ins, b))
with open(sys.argv[1], "w") as f:
    f.write("import Machine\nopen X86\n\n/-! Written by mk_cross_one.py: every instruction of the proved programs, once, with its bytes. -/\n\n"
            "set_option maxRecDepth 100000 in\ndef crossTable : List (Instr × String) := [\n" + ",\n".join(f'  ({i}, "{b}")' for i, b in rows) + "\n]\n")
print(len(rows), "distinct instructions")
