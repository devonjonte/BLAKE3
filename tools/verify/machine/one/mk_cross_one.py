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
# Forms that only the language's word-level functions use (lang/: their tables are made without the bytes):
# written here by hand, from the listing of the function that brought each.
EXTRA = [(".shr64 .rcx 63", "48c1e93f"),      # ladd: shr rcx, 0x3f
         (".shr64 .rax 1", "48d1e8")]         # ladd: shr rax (by one)
for ins, b in EXTRA:
    if b not in seen: seen.add(b); rows.append((ins, b))
with open(sys.argv[1], "w") as f:
    f.write("import Machine\nopen X86\n\n/-! Written by mk_cross_one.py: every instruction of the proved programs, once, with its bytes. -/\n\n"
            "set_option maxRecDepth 100000 in\ndef crossTable : List (Instr × String) := [\n" + ",\n".join(f'  ({i}, "{b}")' for i, b in rows) + "\n]\n")
print(len(rows), "distinct instructions")
