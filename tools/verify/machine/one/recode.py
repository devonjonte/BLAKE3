#!/usr/bin/env python3
"""Rewrite Code.lean's one-lemma-an-instruction lines for merge from Merge.lean's table."""
import re
rows = re.findall(r"^  \((0x4[0-9A-F]{4}), (.+?), (0x[0-9A-F]+)\),?  --", open("Merge.lean").read(), re.M)
lines = open("Code.lean").read().split("\n")
keep = [l for l in lines if not re.match(r"@\[merge_at\] theorem at_4[0-9A-F]{4} ", l)]
first = next(i for i, l in enumerate(lines) if re.match(r"@\[merge_at\] theorem at_4[0-9A-F]{4} ", l))
new = [f"@[merge_at] theorem at_{a[2:]} : prog {a} = some ({ins}, {n}) := rfl" for a, ins, n in rows]
head = [l for l in lines[:first] if l in keep]
out = lines[:first] + new + [l for l in lines[first:] if not re.match(r"@\[merge_at\] theorem at_4[0-9A-F]{4} ", l)]
with open("Code.lean", "w") as f:
    f.write("\n".join(out))
print(len(new), "lemmas")
