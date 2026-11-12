#!/usr/bin/env python3
"""What a reader of each design's contracts must read, from `lean LevelsReading.lean`'s output:
the stack's three contracts (push, merge, add) and the levels' two (ladd, lroot)."""
import re, sys
lines = [l.strip() for l in open(sys.argv[1]) if l.strip().startswith("def ")]
seen, cut = set(), None
for i, l in enumerate(lines):
    if l in seen: cut = i; break
    seen.add(l)
def parse(ls):
    d = {}
    for l in ls:
        m = re.match(r"def (\S+) (\S+) (\d+)$", l)
        d[(m.group(1), m.group(2))] = int(m.group(3))
    return d
stack, levels = parse(lines[:cut]), parse(lines[cut:])
assert ("MergeContract", "Merge.byteContract") in stack and ("LevelsContract", "Ladd.byteContract") in levels
tot = lambda d: sum(d.values())
def names(d): return ", ".join(f"{n} {v}" for (m, n), v in sorted(d.items(), key=lambda x: (x[0][0], x[0][1])))
both = {k: v for k, v in stack.items() if k in levels}
only_s = {k: v for k, v in stack.items() if k not in levels}
only_l = {k: v for k, v in levels.items() if k not in stack}
spec_l = {k: v for k, v in only_l.items() if k[0] in ("Blake3", "Stack")}
print(f"the stack's contracts (push, merge, add): {tot(stack)} lines in {len(stack)} definitions")
print(f"the levels' contracts (ladd, lroot): {tot(levels)} lines in {len(levels)} definitions")
print(f"read for both: {tot(both)} lines")
print(f"only the stack's: {tot(only_s)} lines: {names(only_s)}")
print(f"only the levels': {tot(only_l)} lines, of which {tot(spec_l)} are the specification's own tree and output: {names(only_l)}")
