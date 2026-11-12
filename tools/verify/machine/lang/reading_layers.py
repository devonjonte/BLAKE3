#!/usr/bin/env python3
"""What two theorems' statements depend on, in layers: what both need, and what each needs alone.
usage: reading_layers.py A.txt B.txt   (outputs of `#reading_defs`)"""
import sys
from collections import defaultdict
def load(p):
    d = {}
    for l in open(p):
        f = l.split()
        if f and f[0] == "def": d[(f[1], f[2])] = int(f[3])
    return d
A, B = load(sys.argv[1]), load(sys.argv[2])
def show(title, keys, src):
    by = defaultdict(lambda: [0, 0])
    for k in keys: by[k[0]][0] += 1; by[k[0]][1] += src[k]
    print(f"{title}: {len(keys)} definitions, {sum(src[k] for k in keys)} lines")
    for m in sorted(by): print(f"    {m}: {by[m][0]} definitions, {by[m][1]} lines")
both = set(A) & set(B)
show("both", both, A); show("first only", set(A) - both, A); show("second only", set(B) - both, B)
