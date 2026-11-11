#!/usr/bin/env python3
"""The control of cross_one.sh: a model in which a 32-bit write keeps the register's upper half."""
import sys
p = sys.argv[1]
t = open(p).read()
old = "      | 32 => v &&& 0xFFFFFFFF\n"
new = "      | 32 => (s.get r &&& ~~~(0xFFFFFFFF : BitVec 64)) ||| (v &&& 0xFFFFFFFF)\n"
assert t.count(old) == 1
with open(p, "w") as f:
    f.write(t.replace(old, new))
