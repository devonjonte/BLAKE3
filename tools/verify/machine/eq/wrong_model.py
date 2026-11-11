#!/usr/bin/env python3
"""The control of cross.sh: a PMOVMSKB that reads each byte's lowest bit, not its highest."""
import sys
p = sys.argv[1]
t = open(p).read()
old = "v.extractLsb' 7 1"
assert t.count(old) == 1
with open(p, "w") as f:
    f.write(t.replace(old, "v.extractLsb' 0 1"))
