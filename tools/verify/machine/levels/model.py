#!/usr/bin/env python3
"""The levels design, as a model: `add` and `root` on (n, levels) against the specification's tree.

A parent is a tuple (left, right, root?) so that equal values mean equal trees with the root flag in the
same place. Checked for every count of chunks from 2 to N."""
import sys

def spec(cvs, root=True):
    n = len(cvs)
    if n == 1: return cvs[0]
    left = 1 << ((n - 1).bit_length() - 1)          # the largest power of two below n
    return (spec(cvs[:left], False), spec(cvs[left:], False), root)

class Levels:
    def __init__(self): self.n = 0; self.slot = {}; self.parents = 0
    def add(self, cv):
        n = self.n; j = n & 1
        if n != 0 and j == 0:
            e, L = (n - 1) >> 1, 0
            while True:
                b = e & 1
                assert self.above(L + 1) == b            # the place is free: nothing needed is written over
                self.slot[(L + 1, b)] = (self.slot[(L, 0)], self.slot[(L, 1)], False); self.parents += 1
                if b == 0: break
                e >>= 1; L += 1
        self.slot[(0, j)] = cv
        self.n += 1
    def above(self, L):
        """How many values level L >= 1 holds at rest."""
        return ((self.n - 1) >> 1 >> (L - 1)) & 1 if self.n else 0
    def held(self, L):
        if L == 0: return 0 if self.n == 0 else (1 if self.n & 1 else 2)
        return self.above(L)
    def root(self):
        n = self.n; assert n >= 2
        e, parents = (n - 1) >> 1, 0
        if n & 1 == 0: acc = (self.slot[(0, 0)], self.slot[(0, 1)], e == 0); parents += 1
        else: acc = self.slot[(0, 0)]
        L = 0
        while e != 0:
            L += 1
            if e & 1: acc = (self.slot[(L, 0)], acc, e == 1); parents += 1
            e >>= 1
        return acc, parents

N = int(sys.argv[1]) if len(sys.argv) > 1 else 3000
lv = Levels(); cvs = []; worst = 0
for i in range(N):
    before = lv.parents
    lv.add(i); cvs.append(i)
    worst = max(worst, lv.parents - before)
    assert sum(lv.held(L) << L for L in range(64)) == lv.n
    if lv.n >= 2:
        got, parents = lv.root()
        assert got == spec(cvs), f"{lv.n} chunks"
        assert lv.parents + parents == lv.n - 1
print(f"levels: add and root agree with the specification's tree for every count from 2 to {N}; "
      f"parents made: n - 1 in all; the most in one add: {worst}")
