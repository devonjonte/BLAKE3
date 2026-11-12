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
        q, k = self.n + 1, 0
        while q & 1 == 1:
            if q == 1: q = 0
            else: k += 1; q >>= 1
        j = 1 if q != 0 else 0
        L = k
        while L > 0:
            assert L < k or self.held(L) == j        # the place is free: nothing is written over a value still needed
            self.slot[(L, j)] = (self.slot[(L - 1, 0)], self.slot[(L - 1, 1)], False); self.parents += 1
            j = 0; L -= 1
        self.slot[(0, j)] = cv
        self.n += 1
    def held(self, L):
        q = (self.n + 1) >> L
        return 0 if q <= 1 else (2 if q & 1 else 1)
    def root(self):
        n = self.n; assert n >= 2
        pr = acc = None; L = 0; parents = 0
        while n >> L != 0:
            h = self.held(L); single = None
            root_here = n == 1 << (L + 1)
            if h == 2:
                if pr is not None: single = pr
                pr = (self.slot[(L, 0)], self.slot[(L, 1)], root_here); parents += 1
            elif h == 1:
                if pr is not None: pr = (self.slot[(L, 0)], pr, root_here); parents += 1
                else: single = self.slot[(L, 0)]
            else:
                if pr is not None: single, pr = pr, None
            if single is not None:
                if acc is not None: acc = (single, acc, n >> (L + 1) == 0); parents += 1
                else: acc = single
            L += 1
        assert pr is None
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
