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
    """The levels as the code has them (levels.ode): slot[(L, j)] is place j of level L."""
    def __init__(self): self.n = 0; self.slot = {}; self.parents = 0
    def add(self, cv):
        n = self.n
        x = n if n else 1                      # the count, or 1 when nothing was added yet
        L = 0
        while x & 1 == 0:
            self.at_head(L, x)
            x >>= 1
            b = (x + 1) & 1                    # the level above holds one already: its second place
            assert self.above(L + 1) == b      # the place is free: nothing needed is written over
            self.slot[(L + 1, b)] = (self.slot[(L, 0)], self.slot[(L, 1)], False); self.parents += 1
            L += 1
        self.at_head(L, x)
        self.slot[(0, n & 1)] = cv
        self.n += 1
    def above(self, L):
        """How many values level L >= 1 holds at rest."""
        return ((self.n - 1) >> 1 >> (L - 1)) & 1 if self.n else 0
    def root(self):
        n = self.n; assert n >= 2
        e, parents = n - 1, 0                    # the levels have received all the chunks but the newest
        acc = self.slot[(0, e & 1)]              # the newest chunk's value
        L = 0
        while e > 0:
            if e & 1:
                acc = (self.slot[(L, 0)], acc, e == 1); parents += 1
            e >>= 1; L += 1
        return acc, parents

    # What the proof says of the levels (../lang/Spec_levels.lean), checked here on the model.
    def lev(self, L, size, r):
        """Levels from L up are a counter holding r values of `size` chunks: a level whose count is odd
        holds, in its first place, the newest of its values; half the count went to the level above."""
        while L < 54:
            if r % 2 == 1 and self.slot.get((L, 0)) != sub(self.cvs, (r - 1) * size, size): return False
            L, size, r = L + 1, 2 * size, r // 2
        return r == 0
    def at_rest(self):
        """n >= 1 chunks: the counter of n - 1 from the bottom, and the newest chunk at the bottom's next place."""
        n = self.n
        return n == 0 or (self.lev(0, 1, n - 1) and self.slot.get((0, (n - 1) % 2)) == sub(self.cvs, n - 1, 1))
    def at_head(self, L, x):
        """At the head of add's loop after L turns: x = r + 1, n = x * 2^L, levels from L are the counter of
        r and one more value (number r) sits at level L's next place."""
        n, r, size = self.n, x - 1, 1 << L
        if n == 0: assert L == 0 and x == 1; return
        assert n == x * size and self.lev(L, size, r) and self.slot.get((L, r % 2)) == sub(self.cvs, r * size, size), (n, L)


def sub(cvs, start, size):
    """The specification's subtree over `size` chunks from `start`, below the root."""
    return spec(cvs[start:start + size], False)


N = int(sys.argv[1]) if len(sys.argv) > 1 else 3000
lv = Levels(); cvs = []; worst = 0
for i in range(N):
    before = lv.parents
    lv.cvs = cvs
    lv.add(i); cvs.append(i)
    assert lv.at_rest(), f"{lv.n} chunks: not as the contract says"
    worst = max(worst, lv.parents - before)
    if lv.n >= 2:
        got, parents = lv.root()
        assert got == spec(cvs), f"{lv.n} chunks"
        assert lv.parents + parents == lv.n - 1
print(f"levels: add and root agree with the specification's tree for every count from 2 to {N}; "
      f"parents made: n - 1 in all; the most in one add: {worst}")
