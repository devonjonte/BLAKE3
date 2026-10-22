"""Facts about Z3 terms, read through Z3's C API and memoized for the process.

Each prover case runs in a fresh process (workers.py), so a term may live as
long as the process: every term asked about is kept, so a Z3 id names one
term for the process's life and each fact about a node is computed once,
however many terms share it. Subterms are read as bare pointers, with no
Python wrapper and no reference count, alive because the kept term above
them is: a node costs three C calls, where z3py's wrappers cost about
fifteen (through ctypes, the provers' largest cost: October 22, 2026).
"""
from z3 import main_ctx, Z3_OP_UNINTERPRETED
from z3 import z3core as C

CTX = main_ctx().ref()
_kept = []           # every term asked about, for the process's life
_kids = {}           # id -> the children's (pointer, id) pairs
_symbols = {}        # id -> frozenset of the uninterpreted constants' names
_small = {}          # id -> frozenset of the ids below and at it, or None past LIMIT
LIMIT = 120
_none = frozenset()


def _id(a):
    return C.Z3_get_ast_id(CTX, a)


def _children(a, k):
    r = _kids.get(k)
    if r is None:
        kids = [C.Z3_get_app_arg(CTX, a, i) for i in range(C.Z3_get_app_num_args(CTX, a))]
        r = _kids[k] = [(c, _id(c)) for c in kids]
    return r


def _leaf_symbols(a):
    d = C.Z3_get_app_decl(CTX, a)
    if C.Z3_get_decl_kind(CTX, d) == Z3_OP_UNINTERPRETED:
        return frozenset([C.Z3_get_symbol_string(CTX, C.Z3_get_decl_name(CTX, d))])
    return _none


def _post_order(a, memo, leaf, join):
    """memo[id] for the term at pointer a and every node below it, each
    node's from its children's (a leaf's by leaf), iteratively: the terms
    are deeper than Python's recursion limit."""
    stack = [(a, _id(a))]
    while stack:
        a, k = stack[-1]
        if k in memo:
            stack.pop()
            continue
        kids = _children(a, k)
        todo = [(c, i) for c, i in kids if i not in memo]
        if todo:
            stack.extend(todo)
            continue
        stack.pop()
        memo[k] = join(k, [memo[i] for _, i in kids]) if kids else leaf(a, k)


def _union(sets):
    """The union of frozensets, reusing the largest when it holds them all
    (most nodes of a round hold every symbol their children do)."""
    big = max(sets, key=len)
    if all(s <= big for s in sets):
        return big
    return big.union(*sets)


def keep(t):
    """Keeps t for the process's life, so its id stays its own."""
    _kept.append(t)


def symbols(t):
    """The names of the uninterpreted constants in t."""
    _kept.append(t)
    a = t.as_ast()
    _post_order(a, _symbols, lambda a, k: _leaf_symbols(a), lambda k, sets: _union(sets))
    return _symbols[_id(a)]


def _join_small(k, sets):
    if any(s is None for s in sets):
        return None
    s = _union(sets) | {k}
    return s if len(s) <= LIMIT else None


def small(t):
    """Whether t has at most LIMIT distinct nodes."""
    _kept.append(t)
    a = t.as_ast()
    _post_order(a, _small, lambda a, k: frozenset([k]), _join_small)
    return _small[_id(a)] is not None
