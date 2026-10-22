"""Z3 terms as nodes read through Z3's C API, each read once, for the process.

The provers walk large terms (a kernel's output is millions of nodes),
and z3py's wrappers make each step a dozen ctypes calls, which were the
provers' largest cost (October 22, 2026). A Node holds what the walks ask
of a term (its operator, its width, its integer parameters, its
children), read on first use through the C API on the term's bare
pointer, without wrappers or reference counts. A z3py term is made only
where Z3 must compute (simplify, substitute, the solver): Node.expr.

Each prover case runs in a fresh process (workers.py), so every node lives
as long as the process: `node(t)` keeps t, and a child's pointer stays
valid because the kept term above it holds it. A Z3 id then names one term
for the process's life, so a fact memoized by id (here, and in canon.py)
is exact.
"""
from z3 import main_ctx, Z3_OP_UNINTERPRETED, Z3_APP_AST, Z3_NUMERAL_AST, Z3_BV_SORT, Z3_PARAMETER_INT
from z3 import z3core as C
from z3.z3 import _to_expr_ref

CTX = main_ctx()
REF = CTX.ref()
_nodes = {}          # id -> Node


class Node:
    __slots__ = ("ptr", "id", "_expr", "_kind", "_kids", "_size", "_params", "symbols", "small")

    def __init__(self, ptr, k, expr=None):
        self.ptr, self.id, self._expr = ptr, k, expr
        self._kind = self._kids = self._size = self._params = self.symbols = self.small = None

    @property
    def expr(self):
        """The z3py term, made on first use and kept."""
        if self._expr is None:
            self._expr = _to_expr_ref(self.ptr, CTX)
        return self._expr

    @property
    def kind(self):
        """The operator's kind (Z3_OP_*), as t.decl().kind()."""
        if self._kind is None:
            assert C.Z3_get_ast_kind(REF, self.ptr) in (Z3_APP_AST, Z3_NUMERAL_AST), "a term that is not an application"
            self._kind = C.Z3_get_decl_kind(REF, C.Z3_get_app_decl(REF, self.ptr))
        return self._kind

    @property
    def kids(self):
        """The children, as t.children()."""
        if self._kids is None:
            a = self.ptr
            self._kids = tuple(_node_at(C.Z3_get_app_arg(REF, a, i)) for i in range(C.Z3_get_app_num_args(REF, a)))
        return self._kids

    @property
    def size(self):
        """A bit-vector's width, as t.size(); None for any other sort."""
        if self._size is None:
            s = C.Z3_get_sort(REF, self.ptr)
            self._size = C.Z3_get_bv_sort_size(REF, s) if C.Z3_get_sort_kind(REF, s) == Z3_BV_SORT else 0
        return self._size or None

    @property
    def params(self):
        """The operator's parameters, as t.params() (read raw when all are
        integers: Extract's, ZeroExt's, a rotation's)."""
        if self._params is None:
            d = C.Z3_get_app_decl(REF, self.ptr)
            n = C.Z3_get_decl_num_parameters(REF, d)
            if all(C.Z3_get_decl_parameter_kind(REF, d, i) == Z3_PARAMETER_INT for i in range(n)):
                self._params = tuple(C.Z3_get_decl_int_parameter(REF, d, i) for i in range(n))
            else:
                self._params = tuple(self.expr.params())
        return self._params

    def name(self):
        """The operator's name, as t.decl().name()."""
        return self.expr.decl().name()


def _node_at(ptr):
    k = C.Z3_get_ast_id(REF, ptr)
    n = _nodes.get(k)
    if n is None:
        n = _nodes[k] = Node(ptr, k)
    return n


def node(t):
    """t's node; t is kept for the process's life."""
    k = t.get_id()
    n = _nodes.get(k)
    if n is None:
        n = _nodes[k] = Node(t.as_ast(), k, t)
    elif n._expr is None:
        n._expr = t
    return n


def keep(t):
    """Keeps t for the process's life, so its id stays its own."""
    node(t)


def post_order(root, attr, leaf, join):
    """Sets `attr` on root and every node below it lacking it: a leaf's by
    leaf(node), any other's by join(node, its children's values);
    iteratively, as the terms are deeper than Python's recursion limit."""
    stack = [root]
    while stack:
        n = stack[-1]
        if getattr(n, attr) is not None:
            stack.pop()
            continue
        todo = [c for c in n.kids if getattr(c, attr) is None]
        if todo:
            stack.extend(todo)
            continue
        stack.pop()
        setattr(n, attr, join(n, [getattr(c, attr) for c in n.kids]) if n.kids else leaf(n))
    return getattr(root, attr)


def _union(sets):
    """The union of frozensets, reusing the largest when it holds them all
    (most nodes of a round hold every symbol their children do)."""
    big = max(sets, key=len)
    if all(s <= big for s in sets):
        return big
    return big.union(*sets)


def _leaf_symbols(n):
    if n.kind == Z3_OP_UNINTERPRETED:
        return frozenset([C.Z3_get_symbol_string(REF, C.Z3_get_decl_name(REF, C.Z3_get_app_decl(REF, n.ptr)))])
    return frozenset()


def symbols(t):
    """The names of the uninterpreted constants in t."""
    return post_order(node(t), "symbols", _leaf_symbols, lambda n, sets: _union(sets))


LIMIT = 120
_BIG = False         # `small` of a node with more than LIMIT nodes (None means not yet known)


def _join_small(n, sets):
    if any(s is _BIG for s in sets):
        return _BIG
    s = _union(sets) | {n.id}
    return s if len(s) <= LIMIT else _BIG


def small(t):
    """Whether t has at most LIMIT distinct nodes."""
    return post_order(node(t), "small", lambda n: frozenset([n.id]), _join_small) is not _BIG
