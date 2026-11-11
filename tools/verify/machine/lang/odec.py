#!/usr/bin/env python3
"""odec: a first compiler for an implementation language of our own (a prototype, BLAKE3 #361).

usage: odec.py SOURCE.ode OUT.lean

The language is structured assembly over 64-bit words: variables, loads and stores of 8, 32 and 64
bits, copies, calls of kernels, if, while, trap. `def` and `for` run at compile time (substitution
and unrolling), so the source can be short where the machine code is long. The compiler writes each
function as a value of Lean's `L.Fn` (Lang.lean): that Lean value is what the proofs are about and
what the assembly is printed from, so this compiler is not trusted for either.

    const NAME = EXPR
    extern NAME/ARITY = "symbol"
    def NAME(a, b) = EXPR                    an expression, substituted where it is used
    def NAME(a, b) { STATEMENTS }            statements, substituted where they are used
    fn NAME(p, q, ...) [reg a, b, ...] [requires TEXT]* { STATEMENTS  return EXPR }

    var x = EXPR          x = EXPR          buf name[BYTES]
    u8[ADDR] = EXPR       u32[ADDR] = EXPR  u64[ADDR] = EXPR
    copy BYTES DST <- SRC
    NAME(ARGS)            a kernel (extern) or a statement `def`
    if COND { } [else { }]    while COND { }    for k in A..B { }    trap

    EXPR: numbers, names, u8[ADDR] u32[ADDR] u64[ADDR], + - & | << >>, ( ), NAME(ARGS) of an expression def
    COND: EXPR (< | > | <= | >= | == | !=) EXPR      (unsigned)
"""
import re, sys

TOKEN = re.compile(r"\s*(?:(//[^\n]*)|(0x[0-9a-fA-F_]+|\d[\d_]*)|([A-Za-z_][A-Za-z_0-9]*)|(\"[^\"]*\")|(<<|>>|<=|>=|==|!=|<-|\.\.|[-+&|()\[\]{}<>=,/]))")


def tokens(text):
    out, at = [], 0
    while at < len(text):
        m = TOKEN.match(text, at)
        if not m:
            if text[at:].strip() == "":
                break
            raise SystemExit(f"odec: cannot read {text[at:at + 30]!r}")
        at = m.end()
        if m.group(1):
            continue
        out.append(m.group(2) or m.group(3) or m.group(4) or m.group(5))
    return out


class Parser:
    def __init__(self, toks):
        self.t, self.i = toks, 0
        self.consts, self.externs, self.edefs, self.sdefs, self.fns = {}, {}, {}, {}, []

    def peek(self):
        return self.t[self.i] if self.i < len(self.t) else None

    def take(self, want=None):
        tok = self.peek()
        if tok is None or (want is not None and tok != want):
            raise SystemExit(f"odec: expected {want!r}, found {tok!r} (token {self.i})")
        self.i += 1
        return tok

    # expressions: tuples ("const", n) ("var", x) ("add", a, b) ... ("load", w, a) ("call", name, args)
    LEVELS = [["|"], ["&"], ["<<", ">>"], ["+", "-"]]
    OPS = {"|": "or", "&": "and", "+": "add", "-": "sub"}

    def expr(self, level=0):
        if level == len(self.LEVELS):
            return self.atom()
        left = self.expr(level + 1)
        while self.peek() in self.LEVELS[level]:
            op = self.take()
            right = self.expr(level + 1)
            left = ("shl" if op == "<<" else "shr", left, right) if op in ("<<", ">>") else (self.OPS[op], left, right)
        return left

    def atom(self):
        tok = self.take()
        if tok == "(":
            e = self.expr(); self.take(")"); return e
        if re.fullmatch(r"0x[0-9a-fA-F_]+|\d[\d_]*", tok):
            return ("const", int(tok.replace("_", ""), 0))
        if tok in ("u8", "u32", "u64") and self.peek() == "[":
            self.take("["); a = self.expr(); self.take("]")
            return ("load", int(tok[1:]), a)
        if self.peek() == "(":
            return ("call", tok, self.args())
        return ("var", tok)

    def args(self):
        self.take("(")
        out = []
        while self.peek() != ")":
            out.append(self.expr())
            if self.peek() == ",":
                self.take()
        self.take(")")
        return out

    def cond(self):
        a = self.expr(); op = self.take(); b = self.expr()
        if op not in ("<", ">", "<=", ">=", "==", "!="):
            raise SystemExit(f"odec: not a comparison: {op}")
        return (op, a, b)

    def block(self):
        self.take("{")
        out = []
        while self.peek() != "}":
            out.append(self.stmt())
        self.take("}")
        return out

    def stmt(self):
        tok = self.take()
        if tok == "var":
            x = self.take(); self.take("="); return ("var", x, self.expr())
        if tok == "buf":
            b = self.take(); self.take("["); n = self.expr(); self.take("]"); return ("buf", b, n)
        if tok in ("u8", "u32", "u64"):
            self.take("["); a = self.expr(); self.take("]"); self.take("="); return ("store", int(tok[1:]), a, self.expr())
        if tok == "copy":
            n = self.expr(1 + 3); d = self.expr(); self.take("<-"); return ("copy", n, d, self.expr())
        if tok == "if":
            c = self.cond(); t = self.block(); e = []
            if self.peek() == "else":
                self.take(); e = self.block()
            return ("if", c, t, e)
        if tok == "while":
            c = self.cond(); return ("while", c, self.block())
        if tok == "for":
            k = self.take(); self.take("in"); a = self.expr(); self.take(".."); b = self.expr(); return ("for", k, a, b, self.block())
        if tok == "trap":
            return ("trap",)
        if tok == "return":
            return ("return", self.expr())
        if self.peek() == "(":
            return ("call", tok, self.args())
        self.take("="); return ("set", tok, self.expr())

    def top(self):
        while self.peek() is not None:
            tok = self.take()
            if tok == "const":
                name = self.take(); self.take("="); self.consts[name] = self.expr()
            elif tok == "extern":
                name = self.take(); self.take("/"); n = int(self.take()); self.take("="); self.externs[name] = (self.take().strip('"'), n)
            elif tok == "def":
                name = self.take(); params = [a[1] for a in self.args()]
                if self.peek() == "=":
                    self.take(); self.edefs[name] = (params, self.expr())
                else:
                    self.sdefs[name] = (params, self.block())
            elif tok == "fn":
                name = self.take(); params = [a[1] for a in self.args()]; regs, requires = [], []
                while self.peek() in ("reg", "requires"):
                    if self.take() == "reg":
                        regs.append(self.take())
                        while self.peek() == ",":
                            self.take(); regs.append(self.take())
                    else:
                        requires.append(self.take().strip('"'))
                self.fns.append((name, params, regs, requires, self.block()))
            else:
                raise SystemExit(f"odec: not a declaration: {tok}")


class Lower:
    """Compile-time evaluation (constants, defs, for) and the Lean text of each function."""
    def __init__(self, p):
        self.p = p

    def value(self, e, env):
        """A compile-time number, or None."""
        e = self.expr(e, env)
        return e[1] if e[0] == "const" else None

    def expr(self, e, env):
        k = e[0]
        if k == "const":
            return e
        if k == "var":
            if e[1] in env:
                return env[e[1]]
            if e[1] in self.p.consts:
                return self.expr(self.p.consts[e[1]], {})
            return e
        if k == "load":
            return ("load", e[1], self.expr(e[2], env))
        if k == "call":
            params, body = self.p.edefs[e[1]]
            args = [self.expr(a, env) for a in e[2]]
            assert len(args) == len(params), f"{e[1]}: {len(params)} arguments"
            return self.expr(body, dict(zip(params, args)))
        a, b = self.expr(e[1], env), self.expr(e[2], env)
        if k in ("shl", "shr"):
            assert b[0] == "const", "a shift is by a number"
            if a[0] == "const":
                return ("const", (a[1] << b[1]) % 2**64 if k == "shl" else a[1] >> b[1])
            return (k, a, b[1])
        if a[0] == "const" and b[0] == "const":
            f = {"add": lambda x, y: (x + y) % 2**64, "sub": lambda x, y: (x - y) % 2**64, "and": lambda x, y: x & y, "or": lambda x, y: x | y}[k]
            return ("const", f(a[1], b[1]))
        return (k, a, b)

    def stmts(self, body, env, fn):
        out = []
        for s in body:
            k = s[0]
            if k == "var":
                if s[1] not in fn["locals"] and s[1] not in fn["params"]:
                    fn["locals"].append(s[1])
                out.append(("set", s[1], self.expr(s[2], env)))
            elif k == "set":
                out.append(("set", s[1], self.expr(s[2], env)))
            elif k == "buf":
                fn["bufs"].append((s[1], self.value(s[2], env)))
            elif k == "store":
                out.append(("store", s[1], self.expr(s[2], env), self.expr(s[3], env)))
            elif k == "copy":
                out.append(("copy", self.value(s[1], env), self.expr(s[2], env), self.expr(s[3], env)))
            elif k == "if":
                op, a, b = s[1]; a, b = self.expr(a, env), self.expr(b, env)
                t, e = self.stmts(s[2], env, fn), self.stmts(s[3], env, fn)
                # the language's three comparisons; the others by exchanging sides or branches
                if op == "<": out.append(("ite", ("ltu", a, b), t, e))
                elif op == ">": out.append(("ite", ("ltu", b, a), t, e))
                elif op == ">=": out.append(("ite", ("ltu", a, b), e, t))
                elif op == "<=": out.append(("ite", ("ltu", b, a), e, t))
                elif op == "==": out.append(("ite", ("eq", a, b), t, e))
                else: out.append(("ite", ("ne", a, b), t, e))
            elif k == "while":
                op, a, b = s[1]; a, b = self.expr(a, env), self.expr(b, env)
                c = {"<": ("ltu", a, b), ">": ("ltu", b, a), "==": ("eq", a, b), "!=": ("ne", a, b)}[op]
                out.append(("while", c, self.stmts(s[2], env, fn)))
            elif k == "for":
                lo, hi = self.value(s[2], env), self.value(s[3], env)
                for i in range(lo, hi):
                    out += self.stmts(s[4], {**env, s[1]: ("const", i)}, fn)
            elif k == "trap":
                out.append(("trap",))
            elif k == "return":
                fn["ret"] = self.expr(s[1], env)
            elif k == "call":
                if s[1] in self.p.sdefs:
                    params, body = self.p.sdefs[s[1]]
                    args = [self.expr(a, env) for a in s[2]]
                    assert len(args) == len(params), f"{s[1]}: {len(params)} arguments"
                    out += self.stmts(body, dict(zip(params, args)), fn)
                else:
                    sym, n = self.p.externs[s[1]]
                    args = [self.expr(a, env) for a in s[2]]
                    assert len(args) == n, f"{s[1]} takes {n} arguments"
                    for a in args:
                        assert a[0] in ("const", "var"), f"{s[1]}: an argument is a number, a variable or a buffer"
                    if sym not in fn["externs"]:
                        fn["externs"].append(sym)
                    out.append(("call", sym, args))
        return out

    def lean_e(self, e, bufs):
        k = e[0]
        if k == "const": return f"(.const {e[1]})"
        if k == "var": return f'(.buf "{e[1]}")' if e[1] in bufs else f'(.var "{e[1]}")'
        if k == "load": return f"(.load {e[1]} {self.lean_e(e[2], bufs)})"
        if k in ("shl", "shr"): return f"(.{k} {self.lean_e(e[1], bufs)} {e[2]})"
        return f"(.{k} {self.lean_e(e[1], bufs)} {self.lean_e(e[2], bufs)})"

    def lean_s(self, s, bufs, ind):
        k = s[0]
        E = lambda e: self.lean_e(e, bufs)
        B = lambda body: "[" + (",".join("\n" + ind + "  " + self.lean_s(x, bufs, ind + "  ") for x in body)) + "]"
        if k == "set": return f'.set "{s[1]}" {E(s[2])}'
        if k == "store": return f".store {s[1]} {E(s[2])} {E(s[3])}"
        if k == "copy": return f".copy {s[1]} {E(s[2])} {E(s[3])}"
        if k == "call": return f'.call "{s[1]}" [{", ".join(E(a) for a in s[2])}]'
        if k == "ite": return f".ite (.{s[1][0]} {E(s[1][1])} {E(s[1][2])}) {B(s[2])} {B(s[3])}"
        if k == "while": return f".while (.{s[1][0]} {E(s[1][1])} {E(s[1][2])}) {B(s[2])}"
        return ".trap"

    def function(self, name, params, regs, requires, body):
        fn = {"params": params, "locals": [], "bufs": [], "externs": [], "ret": ("const", 0)}
        # buffers are known before expressions are printed: collect them first
        low = self.stmts(body, {}, fn)
        bufs = {b for b, _ in fn["bufs"]}
        q = lambda xs: "[" + ", ".join(f'"{x}"' for x in xs) + "]"
        doc = "".join(f"  requires {r}\n" for r in requires)
        return (f"/-- `{name}`, from the source.\n{doc}-/\n" if doc else "") + \
            f"def {name} : Fn where\n  name := \"b3l_{name}\"\n  params := {q(params)}\n  locals := {q(fn['locals'])}\n" \
            f"  regs := {q(regs)}\n  bufs := [{', '.join(f'(\"{b}\", {n})' for b, n in fn['bufs'])}]\n  externs := {q(fn['externs'])}\n" \
            f"  body := [" + ",".join("\n    " + self.lean_s(s, bufs, "    ") for s in low) + f"]\n  ret := {self.lean_e(fn['ret'], bufs)}\n"


def main():
    src, out = sys.argv[1], sys.argv[2]
    p = Parser(tokens(open(src).read())); p.top()
    low = Lower(p)
    text = "import Lang\nopen L\n\n/-! Written by odec.py from " + src.split("/")[-1] + ". Not edited by hand. -/\n\nnamespace Ode\n\n"
    names = []
    for f in p.fns:
        text += low.function(*f) + "\n"; names.append(f[0])
    text += f"def all : List Fn := [{', '.join(names)}]\n\nend Ode\n\n" \
        "def main (args : List String) : IO Unit :=\n  match args with\n" \
        "  | [\"rust\", p] => IO.print (rustFile (Ode.all.map fun f => { f with name := p ++ f.name.drop 4 }))\n" \
        "  | [\"asm\", p] => IO.print (asmFile (Ode.all.map fun f => { f with name := p ++ f.name.drop 4 }))\n" \
        "  | _ => IO.eprintln \"usage: rust PREFIX | asm PREFIX\"\n"
    with open(out, "w") as f:
        f.write(text)
    print(f"{len(names)} functions: {', '.join(names)}")


main()
