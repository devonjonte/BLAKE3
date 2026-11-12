#!/usr/bin/env python3
"""The compiler's other output for a word-level function: the proof that it meets its contract.

usage: prove_fn.py SOURCE.ode NAME ROWS LAYOUT OUT.lean

What a function is claimed to do is a contract written in Lean, by hand, for a reader
(`Spec_NAME.lean`, in the vocabulary of `Abi.lean`). The source names it and gives the prover what no
reader needs:

    fn NAME(params)
      meets CONTRACT(ghost: Type, ...)       the contract, and what it is stated for besides the arguments
      uses FILE, ...                         Lean files of lemmas for the prover
      leave by LEMMA                         gives the contract's `ensures` from the invariant when the loop ends
      [enter open LEMMA as names]            takes a `requires` fact apart before the first instruction
    {
      ...
      while CONDITION
        ghost name: Type, ...                what the invariant speaks of besides the variables
        invariant CLAUSE [by LEMMA]          holds each time the loop's head is reached; LEMMA carries it
                                             across a turn (without one: it is read off, or kept by `P.frame`)
        decreases VARIABLE
        [open LEMMA as names]                takes an invariant's fact apart before a turn's instructions
        [assert CLAUSE]                      arithmetic the run needs said
      { ... }

A clause is a comparison of the language's expressions (variables, numbers, `+ - | & << >>`, `low8(e)`,
`low32(e)`, `Name(args)` for a Lean definition), or `Name(args)` alone, which says `Name` of memory.
Whatever the contract requires of the arguments alone is known at every turn without being repeated.
By convention a lemma's memory is `m`, and for a predicate `P` over memory `P.cells` (if there is one)
gives what its holder may read at once and `P.frame` says it depends on its own bytes only.

ROWS is the lifter's reading of the assembled object; LAYOUT is what the compiler printed about where
it put things. This writes, with nothing left for a person to fill in:

  Inv              the invariant on the machine's state: each variable where the compiler keeps it, and
                   around the clauses what the compiler itself keeps (the frame owned, the caller's
                   registers and return address saved in it, every byte outside the frame and what may be
                   modified as it was at entry);
  enter, turn, leave   the three straight-line pieces of a function with one loop, each proved by
                   running its instructions on symbolic memory (Cells.lean), with an external function's
                   contract at each call, split on the conditions the invariant does not settle;
  NAME_meets       for all arguments, Abi.Meets PROGRAM ENTRY (CONTRACT ...): by Abi.meets_of_triple,
                   Hoare.seq and Hoare.loop.

Lean checks all of it; nothing here is trusted. One loop, not nested, for now."""
import re, sys
import odec

src, name, rows_path, layout_path, out_path = sys.argv[1:6]
text = open(src).read()
clauses, callees, stripped = odec.contracts_of(text)
source, _, _ = odec.kernels(stripped)
P = odec.Parser(odec.tokens(source)); P.top()
low = odec.Lower(P)
fdef = next(f for f in P.fns if f[0] == name)
fn = {"params": fdef[1], "locals": [], "bufs": [], "externs": [], "ret": ("const", 0)}
body = low.stmts(fdef[4], {}, fn)
params = fdef[1]
head = clauses[name]["head"]
loops = clauses[name]["loops"]
assert len(loops) <= 1, "one loop at most, for now"
STRAIGHT = not loops                     # no loop: one straight-line piece from the entry to the return
loop = loops[0] if loops else []
sym_extern = {symbol: ext for ext, (symbol, _) in P.externs.items()}

# ---------------------------------------------------------------- the layout
saved, frame, home, bufat = [], 0, {}, {}
for line in open(layout_path):
    f = line.split()
    if f[0] == "saved": saved = f[1:]
    elif f[0] == "frame": frame = int(f[1])
    elif f[0] == "home": home[f[1]] = " ".join(f[2:])
    elif f[0] == "buf": bufat[f[1]] = int(f[2])


def has_call(ss):
    return any(s[0] == "call" or (s[0] == "ite" and (has_call(s[2]) or has_call(s[3]))) or (s[0] == "while" and has_call(s[2])) for s in ss)


own_calls = clauses[name].get("calls", [])            # calls of this file's functions, by their contracts
OWN = {f"b3l_{n}": (n, info) for n, info in odec.own.items()}
# below the frame: where a callee's return address goes, and under it the most stack a callee's contract may use
C0 = (8 + max([odec.own[c["callee"]]["budget"] for c in own_calls] or [0])) if has_call(body) else 0
F = C0 + frame + 8 * len(saved)          # bytes the function owns below the stack pointer it is entered with
REGS = "rax rcx rdx rbx rsp rbp rsi rdi r8 r9 r12 r13 r14 r15".split()
ABI = ["rdi", "rsi", "rdx", "rcx", "r8", "r9"]
XS = " ".join(f"x{i}" for i in range(16))


def slot_of(x):
    m = re.fullmatch(r"qword ptr \[rsp \+ (\d+)\]", home[x])
    return C0 + int(m.group(1)) if m else None


def at(off): return "fb" if off == 0 else f"(fb + {off}#64)"


# ---------------------------------------------------------------- the code's shape
rows = [l.rstrip("\n").split("\t") for l in open(rows_path)]
code = {int(a, 16): (ins, int(n, 16)) for a, n, ins in rows}
ENTRY = int(rows[0][0], 16)
back = [(int(a, 16), int(re.search(r"0x([0-9A-F]+)", ins).group(1), 16)) for a, n, ins in rows if ins.startswith(".jmp") and int(re.search(r"0x([0-9A-F]+)", ins).group(1), 16) <= int(a, 16)]
assert len(back) == (0 if STRAIGHT else 1), "one loop"
HEAD = back[0][1] if back else None
JUMP = re.compile(r"\.(jae|jne|je|jmp|call) 0x([0-9A-F]+)")


def segments(pc, events, stop):
    """Walk the code from pc, taking each conditional jump as the next condition event says (a jump is
    taken when its condition is false) and ending a piece after each call. Returns the pieces' lengths
    and the calls between them. `stop` is "head" or "ret"."""
    events = list(events); pieces, n, calls = [], 0, []
    while True:
        if stop == "head" and pc == HEAD and (n > 0 or pieces):
            assert not events, events; return pieces + [n], calls
        ins, nxt = code[pc]; n += 1
        m = JUMP.match(ins)
        if ins == ".ret":
            assert stop == "ret" and not events; return pieces + [n], calls
        if not m: pc = nxt; continue
        kind, target = m.group(1), int(m.group(2), 16)
        if kind == "jmp": pc = target
        elif kind == "call":
            ev = events.pop(0); assert ev[0] == "call", ev
            calls.append((ev[1], target)); pieces.append(n); n = 0; pc = nxt
        else:
            ev = events.pop(0); assert ev[0] == "cond", ev
            pc = nxt if ev[2] else target


# ---------------------------------------------------------------- expressions to Lean
def lean_low(e, env):
    """A lowered expression (odec's) as a Lean term, in the form the run leaves it."""
    k = e[0]
    if k == "const": return f"{e[1]}#64"
    if k == "var":
        v = env.get(e[1]); assert v is not None, f"{e[1]} has no known value here"; return v
    if k == "load": return None
    a = lean_low(e[1], env)
    if k in ("shl", "shr"): return None if a is None else f"({a} {'<<<' if k == 'shl' else '>>>'} {e[2]})"
    b = lean_low(e[2], env)
    if a is None or b is None: return None
    return f"({a} {dict(add='+', sub='-', **{'and': '&&&', 'or': '|||'})[k]} {b})"


OPS = {"+": "+", "-": "-", "|": "|||", "&": "&&&"}
CT = re.compile(r"\s*(?:(0x[0-9a-fA-F]+|\d+)|([A-Za-z_][\w.]*)|(==|!=|<=|>=|<<|>>|[-+|&()\[\],<>]))")


class Clause:
    """A clause's expression: the language's own operators, `vec[a] == v`, `u64[a] == v`, `low8(e)`,
    `low32(e)`, `result`, and `Name(args)` for a definition of the specification's Lean files."""
    def __init__(self, s):
        self.toks, i = [], 0
        while i < len(s):
            m = CT.match(s, i)
            if not m:
                assert s[i:].strip() == "", f"cannot read {s[i:]!r}"; break
            self.toks.append(m.group(1) or m.group(2) or m.group(3)); i = m.end()
        self.i = 0

    def peek(self): return self.toks[self.i] if self.i < len(self.toks) else None
    def take(self, want=None):
        t = self.toks[self.i]; assert want is None or t == want, (t, want); self.i += 1; return t

    def clause(self, env, mem):
        """The clause as a Lean proposition. Sets self.pred when it is `Name(args)` alone: `Name` of memory."""
        self.pred = None
        if self.peek() in ("vec", "u64"):
            kind = self.take(); self.take("["); a = self.expr(env, mem); self.take("]"); self.take("=="); v = self.expr(env, mem)
            return f"{'Vec' if kind == 'vec' else 'Quad'} {mem} {a} {v}"
        if re.fullmatch(r"[A-Z][\w.]*", self.peek() or "") and self.i + 1 < len(self.toks) and self.toks[self.i + 1] == "(":
            start = self.i; name = self.take(); xs = self.args(env, mem)
            if self.peek() is None:
                self.pred = name; return f"{name} {mem} " + " ".join(xs)
            self.i = start
        a = self.expr(env, mem); op = self.take(); b = self.expr(env, mem)
        return {"==": f"{a} = {b}", "!=": f"{a} ≠ {b}", "<": f"{a} < {b}", "<=": f"{a} ≤ {b}", ">": f"{b} < {a}", ">=": f"{b} ≤ {a}"}[op]

    def args(self, env, mem):
        self.take("("); out = []
        while self.peek() != ")":
            out.append(self.expr(env, mem))
            if self.peek() == ",": self.take()
        self.take(")"); return out

    def expr(self, env, mem):
        a = self.term(env, mem)
        while self.peek() in ("+", "-", "|", "&"):
            op = OPS[self.take()]; b = self.term(env, mem); a = f"({a} {op} {b})"
        return a

    def term(self, env, mem):
        a = self.atom(env, mem)
        while self.peek() in ("<<", ">>"):
            op = self.take(); n = int(self.take(), 0); a = f"({a} {'<<<' if op == '<<' else '>>>'} {n})"
        return a

    def atom(self, env, mem):
        t = self.take()
        if t == "(":
            a = self.expr(env, mem); self.take(")"); return a
        if re.fullmatch(r"0x[0-9a-fA-F]+|\d+", t): return f"{int(t, 0)}#64"
        if self.peek() == "(":
            xs = self.args(env, mem)
            if t == "low8": return f"(BitVec.setWidth 8 {xs[0]})"
            if t == "low32": return f"(BitVec.setWidth 32 {xs[0]})"
            return f"({t} {' '.join(xs)})"
        if t in env: return env[t]
        if t in P.consts: return f"{low.value(P.consts[t], {})}#64"
        raise SystemExit(f"prove_fn: {t} is not known in a clause")


def split_by(s):
    m = re.match(r"^(.*?)\s+by\s+([\w.]+)$", s)
    return (m.group(1), m.group(2)) if m else (s, None)


# ---------------------------------------------------------------- what the source gives the prover
TYPES = {"vec": "V", "word": "BitVec 64"}
def binders(text):
    out = []
    for g in text.split(","):
        if g.strip():
            n, ty = [x.strip() for x in g.split(":", 1)]; out.append((n, TYPES.get(ty, ty)))
    return out


def one(items, word, what):
    xs = [rest for w, rest in items if w == word]
    assert len(xs) == 1, f"{name}: {what}"
    return xs[0]


mm = re.match(r"^([\w.]+)\((.*)\)$", one(head, "meets", "the function must name its contract: meets CONTRACT(ghost: Type, ...)"))
CNAME, fn_ghosts = mm.group(1), binders(mm.group(2))
uses = [u.strip() for w, rest in head if w == "uses" for u in rest.split(",")]
LEAVE = None if (STRAIGHT and not any(w == "leave" for w, _ in head)) else \
    re.match(r"^by\s+([\w.]+)$", one(head, "leave", "the function must name the lemma that gives its ensures when the loop ends: leave by LEMMA")).group(1)
enter_opens = [re.match(r"^open\s+([\w.]+)\s+as\s+(.*)$", rest).groups() for w, rest in head if w == "enter" and rest.startswith("open")]
enter_knows = [re.match(r"^know\s+([\w.]+)$", rest).group(1) for w, rest in head if w == "enter" and rest.startswith("know")]
loop_ghosts = [b for w, rest in loop if w == "ghost" for b in binders(rest)]
invariants = [split_by(rest) for w, rest in loop if w == "invariant"]
decreases = None if STRAIGHT else one(loop, "decreases", "the loop must say what gets smaller: decreases VARIABLE")
opens = [re.match(r"^([\w.]+)\s+as\s+(.*)$", rest).groups() for w, rest in loop if w == "open"]
asserts = [rest for w, rest in loop if w == "assert"]

# where the loop is in the function
wi = next((i for i, s in enumerate(body) if s[0] == "while"), len(body))
before, wcond, wbody, after = body[:wi], (body[wi][1] if wi < len(body) else None), (body[wi][2] if wi < len(body) else []), body[wi + 1:]


def sets(ss):
    out = set()
    for s in ss:
        if s[0] == "set": out.add(s[1])
        elif s[0] == "ite": out |= sets(s[2]) | sets(s[3])
        elif s[0] == "while": out |= sets(s[2])
    return out


def reads(e):
    if e[0] == "var": return {e[1]}
    return set().union(*[reads(x) for x in e[1:] if isinstance(x, tuple)]) if len(e) > 1 else set()


def mentions(s, x):
    """Does this statement read or set x anywhere?"""
    k = s[0]
    if k == "ite": return x in reads(s[1][1]) | reads(s[1][2]) or any(mentions(y, x) for y in s[2] + s[3])
    if k == "while": return x in reads(s[1][1]) | reads(s[1][2]) or any(mentions(y, x) for y in s[2])
    if k == "call": return any(x in reads(a) for a in s[2])
    if k == "set": return s[1] == x or x in reads(s[2])
    return any(x in reads(e) for e in s[1:] if isinstance(e, tuple))


assert not (sets(body) & set(params)), "a parameter is assigned: not yet"
changed = sets(wbody)                                   # variables the loop assigns
first_use = {}                                          # is a changed variable read before the body sets it?
for s_ in wbody:
    for x in changed:
        if x in first_use or not mentions(s_, x): continue
        first_use[x] = "set" if (s_[0] == "set" and s_[1] == x and x not in reads(s_[2])) else "read"
live = {x for x in changed if x in (reads(wcond[1]) | reads(wcond[2]) if wcond else set()) | reads(fn["ret"]) or first_use.get(x) == "read"}
for x in live: assert slot_of(x) is None, f"{x} changes in the loop and lives in the frame: not yet"
# a variable set before the loop and not in it: the invariant must say what it is (`invariant x == E`)
frozen = {}
base_env = {p: p for p in params}
base_env.update({g: g for g, _ in fn_ghosts})
for cl, _ in invariants:
    m = re.match(r"^(\w+)\s*==\s*(.*)$", cl)
    if m and m.group(1) in fn["locals"] and m.group(1) not in changed:
        frozen[m.group(1)] = Clause(m.group(2)).expr(base_env, "?")
for x in ([] if STRAIGHT else sets(before)): assert x in frozen or x in changed, f"the invariant must say what {x} is (invariant {x} == ...)"
inv_user = [(cl, by) for cl, by in invariants if not (re.match(r"^(\w+)\s*==", cl) and re.match(r"^(\w+)", cl).group(1) in frozen)]


def env_at(reg):
    """Each variable as a Lean term at the loop's head; `reg` gives a register-homed variable's term."""
    env = dict(base_env); env.update(frozen)
    for x in live: env[x] = reg(x)
    env.update({g: g for g, _ in loop_ghosts})
    return env


# ---------------------------------------------------------------- the invariant on the machine's state
CARGS = " ".join(params + [g for g, _ in fn_ghosts])
C = f"(Abi.Contract.framed ({CNAME} {CARGS}) {F}#64)"                  # the contract, with the frame the compiler made
OPEN_C = f"{CNAME}, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true"
UNFOLD = f"{OPEN_C}, Abi.AllApart, Abi.Apart, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, BitVec.reduceAdd"
UNFOLD_X = f"{OPEN_C}, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, BitVec.reduceAdd"
CALLEE_SAVED = ["rbx", "rbp", "r12", "r13", "r14", "r15"]
ARGDECL = f"(fb {' '.join(params)} ra : BitVec 64) (sv : Abi.Saved) " + " ".join(f"({g} : {t})" for g, t in fn_ghosts) + " (m0 : Mem)"
ARGUSE = " ".join(["fb"] + params + ["ra", "sv"] + [g for g, _ in fn_ghosts] + ["m0"])
PRE = f"Abi.Pre 0x{ENTRY:X} {C} fb ra sv m0"
POST = f"Abi.Post {C} fb ra sv m0"
outside = f"(∀ x : BitVec 64, {C}.stack + 8#64 ≤ x - fb → (∀ r ∈ {C}.modifies, r.2 ≤ x - r.1) → s.mem x = m0 x)"
param_reg = [(p, home[p]) for p in params if slot_of(p) is None]
param_slot = [(p, slot_of(p)) for p in params if slot_of(p) is not None]
unpushed = [r for r in CALLEE_SAVED if r not in saved]

# (text, how it is proved of a state that was run to, its name when the invariant is taken apart)
inv_fixed = [f"s.pc = 0x{HEAD or 0:X}", f"s.rsp = {at(C0)}"] + [f"s.{r} = {p}" for p, r in param_reg] + [f"s.{r} = sv.{r}" for r in unpushed]
inv_mem = [(f"Region s.mem fb {F}#64", "mem_region", "hF"), (f"Quad s.mem (fb + {F}#64) ra", "mem_fact", "hRa")] + \
    [(f"Quad s.mem (fb + {F - 8 * (i + 1)}#64) sv.{r}", "mem_fact", f"hS{i}") for i, r in enumerate(saved)] + \
    [(f"Quad s.mem {at(o)} {p}", "mem_fact", f"hPs{i}") for i, (p, o) in enumerate(param_slot)] + \
    [(f"Abi.AllApart ((fb, {C}.stack + 8#64) :: {C}.regions)", "exact hAp0", "hAp"), (outside, None, "hOut"),
     (f"{C}.accepts", "exact hAcc0", "hAcc"), (f"{C}.requires m0", "exact hReq0", "hReq")]
inv_frozen = [(f"s.{home[x]} = {e}" if slot_of(x) is None else f"Quad s.mem {at(slot_of(x))} {e}", slot_of(x) is None) for x, e in frozen.items()]
env_s = env_at(lambda x: f"s.{home[x]}")
inv_clauses, inv_pred = [], []
for cl, _ in inv_user:
    c = Clause(cl); inv_clauses.append(c.clause(env_s, "s.mem")); inv_pred.append(c.pred)
preds = [p for i, p in enumerate(inv_pred) if p and p not in inv_pred[:i]]
ex = "".join(f"({g} : {t}) " for g, t in loop_ghosts)
inv_inner = " ∧\n    ".join([c for c, _ in inv_frozen] + inv_clauses)

L = ["import Cells", "import Kernels", "import AbiProof"] + (["import AbiCall"] if own_calls else []) + [f"import Spec_{CNAME.split('.')[0].lower()}"] + [f"import {u}" for u in uses] + \
    [f"import {odec.own[c]['theorem'].rsplit('.', 1)[0]}" for c in dict.fromkeys(x["callee"] for x in own_calls)] + [f"import Code_{name}", "open X86 Cells", "",
     f"/-! # `{name}`, as assembled, meets `{CNAME}`", "",
     f"Written by prove_fn.py from {src.split('/')[-1]} and the compiler's layout; not edited by hand, and not to be read",
     f"but for its last theorem's statement: Lean checks the rest. The frame: {F} bytes below the stack pointer at entry",
     f"(`fb` is its lowest address), the caller's {', '.join(saved)} at its top.", "-/", "",
     f"namespace Proof_{name}", "", "set_option maxRecDepth 1000000", "set_option maxHeartbeats 0", "set_option linter.unusedVariables false", ""]
if not STRAIGHT:
    L += [f"/-- What holds each time the loop's head is reached: the source's `invariant` clauses, each variable where the",
          f"compiler keeps it, and the frame as the compiler keeps it. -/",
          f"def Inv {ARGDECL} (s : State) : Prop :=\n  " + " ∧\n  ".join(inv_fixed + [c for c, _, _ in inv_mem]) + " ∧\n  " + (f"∃ {ex}, " if ex else "") + inv_inner, ""]

STATE = lambda names: "⟨" + ", ".join(names) + f", zf, cf, {', '.join(XS.split())}, mem, pc⟩"
INTROS = "intro rax' rcx' rdx' rsi' rdi' r8' r9' zf' cf' y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15"


def cond_fact(c, value, env):
    kind, a, b = c[0], lean_low(c[1], env), lean_low(c[2], env)
    assert a and b, "a condition on a value read from memory: not yet"
    if kind == "ltu": return f"({a}).ult ({b}) = {'true' if value else 'false'}"
    return f"({a} - {b} == 0#64) = {'true' if value == (kind == 'eq') else 'false'}"


def cond_prop(c, env):
    kind, a, b = c[0], lean_low(c[1], env), lean_low(c[2], env)
    return f"{a} < {b}" if kind == "ltu" else f"{a} = {b}"


def paths(ss, env):
    """Every way through the statements: lists of events (a condition with its value, or a call)."""
    res = [([], env)]
    for s in ss:
        new = []
        for ev, e in res:
            k = s[0]
            if k == "set":
                e2 = dict(e); e2[s[1]] = lean_low(s[2], e); new.append((ev, e2))
            elif k == "call": new.append((ev + [("call", s[1])], e))
            elif k == "trap": pass
            elif k == "ite":
                tp, ep = paths(s[2], e), paths(s[3], e); split = bool(tp) and bool(ep)
                new += [(ev + [("cond", s[1], True, split, e)] + ev2, e2) for ev2, e2 in tp]
                new += [(ev + [("cond", s[1], False, split, e)] + ev2, e2) for ev2, e2 in ep]
            else: new.append((ev, e))
        res = new
    return res


def run_piece(events, start, stop, extra, ind):
    """The tactics that run one path: its conditions as facts, each piece run, each call by its contract."""
    t = []
    conds = [e for e in events if e[0] == "cond"]
    for i, e in enumerate(conds):
        t.append(f"{ind}have c{i} : {cond_fact(e[1], e[2], e[4])} := by bv_decide")
    pieces, calls = segments(start, events, stop)
    facts = ", ".join([f"c{i}" for i in range(len(conds))] + extra)
    for i, n in enumerate(pieces):
        t += [f"{ind}refine runs_then (a := {n}) (s1 := ?_) ?_ ?_", f"{ind}case refine_2 => run_fn [{facts}]; rfl"]
        if i < len(calls):
            callee = sym_extern[calls[i][0]]; assert callee in callees, f"no contract for {callee} (callee ... meets ...)"
            lemma, nh = callees[callee]
            t += [f"{ind}refine {lemma} Code_{name}.has_kernels {' '.join(['(by mem_auto)'] * nh)} ?_", f"{ind}{INTROS}"]
    return t


def outside_goal(ind, old):
    """A byte outside the frame and what may be modified is as it was at entry."""
    return [f"{ind}· intro x hx hmod"] + ([f"{ind}  refine Eq.trans ?_ (hOut x hx hmod)"] if old else []) + \
        [f"{ind}  have hx' := hx", f"{ind}  have hmod' := hmod", f"{ind}  simp only [{UNFOLD_X}] at hx' hmod'", f"{ind}  first | rfl | mem_away"]


def prove_inv(ind, old_outside, turn):
    """The invariant of the state reached: each part by the tactic its kind takes."""
    n_ex = len(loop_ghosts)
    t = [f"{ind}refine runs_done " + ("⟨" if turn else "") + "⟨" + ", ".join(["rfl"] * len(inv_fixed) + ["?_"] * (len(inv_mem) + 1)) + "⟩" + (", ?_⟩" if turn else ""),
         f"{ind}all_goals try dsimp only"]
    for text, tac, _ in inv_mem:
        t += [f"{ind}· {tac}"] if tac else outside_goal(ind, old_outside)
    t += [f"{ind}· " + "; ".join(["apply Exists.intro"] * n_ex) if n_ex else f"{ind}· skip",
          f"{ind}  refine ⟨" + ", ".join(["?_"] * (len(inv_frozen) + len(inv_clauses))) + "⟩"]
    for c, in_reg in inv_frozen: t.append(f"{ind}  · {'rfl' if in_reg else 'mem_fact'}")
    for (cl, by), pred in zip(inv_user, inv_pred):
        if turn and by: t.append(f"{ind}  · apply {by} <;> mem_auto")
        elif pred: t.append(f"{ind}  · first | mem_auto | (apply {pred}.frame <;> mem_auto)")
        else: t.append(f"{ind}  · first | rfl | mem_auto")
    if turn: t.append(f"{ind}· exact BitVec.lt_def.mp (by bv_decide)")
    return t


def tree(ps, done, leaf, ind):
    """Split on each condition the hypotheses do not settle, then prove each leaf."""
    first = ps[0][0]
    idx = next((i for i, e in enumerate(first) if e[0] == "cond" and e[3] and i not in done), None)
    if idx is None: return leaf(first, ind)
    e = first[idx]
    yes = [p for p in ps if p[0][idx][2]]; no = [p for p in ps if not p[0][idx][2]]
    ty, tn = tree(yes, done | {idx}, leaf, ind + "  "), tree(no, done | {idx}, leaf, ind + "  ")
    return [f"{ind}by_cases hs{idx} : {cond_prop(e[1], e[4])}", f"{ind}·" + ty[0][len(ind) + 1:]] + ty[1:] + [f"{ind}·" + tn[0][len(ind) + 1:]] + tn[1:]


def known(ind, mem, at_head):
    """What is at hand before a piece is run: the regions apart, what the contract requires (of the
    arguments alone, once the loop is entered), and what the holder of each memory predicate may read."""
    t = [f"{ind}have hAp0 := hAp", f"{ind}simp only [{UNFOLD}] at hAp", f"{ind}split_ands hAp",
         f"{ind}have hAcc0 := hAcc", f"{ind}try (simp only [{OPEN_C}] at hAcc; split_ands hAcc)",
         f"{ind}have hReq0 := hReq", f"{ind}simp only [{OPEN_C}] at hReq", f"{ind}split_ands hReq"]
    if at_head: t.append(f"{ind}forget_about m0 except hOut hReq0")
    for i, p in enumerate(preds):
        t.append(f"{ind}try (have hK{i} := {p}.cells (m := {mem}) (by assumption); split_ands hK{i})")
    return t


def open_with(lemma, names, mem, i, ind):
    """A lemma that takes a fact apart: its hypotheses found, its conclusion's parts named."""
    return [f"{ind}have_by hO{i} := {lemma} (m := {mem})", f"{ind}obtain ⟨{names}, hO{i}⟩ := hO{i}", f"{ind}try norm_addr at hO{i}", f"{ind}split_ands hO{i}"] + \
        [f"{ind}try subst {g}" for g, _ in loop_ghosts]


# ---------------------------------------------------------------- a function with no loop: one piece
def know_with(lemma, mem, i, ind):
    """A lemma whose conclusion is facts to have at hand: its hypotheses found."""
    return [f"{ind}have_by hE{i} := {lemma} (m := {mem})", f"{ind}try norm_addr at hE{i}", f"{ind}split_ands hE{i}"]


if STRAIGHT:
    wp = paths(body, dict(base_env))
    kinds = {e[1] in OWN for ev, _ in wp for e in ev if e[0] == "call"}
    assert kinds <= {True}, "a call of a kernel in a function with no loop: not yet"
    ENTER = [f"  obtain {STATE(REGS)} := s",
             "  obtain ⟨hpc, hsp, hargs, hbx, hbp, h12, h13, h14, h15, hmem, hF, hRa, hAp, hAcc, hReq⟩ := hP",
             f"  simp only [{OPEN_C}] at hpc hsp hargs hbx hbp h12 h13 h14 h15 hmem hF hRa",
             "  simp only [List.length_cons, List.length_nil, List.take, List.cons.injEq, and_true] at hargs",
             f"  obtain ⟨{', '.join(f'ha{i}' for i in range(len(params)))}⟩ := hargs",
             f"  subst pc rsp {' '.join(ABI[:len(params)])} {' '.join(CALLEE_SAVED)} mem"] + known("  ", "m0", False)
    for i, lemma in enumerate(enter_knows): ENTER += know_with(lemma, "m0", i, "  ")
    for i, (lemma, names) in enumerate(enter_opens): ENTER += open_with(lemma, names, "m0", i, "  ")
    NORM = "add_sub_lit, BitVec.add_assoc, BitVec.add_zero, BitVec.reduceAdd, BitVec.reduceSub"
    LISTS = "abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true"

    def finish(ind, out_fact):
        """The return: the contract's Post of the state run to."""
        t = [f"{ind}refine runs_done ⟨rfl, by simp only [{CNAME}, Abi.Contract.framed]; bv_decide, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩",
             f"{ind}all_goals try dsimp only"]
        t += [f"{ind}· intro x hx hmod", f"{ind}  exact {out_fact} x hx hmod"] if out_fact else outside_goal(ind, False)
        t += [f"{ind}· simp only [{OPEN_C}]"]
        t += [f"{ind}  apply {LEAVE} <;> mem_auto"] if LEAVE else [f"{ind}  repeat' (with_reducible apply And.intro)", f"{ind}  all_goals (first | trivial | assumption)"]
        return t

    def leaf(ev, ind):
        if not any(e[0] == "call" for e in ev):
            return run_piece(ev, ENTRY, "ret", [], ind) + finish(ind, None)
        # calls of our own functions, each by its contract: the state at a return is known by what the contract
        # promises; what holds of its memory is said again (the frame's cells, what is kept, the bytes outside)
        pieces, calls = segments(ENTRY, ev, "ret")
        call_stmts = [s for s in body if s[0] == "call"]
        assert len(call_stmts) == len(calls) == len(own_calls), "calls under conditions: not yet"
        ras = [int(n, 16) for a, n, ins in rows if ins.startswith(".call")]
        slots = [(F, "ra")] + [(F - 8 * (i + 1), f"sv.{r}") for i, r in enumerate(saved)] + [(o, p_) for p_, o in param_slot]
        t, prev = [], "m0"
        for i, ((sym, target), stmt, oc) in enumerate(zip(calls, call_stmts, own_calls), 1):
            callee, info = OWN[sym]
            assert callee == oc["callee"] and target == info["at"], (callee, oc, hex(target))
            args = " ".join([lean_low(a, base_env) for a in stmt[2]] + oc["with"])
            CK, OPENK = f"{info['contract']} {args}", f"{info['contract']}, {LISTS}"
            st = "⟨" + ", ".join(f"{r}_{i}" for r in REGS) + f", zf_{i}, cf_{i}, " + ", ".join(f"y{i}_{j}" for j in range(16)) + f", mem{i}, pc_{i}⟩"
            hs = f"hpc{i} hsp{i} hbx{i} hbp{i} h12_{i} h13_{i} h14_{i} h15_{i} hens{i} hout{i} hown{i}"
            t += [f"{ind}refine runs_then (a := {pieces[i - 1]}) (s1 := ?_) ?_ ?_", f"{ind}case refine_2 => run_fn []; rfl",
                  f"{ind}refine Abi.call_meets (c := {CK}) (ra := {ras[i - 1]}#64)",
                  f"{ind}  (Abi.Meets.mono Code_{name}.has_{info['code']} ({info['theorem']} {args})) rfl rfl ?_ ?_ ?_ ?_ ?_ ?_",
                  f"{ind}· dsimp only; mem_fact",
                  f"{ind}· dsimp only [{info['contract']}]; mem_subregion",
                  f"{ind}· dsimp only",
                  f"{ind}  simp only [{OPENK}, Abi.AllApart, Abi.Apart, BitVec.reduceAdd]",
                  f"{ind}  try simp only [{NORM}]",
                  f"{ind}  repeat' (with_reducible apply And.intro)",
                  f"{ind}  all_goals bv_decide",
                  f"{ind}· simp only [{info['contract']}]",
                  f"{ind}  repeat' (with_reducible apply And.intro)",
                  f"{ind}  all_goals assumption",
                  f"{ind}· dsimp only",
                  f"{ind}  simp only [{OPENK}]",
                  f"{ind}  repeat' (with_reducible apply And.intro)",
                  f"{ind}  all_goals (first | mem_auto | (apply_frame <;> mem_auto))",
                  f"{ind}· intro s{i} {hs}"]
            ind += "  "
            t += [f"{ind}obtain {st} := s{i}",
                  f"{ind}dsimp only at {hs}",
                  f"{ind}subst pc_{i} rsp_{i} rbx_{i} rbp_{i} r12_{i} r13_{i} r14_{i} r15_{i}",
                  f"{ind}simp only [{OPENK}] at hens{i}",
                  f"{ind}split_ands hens{i}",
                  f"{ind}simp only [{OPENK}, {NORM}] at hout{i}",
                  f"{ind}have hF{i} : Region mem{i} fb {F}#64 := hown{i} fb {F}#64 (by mem_region)"]
            for j, (off, v) in enumerate(slots):
                t.append(f"{ind}have hS{i}_{j} : Quad mem{i} {at(off)} {v} := X86.Quad.frame (by mem_fact) (fun x hx => hout{i} x (by bv_decide) (by bv_decide))")
            for j, cl in enumerate(oc["keep"]):
                c = Clause(cl); prop = c.clause(base_env, f"mem{i}")
                assert c.pred, f"keep {cl}: a predicate of memory, Name(args)"
                t.append(f"{ind}have hK{i}_{j} : {prop} := {c.pred}.frame (m := {prev}) (by assumption) (fun x hx => by rw [hout{i} x (by bv_decide) (by bv_decide)]; first | rfl | mem_away)")
            t += [f"{ind}have hOut{i} : {outside.replace('s.mem x', f'mem{i} x')} := by",
                  f"{ind}  intro x hx hmod", f"{ind}  have hx' := hx", f"{ind}  have hmod' := hmod",
                  f"{ind}  simp only [{UNFOLD_X}] at hx' hmod'",
                  f"{ind}  rw [hout{i} x (by bv_decide) (by bv_decide)]",
                  f"{ind}  " + ("first | rfl | mem_away" if i == 1 else f"refine Eq.trans ?_ (hOut{i - 1} x hx hmod); first | rfl | mem_away"),
                  f"{ind}clear hout{i} hown{i}"]
            prev = f"mem{i}"
        t += [f"{ind}refine runs_then (a := {pieces[-1]}) (s1 := ?_) ?_ ?_", f"{ind}case refine_2 => run_fn []; rfl"]
        return t + finish(ind, f"hOut{len(calls)}")

    ALL = f"({' '.join(params)} : BitVec 64) " + " ".join(f"({g} : {t})" for g, t in fn_ghosts)
    L += [f"theorem whole {ARGDECL}",
          f"    (s : State) (hP : {PRE} s) : ∃ n_ s', steps Code_{name}.prog n_ s = some s' ∧ {POST} s' := by"] + ENTER + \
         tree(wp, set(), leaf, "  ") + ["",
          f"/-- **`{name}`, as assembled, meets its contract, whatever its arguments.** -/",
          f"theorem {name}_meets : ∀ {ALL},",
          f"    Abi.Meets Code_{name}.prog 0x{ENTRY:X} ({CNAME} {CARGS}) := by",
          f"  intro {CARGS}",
          f"  refine Abi.meets_of_triple {F}#64 (by dsimp only [{CNAME}]; decide) (by dsimp only [{CNAME}]; decide) (fun fb ra sv m0 => ?_)",
          "  intro s hP",
          f"  exact whole {ARGUSE} s hP", "",
          f"#print axioms {name}_meets", "", f"end Proof_{name}", ""]
    with open(out_path, "w") as f:
        f.write("\n".join(L))
    print(f"{name}: {len(rows)} instructions, frame {F} bytes, no loop; {len(wp)} way(s) through" +
          (f"; {len(own_calls)} calls by contract" if own_calls else "") + f"; wrote {out_path}")
    sys.exit(0)

# ---------------------------------------------------------------- enter
ep = paths(before, dict(base_env))
assert len(ep) == 1 and not any(e[0] == "call" for e in ep[0][0]), "a condition or a call before the loop: not yet"
L += [f"theorem enter {ARGDECL}",
      f"    (s : State) (hP : {PRE} s) : ∃ n_ s', steps Code_{name}.prog n_ s = some s' ∧ Inv {ARGUSE} s' := by",
      f"  obtain {STATE(REGS)} := s",
      "  obtain ⟨hpc, hsp, hargs, hbx, hbp, h12, h13, h14, h15, hmem, hF, hRa, hAp, hAcc, hReq⟩ := hP",
      f"  simp only [{OPEN_C}] at hpc hsp hargs hbx hbp h12 h13 h14 h15 hmem hF hRa",
      "  simp only [List.length_cons, List.length_nil, List.take, List.cons.injEq, and_true] at hargs",
      f"  obtain ⟨{', '.join(f'ha{i}' for i in range(len(params)))}⟩ := hargs",
      f"  subst pc rsp {' '.join(ABI[:len(params)])} {' '.join(CALLEE_SAVED)} mem"] + known("  ", "m0", False)
for i, (lemma, names) in enumerate(enter_opens): L += open_with(lemma, names, "m0", i, "  ")
L += run_piece(ep[0][0], ENTRY, "head", [], "  ") + prove_inv("  ", False, False) + [""]

# ---------------------------------------------------------------- what the loop's head gives
head_names = [next((x for x in live if home[x] == r), r) for r in REGS]
inv_names = ["hpc", "hsp"] + [f"hp{i}" for i in range(len(param_reg))] + [f"hu{i}" for i in range(len(unpushed))] + [n for _, _, n in inv_mem] + \
    [g for g, _ in loop_ghosts] + [f"hZ{i}" for i in range(len(inv_frozen))] + [f"hI{i}" for i in range(len(inv_user))]
on_state = ["hpc", "hsp"] + [f"hp{i}" for i in range(len(param_reg))] + [f"hu{i}" for i in range(len(unpushed))] + \
    [n for c, _, n in inv_mem if "s." in c] + [f"hZ{i}" for i in range(len(inv_frozen))] + [f"hI{i}" for i, c in enumerate(inv_clauses) if "s." in c]
env_h = env_at(lambda x: x)
frozen_reg = [home[x] for x in frozen if slot_of(x) is None]
open_head = [f"  obtain {STATE(head_names)} := s", f"  obtain ⟨{', '.join(inv_names)}⟩ := hI",
             f"  simp only at {' '.join(on_state)} hc",
             f"  subst pc rsp {' '.join([r for _, r in param_reg] + unpushed + frozen_reg)}".rstrip()] + known("  ", "mem", True)
wc_env = dict(env_h)
measure_reg = home[decreases]; assert slot_of(decreases) is None

# ---------------------------------------------------------------- turn
turn_open = []
for i, (lemma, names) in enumerate(opens): turn_open += open_with(lemma, names, "mem", i, "  ")
for i, a in enumerate(asserts):
    turn_open.append(f"  have as{i} : {Clause(a).clause(env_h, '?')} := by bv_decide")
tp = [([("cond", wcond, True, False, wc_env)] + ev, e) for ev, e in paths(wbody, wc_env)]
L += [f"theorem turn {ARGDECL}",
      f"    (s : State) (hI : Inv {ARGUSE} s) (hc : {cond_prop(wcond, env_s)}) :",
      f"    ∃ n_ s', steps Code_{name}.prog n_ s = some s' ∧ (Inv {ARGUSE} s' ∧ s'.{measure_reg}.toNat < s.{measure_reg}.toNat) := by"] + open_head + turn_open + \
     tree(tp, set(), lambda ev, ind: run_piece(ev, HEAD, "head", [f"as{i}" for i in range(len(asserts))], ind) + prove_inv(ind, True, True), "  ") + [""]

# ---------------------------------------------------------------- leave
lp = [([("cond", wcond, False, False, wc_env)] + ev, e) for ev, e in paths(after, wc_env)]
assert len(lp) == 1 and not any(e[0] == "call" for e in lp[0][0]), "a condition or a call after the loop: not yet"
L += [f"theorem leave {ARGDECL}",
      f"    (s : State) (hI : Inv {ARGUSE} s) (hc : ¬ {cond_prop(wcond, env_s)}) :",
      f"    ∃ n_ s', steps Code_{name}.prog n_ s = some s' ∧ {POST} s' := by"] + open_head + \
     run_piece(lp[0][0], HEAD, "ret", [], "  ") + \
     [f"  refine runs_done ⟨rfl, by simp only [{CNAME}, Abi.Contract.framed]; bv_decide, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩", "  all_goals try dsimp only"] + \
     outside_goal("  ", True) + [f"  · simp only [{OPEN_C}]", f"    apply {LEAVE} <;> mem_auto", ""]

# ---------------------------------------------------------------- the theorem
ALL = f"({' '.join(params)} : BitVec 64) " + " ".join(f"({g} : {t})" for g, t in fn_ghosts)
L += [f"/-- **`{name}`, as assembled, meets its contract, whatever its arguments.** -/",
      f"theorem {name}_meets : ∀ {ALL},",
      f"    Abi.Meets Code_{name}.prog 0x{ENTRY:X} ({CNAME} {CARGS}) := by",
      f"  intro {CARGS}",
      f"  refine Abi.meets_of_triple {F}#64 (by dsimp only [{CNAME}]; decide) (by dsimp only [{CNAME}]; decide) (fun fb ra sv m0 => ?_)",
      f"  refine Hoare.seq (Q := Inv {ARGUSE}) ?_ ?_",
      f"  · intro s hP", f"    exact enter {ARGUSE} s hP",
      f"  · refine Hoare.loop (fun s => s.{measure_reg}.toNat) (fun s hI => ?_)",
      f"    by_cases hc : {cond_prop(wcond, env_s)}",
      f"    · obtain ⟨n_, s', h, hi, hm⟩ := turn {ARGUSE} s hI hc", "      exact ⟨n_, s', h, Or.inl ⟨hi, hm⟩⟩",
      f"    · obtain ⟨n_, s', h, hq⟩ := leave {ARGUSE} s hI hc", "      exact ⟨n_, s', h, Or.inr hq⟩", "",
      f"#print axioms {name}_meets", "", f"end Proof_{name}", ""]
with open(out_path, "w") as f:
    f.write("\n".join(L))
print(f"{name}: {len(rows)} instructions, frame {F} bytes, loop head 0x{HEAD:X}; {len(tp)} ways through a turn; wrote {out_path}")
