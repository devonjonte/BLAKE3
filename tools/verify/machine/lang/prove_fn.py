#!/usr/bin/env python3
"""The compiler's other output for a word-level function: the proof that it meets its statement.

usage: prove_fn.py SOURCE.ode NAME ROWS LAYOUT OUT.lean

A function's statement is written in Lean, by hand, for a reader (`Spec_NAME.lean`: a contract in the
vocabulary of `Abi.lean`). The source names it (`meets CONTRACT(ghosts) as STATEMENT`) and gives the
prover what no reader needs: for its loop the `invariant` clauses and what `decreases`, and the names
of lemmas that open the statement's view of memory at entry, close it at the end, and carry a clause
across a turn. ROWS is the lifter's reading of the assembled object; LAYOUT is what the compiler printed
about where it put things.

This writes, with nothing left for a person to fill in:

  Inv              what holds at the loop's head, on the machine's state: the invariant with every
                   variable replaced by the register or frame slot the compiler gave it, and around it
                   what the compiler itself keeps (the frame owned, the caller's registers and return
                   address saved in it, every byte outside the frame and what may be modified as it was);
  enter, turn, leave   the three straight-line pieces of a function with one loop, each proved by
                   running its instructions on symbolic memory (Cells.lean's run_fn), with an external
                   function's contract at each call, split on the conditions the invariant does not settle;
  NAME_meets : STATEMENT   by Abi.meets_of_triple, Hoare.seq and Hoare.loop.

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
assert len(loops) == 1, "one loop, for now"
loop = loops[0]
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


C0 = 8 if has_call(body) else 0          # where a callee's return address goes, below the frame
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
assert len(back) == 1, "one loop"
HEAD = back[0][1]
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

    def clause(self, env, mem, preds):
        if self.peek() in preds:                       # a predicate over memory
            p = self.take(); return f"{p} {mem} " + " ".join(self.args(env, mem))
        if self.peek() in ("vec", "u64"):
            kind = self.take(); self.take("["); a = self.expr(env, mem); self.take("]"); self.take("=="); v = self.expr(env, mem)
            return f"{'Vec' if kind == 'vec' else 'Quad'} {mem} {a} {v}"
        a = self.expr(env, mem)
        if self.peek() is None: return a[1:-1] if a.startswith("(") else a      # a predicate that is not about memory
        op = self.take(); b = self.expr(env, mem)
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


# ---------------------------------------------------------------- the contract's parts
TYPES = {"vec": "V", "word": "BitVec 64"}
def ghosts(items):
    out = []
    for word, rest in items:
        if word == "ghost":
            for g in rest.split(","):
                n, t = [x.strip() for x in g.split(":")]; out.append((n, TYPES.get(t, t)))
    return out


specs = [rest for word, rest in head if word == "spec"]
fn_ghosts, loop_ghosts = ghosts(head), ghosts(loop)
preds, pred_cells, pred_frame = [], {}, {}
for word, rest in head:
    if word == "predicate":
        f = rest.split(); preds.append(f[0])
        for k, v in zip(f[1::2], f[2::2]):
            (pred_cells if k == "cells" else pred_frame)[f[0]] = v
meets = [rest for word, rest in head if word == "meets"]
assert len(meets) == 1, "the function must name its statement: meets CONTRACT(ghost: Type, ...) as STATEMENT"
mm = re.match(r"^([\w.]+)\((.*)\)\s+as\s+([\w.]+)$", meets[0]); assert mm, meets[0]
CNAME, STATEMENT = mm.group(1), mm.group(3)
fn_ghosts = [(g.split(":")[0].strip(), TYPES.get(g.split(":")[1].strip(), g.split(":")[1].strip())) for g in mm.group(2).split(",") if g.strip()]
enter_opens = [re.match(r"^open\s+([\w.]+)\s+as\s+(.*)$", rest).groups() for word, rest in head if word == "enter"]
leave_by = [re.match(r"^by\s+([\w.]+)$", rest).group(1) for word, rest in head if word == "leave"]
assert len(leave_by) == 1, "the function must name the lemma that gives its ensures when the loop ends: leave by LEMMA"
invariants = [split_by(rest) for word, rest in loop if word == "invariant"]
decreases = [rest for word, rest in loop if word == "decreases"][0]
opens = [rest for word, rest in loop if word == "open"]
asserts = [rest for word, rest in loop if word == "assert"]

# where the loop is in the function
wi = next(i for i, s in enumerate(body) if s[0] == "while")
before, wcond, wbody, after = body[:wi], body[wi][1], body[wi][2], body[wi + 1:]


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


assert not (sets(body) & set(params)), "a parameter is assigned: not yet"
changed = sets(wbody)                                   # variables the loop assigns
def mentions(s, x):
    """Does this statement read or set x anywhere?"""
    k = s[0]
    if k == "ite": return x in reads(s[1][1]) | reads(s[1][2]) or any(mentions(y, x) for y in s[2] + s[3])
    if k == "while": return x in reads(s[1][1]) | reads(s[1][2]) or any(mentions(y, x) for y in s[2])
    if k == "call": return any(x in reads(a) for a in s[2])
    if k == "set": return s[1] == x or x in reads(s[2])
    return any(x in reads(e) for e in s[1:] if isinstance(e, tuple))


first_use = {}                                          # is a changed variable read before the body sets it?
for s_ in wbody:
    for x in changed:
        if x in first_use or not mentions(s_, x): continue
        first_use[x] = "set" if (s_[0] == "set" and s_[1] == x and x not in reads(s_[2])) else "read"
live = {x for x in changed if x in reads(wcond[1]) | reads(wcond[2]) | reads(fn["ret"]) or first_use.get(x) == "read"}
for x in live: assert slot_of(x) is None, f"{x} changes in the loop and lives in the frame: not yet"
# a variable set before the loop and not in it: the invariant must say what it is (`invariant x == E`)
frozen = {}
base_env = {p: p for p in params}
base_env.update({g: g for g, _ in fn_ghosts})
for cl, _ in invariants:
    m = re.match(r"^(\w+)\s*==\s*(.*)$", cl)
    if m and m.group(1) in fn["locals"] and m.group(1) not in changed:
        frozen[m.group(1)] = Clause(m.group(2)).expr(base_env, "?")
for x in sets(before): assert x in frozen or x in changed, f"the invariant must say what {x} is (invariant {x} == ...)"
inv_user = [(cl, by) for cl, by in invariants if not (re.match(r"^(\w+)\s*==", cl) and re.match(r"^(\w+)", cl).group(1) in frozen)]


def env_at(reg):
    """Each variable as a Lean term at the loop's head; `reg` gives a register-homed variable's term."""
    env = dict(base_env); env.update(frozen)
    for x in live: env[x] = reg(x)
    env.update({g: g for g, _ in loop_ghosts})
    return env


# ---------------------------------------------------------------- the three predicates
C = f"({CNAME} {' '.join(params + [g for g, _ in fn_ghosts])})"        # the contract, as the statement applies it
UNFOLD = f"{CNAME}, Abi.AllApart, Abi.Apart, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, BitVec.reduceAdd"
UNFOLD_X = f"{CNAME}, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, BitVec.reduceAdd"
CALLEE_SAVED = ["rbx", "rbp", "r12", "r13", "r14", "r15"]
ARGDECL = f"(fb {' '.join(params)} ra : BitVec 64) (sv : Abi.Saved) " + " ".join(f"({g} : {t})" for g, t in fn_ghosts) + " (m0 : Mem)"
ARGUSE = " ".join(["fb"] + params + ["ra", "sv"] + [g for g, _ in fn_ghosts] + ["m0"])
PRE = f"Abi.Pre 0x{ENTRY:X} {C} fb ra sv m0"
POST = f"Abi.Post {C} fb ra sv m0"
outside = f"(∀ x : BitVec 64, {C}.stack + 8#64 ≤ x - fb → (∀ r ∈ {C}.modifies, r.2 ≤ x - r.1) → s.mem x = m0 x)"
param_reg = [(p, home[p]) for p in params if slot_of(p) is None]
param_slot = [(p, slot_of(p)) for p in params if slot_of(p) is not None]
unpushed = [r for r in CALLEE_SAVED if r not in saved]

# the invariant on the machine's state: (text, how it is proved of a state that was run to, its name when taken apart)
inv_fixed = [f"s.pc = 0x{HEAD:X}", f"s.rsp = {at(C0)}"] + [f"s.{r} = {p}" for p, r in param_reg] + [f"s.{r} = sv.{r}" for r in unpushed]
inv_mem = [(f"Region s.mem fb {F}#64", "mem_region", "hF"), (f"Quad s.mem (fb + {F}#64) ra", "mem_fact", "hRa")] + \
    [(f"Quad s.mem (fb + {F - 8 * (i + 1)}#64) sv.{r}", "mem_fact", f"hS{i}") for i, r in enumerate(saved)] + \
    [(f"Quad s.mem {at(o)} {p}", "mem_fact", f"hPs{i}") for i, (p, o) in enumerate(param_slot)] + \
    [(f"Abi.AllApart ((fb, {C}.stack + 8#64) :: {C}.regions)", "exact hAp0", "hAp"), (outside, None, "hOut")]
inv_frozen = [(f"s.{home[x]} = {e}" if slot_of(x) is None else f"Quad s.mem {at(slot_of(x))} {e}", slot_of(x) is None) for x, e in frozen.items()]
env_s = env_at(lambda x: f"s.{home[x]}")
inv_clauses = [Clause(cl).clause(env_s, "s.mem", preds) for cl, _ in inv_user]
ex = "".join(f"({g} : {t}) " for g, t in loop_ghosts)
inv_inner = " ∧\n    ".join([c for c, _ in inv_frozen] + inv_clauses)

L = ["import Cells", "import Kernels", "import AbiProof"] + [f"import {s}" for s in specs] + [f"import Code_{name}", "open X86 Cells", "",
     f"/-! # `{name}`, as assembled, meets its statement `{STATEMENT}`", "",
     f"Written by prove_fn.py from {src.split('/')[-1]} and the compiler's layout; not edited by hand, and not to be read:",
     f"Lean checks that it proves the statement. The frame: {F} bytes below the stack pointer at entry (`fb` is its",
     f"lowest address), the caller's {', '.join(saved)} at its top.", "-/", "",
     f"namespace Proof_{name}", "", "set_option maxRecDepth 1000000", "set_option maxHeartbeats 0", "set_option linter.unusedVariables false", "",
     f"/-- What holds each time the loop's head is reached: the source's `invariant` clauses, each variable where the",
     f"compiler keeps it, and the frame as the compiler keeps it. -/",
     f"def Inv {ARGDECL} (s : State) : Prop :=\n  " + " ∧\n  ".join(inv_fixed + [c for c, _, _ in inv_mem]) + " ∧\n  " + (f"∃ {ex}, " if ex else "") + inv_inner, ""]

STATE = lambda names: "⟨" + ", ".join(names) + f", zf, cf, {', '.join(XS.split())}, mem, pc⟩"
INTROS = "intro rax' rcx' rdx' rsi' rdi' r8' r9' zf' cf' y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15"
DEFAULT = "first | rfl | mem_auto" + "".join(f" | (apply {f} <;> mem_auto)" for f in pred_frame.values())


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
    for cl, by in inv_user:
        t.append(f"{ind}  · apply {by} <;> mem_auto" if (turn and by) else f"{ind}  · {DEFAULT}")
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


def known(ind):
    """What is at hand before a piece is run: the regions apart, and what the holder of each memory predicate knows."""
    t = [f"{ind}have hAp0 := hAp", f"{ind}simp only [{UNFOLD}] at hAp", f"{ind}split_ands hAp"]
    for i, lemma in enumerate(pred_cells.values()):
        t += [f"{ind}have hK{i} := {lemma} (by assumption)", f"{ind}split_ands hK{i}"]
    return t


# ---------------------------------------------------------------- enter
ep = paths(before, dict(base_env))
assert len(ep) == 1 and not any(e[0] == "call" for e in ep[0][0]), "a condition or a call before the loop: not yet"
arg_names = [f"ha{i}" for i in range(len(params))]
L += [f"theorem enter {ARGDECL}",
      f"    (s : State) (hP : {PRE} s) : ∃ n_ s', steps Code_{name}.prog n_ s = some s' ∧ Inv {ARGUSE} s' := by",
      f"  obtain {STATE(REGS)} := s",
      "  obtain ⟨hpc, hsp, hargs, hbx, hbp, h12, h13, h14, h15, hmem, hF, hRa, hAp, hReq⟩ := hP",
      f"  simp only [{CNAME}] at hpc hsp hargs hbx hbp h12 h13 h14 h15 hmem hF hRa hReq",
      "  simp only [List.length_cons, List.length_nil, List.take, List.cons.injEq, and_true] at hargs",
      f"  obtain ⟨{', '.join(arg_names)}⟩ := hargs",
      f"  subst pc rsp {' '.join(ABI[:len(params)])} {' '.join(CALLEE_SAVED)} mem",
      "  split_ands hReq"]
for i, (lemma, names) in enumerate(enter_opens):
    L += [f"  obtain ⟨{names}, hE{i}⟩ := {lemma} (by assumption)", f"  split_ands hE{i}"]
L += known("  ") + run_piece(ep[0][0], ENTRY, "head", [], "  ") + prove_inv("  ", False, False) + [""]

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
             f"  subst pc rsp {' '.join([r for _, r in param_reg] + unpushed + frozen_reg)}".rstrip()] + known("  ")
wc_env = dict(env_h)
measure_reg = home[decreases]; assert slot_of(decreases) is None

# ---------------------------------------------------------------- turn
turn_open = []
for o in opens:
    m = re.match(r"^([\w.]+)\((.*)\)\s+as\s+(.*)$", o); lemma, conds, names = m.group(1), [c for c in m.group(2).split(",") if c.strip()], [n.strip() for n in m.group(3).split(",")]
    turn_open += [f"  obtain ⟨{', '.join(names)}, hEq, hO⟩ := {lemma} (by assumption) {' '.join(['(by bv_decide)'] * len(conds))}", "  subst hEq", "  norm_addr at hO", "  split_ands hO"]
for i, a in enumerate(asserts):
    turn_open.append(f"  have as{i} : {Clause(a).clause(env_h, '?', preds)} := by bv_decide")
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
     [f"  refine runs_done ⟨rfl, by dsimp only [{CNAME}]; bv_decide, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩", "  all_goals try dsimp only"] + \
     outside_goal("  ", True) + [f"  · dsimp only [{CNAME}]", f"    apply {leave_by[0]} <;> mem_auto", ""]

# ---------------------------------------------------------------- the theorem
L += [f"/-- **`{name}`, as assembled, meets its statement.** -/",
      f"theorem {name}_meets : {STATEMENT} := by",
      f"  intro {' '.join(params + [g for g, _ in fn_ghosts])}",
      "  refine Abi.meets_of_triple (fun fb ra sv m0 => ?_)",
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
