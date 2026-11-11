#!/usr/bin/env python3
"""The compiler's other output for a word-level function: the theorem its contract makes, and the proof.

usage: prove_fn.py SOURCE.ode NAME ROWS LAYOUT OUT.lean

SOURCE's function NAME carries a contract (see odec.py's contracts_of): what a caller owes (`requires`),
what it gets (`ensures`), and for its loop what holds at the head (`invariant`) and what gets smaller
(`decreases`). ROWS is the lifter's reading of the assembled object; LAYOUT is what the compiler
printed about where it put things (`lean --run HasherOde.lean layout NAME`).

This writes, with nothing left for a person to fill in:

  Pre, Inv, Post   predicates on the machine's state: the clauses with every variable replaced by the
                   register or frame slot the compiler gave it, and around them what the compiler itself
                   keeps: the frame owned, the caller's registers and return address saved in it, every
                   byte outside the frame and the `modifies` regions as it was;
  enter, turn, leave   the three straight-line pieces of a function with one loop, each proved by
                   running its instructions on symbolic memory (Cells.lean's run_fn), with an external
                   function's contract at each call, split on the conditions the invariant does not settle;
  NAME_meets_its_contract   Hoare.Triple prog Pre Post, by Hoare.seq and Hoare.loop.

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
regions = {}
for word, rest in head:
    if word == "region":
        for m in re.finditer(r"(\w+)\[(\d+)\]", rest): regions[m.group(1)] = int(m.group(2))
modifies = [r.strip() for word, rest in head if word == "modifies" for r in rest.split(",")]
requires = [rest for word, rest in head if word == "requires"]
ensures = [split_by(rest) for word, rest in head if word == "ensures"]
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
ARGS = ["fb"] + params + ["ra"] + [f"sv_{r}" for r in saved]
ARGDECL = f"({' '.join(ARGS)} : BitVec 64) " + " ".join(f"({g} : {t})" for g, t in fn_ghosts) + " (m0 : Mem)"
ARGUSE = " ".join(ARGS + [g for g, _ in fn_ghosts] + ["m0"])
outside = f"(∀ x : BitVec 64, {F + 8}#64 ≤ x - fb → " + "".join(f"{regions[r]}#64 ≤ x - {r} → " for r in modifies) + "s.mem x = m0 x)"
param_reg = [(p, home[p]) for p in params if slot_of(p) is None]
param_slot = [(p, slot_of(p)) for p in params if slot_of(p) is not None]

pure_req, mem_req = [], []
for r in requires:
    c = Clause(r)
    (mem_req if (c.peek() in preds or c.peek() in ("vec", "u64")) else pure_req).append(r)
pre_parts = [f"s.pc = 0x{ENTRY:X}", f"s.rsp = fb + {F}#64"] + [f"s.{ABI[i]} = {p}" for i, p in enumerate(params)] + \
    [f"s.{r} = sv_{r}" for r in saved] + ["s.mem = m0", f"Region m0 fb {F}#64", f"Quad m0 (fb + {F}#64) ra"] + \
    [Clause(r).clause(base_env, "m0", preds) for r in mem_req]
inv_fixed = [f"s.pc = 0x{HEAD:X}", f"s.rsp = {at(C0)}"] + [f"s.{r} = {p}" for p, r in param_reg]
inv_mem = [f"Region s.mem fb {F}#64", f"Quad s.mem (fb + {F}#64) ra"] + \
    [f"Quad s.mem (fb + {F - 8 * (i + 1)}#64) sv_{r}" for i, r in enumerate(saved)] + [f"Quad s.mem {at(o)} {p}" for p, o in param_slot] + [outside]
inv_frozen = [(f"s.{home[x]} = {e}" if slot_of(x) is None else f"Quad s.mem {at(slot_of(x))} {e}", slot_of(x) is None) for x, e in frozen.items()]
env_s = env_at(lambda x: f"s.{home[x]}")
inv_clauses = [Clause(cl).clause(env_s, "s.mem", preds) for cl, _ in inv_user]
ex = "".join(f"({g} : {t}) " for g, t in loop_ghosts)
inv_inner = " ∧\n    ".join([c for c, _ in inv_frozen] + inv_clauses)
post_env = dict(base_env); post_env["result"] = "s.rax"
post_parts = ["s.pc = ra.toNat", f"s.rsp = fb + {F + 8}#64"] + [f"s.{r} = sv_{r}" for r in saved] + [outside] + \
    [Clause(cl).clause(post_env, "s.mem", preds) for cl, _ in ensures]

# hypotheses of every piece: the pure requirements, and that the regions and the frame are apart
HYP = [(f"hq{i}", Clause(r).clause(base_env, "?", preds)) for i, r in enumerate(pure_req)]
rs = list(regions.items())
HYP += [(f"ap_fb_{r}", f"{F + 8}#64 ≤ {r} - fb ∧ {n}#64 ≤ fb - {r}") for r, n in rs]
HYP += [(f"ap_{a}_{b}", f"{na}#64 ≤ {b} - {a} ∧ {nb}#64 ≤ {a} - {b}") for i, (a, na) in enumerate(rs) for b, nb in rs[i + 1:]]
HYPDECL = " ".join(f"({n} : {t})" for n, t in HYP)
HYPUSE = " ".join(n for n, _ in HYP)

L = [f"import Cells", "import Kernels"] + [f"import {s}" for s in specs] + [f"import Code_{name}", "open X86 Cells", "",
     f"/-! # `{name}`, as assembled, meets the contract its source states", "",
     f"Written by prove_fn.py from the clauses in {src.split('/')[-1]} and the compiler's layout; not edited by hand.",
     f"The frame: {F} bytes below the stack pointer at entry (`fb` is its lowest address), "
     f"the caller's {', '.join(saved)} at its top.", "-/", "",
     f"namespace Proof_{name}", "", "set_option maxRecDepth 1000000", "set_option maxHeartbeats 0", "set_option linter.unusedVariables false", "",
     f"/-- What a caller owes: the `requires` clauses about memory, and the machine at the function's first instruction. -/",
     f"def Pre {ARGDECL} (s : State) : Prop :=\n  " + " ∧\n  ".join(pre_parts), "",
     f"/-- What holds each time the loop's head is reached: the `invariant` clauses, each variable where the",
     f"compiler keeps it, and the frame as the compiler keeps it. -/",
     f"def Inv {ARGDECL} (s : State) : Prop :=\n  " + " ∧\n  ".join(inv_fixed + inv_mem) + " ∧\n  " + (f"∃ {ex}, " if ex else "") + inv_inner, "",
     f"/-- What the caller gets: the `ensures` clauses, its registers and stack pointer back, and no byte changed",
     f"outside the frame and what the function may modify. -/",
     f"def Post {ARGDECL} (s : State) : Prop :=\n  " + " ∧\n  ".join(post_parts), ""]

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


def prove_inv(ind, old_outside, turn):
    """The invariant of the state reached: each part by the tactic its kind takes."""
    n_ex = len(loop_ghosts)
    t = [f"{ind}refine runs_done " + ("⟨" if turn else "") + "⟨" + ", ".join(["rfl"] * len(inv_fixed) + ["?_"] * (len(inv_mem) + 1)) + "⟩" + (", ?_⟩" if turn else ""),
         f"{ind}all_goals dsimp only", f"{ind}· mem_region"] + [f"{ind}· mem_fact"] * (len(inv_mem) - 2)
    hs = " ".join(f"hx{i}" for i in range(1 + len(modifies)))
    t += [f"{ind}· intro x {hs}"] + ([f"{ind}  refine Eq.trans ?_ (hOut x {hs})"] if old_outside else []) + [f"{ind}  mem_away"]
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
    return [f"{ind}by_cases hs{idx} : {cond_prop(e[1], e[4])}"] + \
        [f"{ind}·" + tree(yes, done | {idx}, leaf, ind + "  ")[0][len(ind) + 1:]] + tree(yes, done | {idx}, leaf, ind + "  ")[1:] + \
        [f"{ind}·" + tree(no, done | {idx}, leaf, ind + "  ")[0][len(ind) + 1:]] + tree(no, done | {idx}, leaf, ind + "  ")[1:]


def cells_of(hyps, ind):
    """What the holder of each memory predicate knows at once."""
    t = []
    for h, clause in hyps:
        p = clause.split()[0]
        if p in pred_cells: t += [f"{ind}have {h}c := {pred_cells[p]} {h}", f"{ind}split_ands {h}c"]
    return t


# ---------------------------------------------------------------- enter
entry_names = list(REGS)
mem_hyps = [(f"hR{i}", Clause(r).clause(base_env, "m0", preds)) for i, r in enumerate(mem_req)]
pre_names = ["hpc", "hsp"] + [f"ha{i}" for i in range(len(params))] + [f"hv{i}" for i in range(len(saved))] + ["hmem", "hF", "hRa"] + [h for h, _ in mem_hyps]
ep = paths(before, dict(base_env))
assert len(ep) == 1 and not any(e[0] == "call" for e in ep[0][0]), "a condition or a call before the loop: not yet"
L += [f"theorem enter {ARGDECL} {HYPDECL}",
      f"    (s : State) (hP : Pre {ARGUSE} s) : ∃ k s', steps Code_{name}.prog k s = some s' ∧ Inv {ARGUSE} s' := by",
      f"  obtain {STATE(entry_names)} := s", f"  obtain ⟨{', '.join(pre_names)}⟩ := hP",
      f"  simp only at {' '.join(pre_names[:pre_names.index('hmem') + 1])}",
      f"  subst pc rsp {' '.join(ABI[:len(params)])} {' '.join(saved)} mem"] + cells_of(mem_hyps, "  ") + \
     run_piece(ep[0][0], ENTRY, "head", [], "  ") + prove_inv("  ", False, False) + [""]

# ---------------------------------------------------------------- what the loop's head gives
head_names = [next((x for x in live if home[x] == r), r) for r in REGS]
inv_names = ["hpc", "hsp"] + [f"hp{i}" for i in range(len(param_reg))] + ["hF", "hRa"] + [f"hS{i}" for i in range(len(saved))] + \
    [f"hPs{i}" for i in range(len(param_slot))] + ["hOut"] + [g for g, _ in loop_ghosts] + [f"hZ{i}" for i in range(len(inv_frozen))] + [f"hI{i}" for i in range(len(inv_user))]
env_h = env_at(lambda x: x)
inv_hyps = [(f"hI{i}", Clause(cl).clause(env_h, "mem", preds)) for i, (cl, _) in enumerate(inv_user)]
frozen_reg = [home[x] for x in frozen if slot_of(x) is None]
open_head = [f"  obtain {STATE(head_names)} := s", f"  obtain ⟨{', '.join(inv_names)}⟩ := hI",
             f"  simp only at {' '.join(n for n in inv_names if n.startswith('h'))} hc",
             f"  subst pc rsp {' '.join(r for _, r in param_reg)} {' '.join(frozen_reg)}".rstrip()] + cells_of(inv_hyps, "  ")
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
L += [f"theorem turn {ARGDECL} {HYPDECL}",
      f"    (s : State) (hI : Inv {ARGUSE} s) (hc : {cond_prop(wcond, env_s)}) :",
      f"    ∃ k s', steps Code_{name}.prog k s = some s' ∧ (Inv {ARGUSE} s' ∧ s'.{measure_reg}.toNat < s.{measure_reg}.toNat) := by"] + open_head + turn_open + \
     tree(tp, set(), lambda ev, ind: run_piece(ev, HEAD, "head", [f"as{i}" for i in range(len(asserts))], ind) + prove_inv(ind, True, True), "  ") + [""]

# ---------------------------------------------------------------- leave
lp = [([("cond", wcond, False, False, wc_env)] + ev, e) for ev, e in paths(after, wc_env)]
assert len(lp) == 1 and not any(e[0] == "call" for e in lp[0][0]), "a condition or a call after the loop: not yet"
hs = " ".join(f"hx{i}" for i in range(1 + len(modifies)))
L += [f"theorem leave {ARGDECL} {HYPDECL}",
      f"    (s : State) (hI : Inv {ARGUSE} s) (hc : ¬ {cond_prop(wcond, env_s)}) :",
      f"    ∃ k s', steps Code_{name}.prog k s = some s' ∧ Post {ARGUSE} s' := by"] + open_head + \
     run_piece(lp[0][0], HEAD, "ret", [], "  ") + \
     ["  refine runs_done ⟨" + ", ".join(["rfl"] * (2 + len(saved)) + ["?_"] * (1 + len(ensures))) + "⟩", "  all_goals dsimp only",
      f"  · intro x {hs}", f"    refine Eq.trans ?_ (hOut x {hs})", "    first | rfl | mem_away"] + \
     [f"  · apply {by} <;> mem_auto" if by else f"  · {DEFAULT}" for _, by in ensures] + [""]

# ---------------------------------------------------------------- the theorem
doc = [f"/-- **`{name}`, as assembled, meets its contract.** From any state at its first instruction in which the", "`requires` clauses hold"]
L += [f"/-- **`{name}`, as assembled, meets its contract.** From any state at its first instruction where the `requires`",
      f"clauses hold (and the frame's {F} bytes are owned and apart from the regions the contract names), the",
      f"{len(rows)} instructions run without a fault, through however many turns of the loop, to the caller's return",
      f"address, where the `ensures` clauses hold. -/",
      f"theorem {name}_meets_its_contract {ARGDECL} {HYPDECL} :",
      f"    Hoare.Triple Code_{name}.prog (Pre {ARGUSE}) (Post {ARGUSE}) := by",
      f"  refine Hoare.seq (Q := Inv {ARGUSE}) ?_ ?_",
      f"  · intro s hP", f"    exact enter {ARGUSE} {HYPUSE} s hP",
      f"  · refine Hoare.loop (fun s => s.{measure_reg}.toNat) (fun s hI => ?_)",
      f"    by_cases hc : {cond_prop(wcond, env_s)}",
      f"    · obtain ⟨k, s', h, hi, hm⟩ := turn {ARGUSE} {HYPUSE} s hI hc", "      exact ⟨k, s', h, Or.inl ⟨hi, hm⟩⟩",
      f"    · obtain ⟨k, s', h, hq⟩ := leave {ARGUSE} {HYPUSE} s hI hc", "      exact ⟨k, s', h, Or.inr hq⟩", "",
      f"#print axioms {name}_meets_its_contract", "", f"end Proof_{name}", ""]
with open(out_path, "w") as f:
    f.write("\n".join(L))
print(f"{name}: {len(rows)} instructions, frame {F} bytes, loop head 0x{HEAD:X}; {len(tp)} ways through a turn; wrote {out_path}")
