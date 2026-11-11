#!/usr/bin/env python3
"""From the functions written in Lang.lean to checked theorems about their machine code.

  1. Lean prints the Rust (Lang.lean's `main`).
  2. rustc compiles it; llvm-objdump lists it.
  3. For each function this writes Code_NAME.lean (the instructions, one lemma an address) and
     Proof_NAME.lean: where the loop keeps its things (read off the listing), the proof that one
     turn of the loop is one step of the Lean function, and the whole function's theorem by the
     loop rule (Rule.lean).

Nothing written here is trusted: a wrong guess about a register is a proof that does not check.
usage: make.py [--target TRIPLE] [--objdump PATH]"""
import argparse, pathlib, re, subprocess, sys

here = pathlib.Path(__file__).resolve().parent
R64 = "rax rcx rdx rbx rsp rbp rsi rdi r8 r9".split()
REG = {}
for r in R64[:8]:
    REG[r] = (r, 64); REG["e" + r[1:]] = (r, 32)
for r in R64[8:]:
    REG[r] = (r, 64); REG[r + "d"] = (r, 32)
PTR = {"byte": 8, "dword": 32, "qword": 64}


def bv(n):
    return f"0x{n & (2**64 - 1):X}"


def operand(text):
    """(lean term, width or None, registers read to form it, is it memory)"""
    text = text.strip()
    if text in REG:
        r, w = REG[text]; return f"(.reg .{r})", w, [r], False
    m = re.fullmatch(r"(?:(byte|dword|qword) ptr )?\[(\w+) \+ (\w+)\]", text)
    if m and m.group(3) in REG:
        (base, w0), (index, w1) = REG[m.group(2)], REG[m.group(3)]; assert w0 == w1 == 64, text
        return f"(.memi .{base} .{index})", PTR.get(m.group(1)), [base, index], True
    m = re.fullmatch(r"(-?)0x([0-9a-f]+)", text)
    if m:
        v = int(m.group(2), 16); return f"(.imm {bv(-v if m.group(1) else v)})", None, [], False
    raise SystemExit(f"unknown operand: {text!r}")


class Row:
    """One instruction: where it is, what the model calls it, what it reads, writes and touches."""
    def __init__(self, at, nxt, op, args, raw):
        self.at, self.next, self.op, self.args, self.raw = at, nxt, op, args, raw
        self.reads, self.writes, self.mem, self.target = [], [], [], None
        a = [x.strip() for x in args.split(",")] if args else []
        if op in ("mov", "and", "or", "xor", "add", "test", "cmp"):
            (d, wd, rd, md), (s, ws, rs, ms) = operand(a[0]), operand(a[1]); w = wd or ws
            assert w and (not wd or not ws or wd == ws), args
            self.lean = f".{op} {w} {d} {s}"
            self.mem = (rd if md else []) and [tuple(rd)]
            self.mem = ([tuple(rd)] if md else []) + ([tuple(rs)] if ms else [])
            self.reads = list(rs) + (list(rd) if md else [])
            same = op == "xor" and not md and not ms and rd == rs
            if not md:
                if op not in ("mov",) and not same: self.reads += rd
                if op not in ("test", "cmp"): self.writes = list(rd)
            if same: self.reads = []
            self.imm = int(a[1], 16) if re.fullmatch(r"0x[0-9a-f]+", a[1]) else None
            self.dst, self.src = (rd[0] if not md else None), (rs[0] if rs and not ms else None)
        elif op in ("shr", "shl"):
            d, w, rd, md = operand(a[0]); n = int(a[1], 16); assert w and not md and 0 < n < w
            self.lean = f".{op} {w} {d} {n}"; self.reads = self.writes = list(rd)
        elif op == "rol":
            r, w = REG[a[0]]; n = int(a[1], 16) if len(a) > 1 else 1; assert w == 32 and 0 < n < 32
            self.lean = f".rol32 .{r} {n}"; self.reads = self.writes = [r]
        elif op == "not":
            d, w, rd, md = operand(a[0]); assert w and not md
            self.lean = f".not {w} {d}"; self.reads = self.writes = list(rd)
        elif op == "lea":
            r, w = REG[a[0]]; m = re.fullmatch(r"\[(\w+) \+ (\w+) ([+-]) (0x[0-9a-f]+)\]", a[1]); assert w == 32 and m, args
            (b, wb), (i, wi) = REG[m.group(1)], REG[m.group(2)]; assert wb == wi == 64
            d = int(m.group(4), 16) * (-1 if m.group(3) == "-" else 1)
            self.lean = f".lea32 .{r} .{b} .{i} {bv(d)}"; self.reads = [b, i]; self.writes = [r]
        elif op in ("je", "jne"):
            self.target = int(a[0].split()[0], 16); self.lean = None
        elif op == "jmp":
            self.target = int(a[0].split()[0], 16); self.lean = None
        elif op == "nop":
            self.lean = ".nop"
        elif op == "ret":
            assert not a; self.lean = ".ret"
        elif op in ("push", "pop"):
            r, w = REG[a[0]]; assert w == 64; self.lean = f".{op} .{r}"; self.reg = r
        else:
            raise SystemExit(f"unknown instruction: {op} {args}")

    def place(self, shift):
        self.at += shift; self.next += shift
        if self.target is not None:
            self.target += shift
            self.lean = f".jmp {bv(self.target)}" if self.op == "jmp" else f".jcc .{self.op[1:]} {bv(self.target)}"


def functions(listing):
    """{name: [Row]} with each function's first instruction at 0x1000."""
    out, name = {}, None
    for line in listing.splitlines():
        m = re.match(r"^[0-9a-f]+ <_?(.+)>:$", line)
        if m: name = m.group(1); out[name] = []; continue
        m = re.match(r"^\s+([0-9a-f]+):((?: [0-9a-f]{2})+)\s+(\S+)\s*(.*)$", line)
        if m:
            at = int(m.group(1), 16); size = len(m.group(2).split())
            out[name].append(Row(at, at + size, m.group(3), m.group(4).strip(), m.group(2).strip()))
    for rows in out.values():
        shift = 0x1000 - rows[0].at
        for r in rows: r.place(shift)
    return out


def code_file(name, rows):
    cap = name.capitalize()
    text = [f"import X86", "import Attr", "",
            f"/-! `{name}` as rustc compiled it and llvm-objdump reads it. Written by make.py; not edited by hand. -/", "",
            f"namespace Code_{cap}", "open X86", "", "def table : List (Nat × Instr × Nat) := ["]
    for i, r in enumerate(rows):
        text.append(f"  (0x{r.at:X}, {r.lean}, 0x{r.next:X}){',' if i + 1 < len(rows) else ' '}  -- {r.raw:<20} {r.op} {r.args}")
    text += ["]", "", "/-- The instruction at an address, and the address after it. -/",
             "def prog (pc : Nat) : Option (Instr × Nat) := table.lookup pc", ""]
    text += [f"@[code_at] theorem at_{r.at:X} : prog 0x{r.at:X} = some ({r.lean}, 0x{r.next:X}) := rfl" for r in rows]
    text += ["", f"end Code_{cap}", ""]
    return "\n".join(text)


def walk(rows, start, taken):
    """The instructions run from `start` to a `ret`, taking a conditional jump when `taken` says so."""
    by = {r.at: r for r in rows}; path, at = [], start
    while True:
        r = by[at]; path.append(r)
        if r.op == "ret": return path
        at = r.target if r.op == "jmp" or (r.op in ("je", "jne") and taken(r)) else r.next


def shows(path, sp, taken, stop=None):
    """What the model's observer sees along a path, newest first, as Lean; and the stack pointer's text after."""
    seen = []
    for r in path:
        if stop is not None and r.at == stop: break
        if r.op == "push": seen.append(f".addr ({sp} - 8)"); sp = f"{sp} - 8"
        elif r.op == "pop": seen.append(f".addr ({sp})"); sp = f"{sp} + 8"
        elif r.op == "ret": seen.append(f".addr ({sp})"); seen.append(".pc 0")
        elif r.op in ("je", "jne"): seen.append(f".pc 0x{(r.target if taken(r) else r.next):X}")
        else: assert not r.mem, "a memory operand outside the loop"
    return "".join(f"{x} :: " for x in reversed(seen)), sp


def proof_file(name, rows):
    cap = name.capitalize()
    back = [r for r in rows if r.op == "jne" and r.target < r.at]
    assert len(back) == 1, "one loop"
    jcc = back[0]; head, exit_ = jcc.target, jcc.next
    body = [r for r in rows if head <= r.at <= jcc.at]
    mems = [m for r in body for m in r.mem]; assert mems and len(set(mems)) == 1, "one word a turn"
    base, index = mems[0]
    cmp = [r for r in body if r.op == "cmp"]; assert len(cmp) == 1 and index in cmp[0].reads
    end = [x for x in cmp[0].reads if x != index][0]
    live, written = [], []
    for r in body:
        live += [x for x in r.reads if x not in written and x not in live]; written += r.writes
    carried = [x for x in live if x in written and x != index]
    assert len(carried) == 1, f"the carried value: {carried}"
    acc = carried[0]
    store = [r for r in body if r.op == "mov" and r.mem and r.dst is None]; assert len(store) == 1
    out = store[0].src
    # A register the loop reads and never writes, other than the slice's: a constant from the prologue.
    entry = rows[0].at
    first = [r for r in rows if r.op == "je"][0]
    pre = walk(rows, entry, lambda r: False); pre = pre[:[r.at for r in pre].index(head)]
    consts = {}
    for x in live:
        if x in written or x in (base, end): continue
        setters = [r for r in pre if r.op == "mov" and r.dst == x and r.imm is not None]
        assert len(setters) == 1, f"where is {x} set?"
        consts[x] = setters[0].imm
    good = " ∧ ".join(f"s.{x} = {bv(v)}" for x, v in consts.items()) or "True"
    assert [r.op for r in pre[:2]] == ["push", "mov"] and pre[0].reg == "rbp", "the frame this template knows"
    post = walk(rows, exit_, lambda r: False)
    empty = walk(rows, entry, lambda r: r is first)
    assert [r.op for r in post[-2:]] == ["pop", "ret"] and [r.op for r in empty[-2:]] == ["pop", "ret"]
    pre_shows, sp_head = shows(pre, "sp", lambda r: False)
    post_shows, _ = shows(post, sp_head, lambda r: False)
    empty_shows, _ = shows(empty, "sp", lambda r: r is first)
    turn_shows = "".join(".addr p, " for _ in mems)
    regs = "rax rcx rdx rbx rsp rbp rsi rdi r8 r9"
    state = lambda pc, leak, **over: "⟨" + ", ".join(over.get(r, r) for r in regs.split()) + f", zf, cf, m, {pc}, {leak}⟩"
    state2 = "⟨rax2, rcx2, rdx2, rbx, rsp - 8, rsp - 8, rsi2, rdi2, r82, r92, zf2, cf2, m2, " + f"0x{exit_:X}, leak2⟩"
    on_rsp = lambda s: s.replace("sp", "rsp")
    return f'''import Rule
import Run
import Lang
import Code_{cap}
open X86

/-! `{name}`: the machine code computes the Lean function. Written by make.py from the listing; not edited by hand. -/

namespace {cap}

abbrev prog := Code_{cap}.prog

/-- Where the compiled loop keeps its things. -/
def view : View State Obs (BitVec 64 × BitVec 64 × BitVec 64) where
  steps := steps prog
  steps_add := steps_add prog
  mem := State.mem
  pc := State.pc
  leak := State.leak
  head := 0x{head:X}
  exit := 0x{exit_:X}
  turn := {len(body)}
  acc s := s.{acc}.setWidth 32
  out s := s.{out}.setWidth 32
  ptr s := s.{base} + s.{index}
  left s := s.{end} - s.{index}
  kept s := (s.rbx, s.rsp, s.rbp)
  good {'s' if consts else '_'} := {good}
  obs p last := [.pc (if last then 0x{exit_:X} else 0x{head:X}), {turn_shows.rstrip(", ")}]

macro "close" : tactic => `(tactic| first
  | rfl | trivial | bv_decide
  | (simp only [view, {name}, Scan.step, Exp.eval]; bv_decide)
  | (apply put32_congr; simp only [view, {name}, Scan.step, Exp.eval]; bv_decide))

/-- **One turn of the compiled loop is one step of the Lean function.** -/
theorem turn : Turn view {name}.step := by
  intro ⟨{regs.replace(" ", ", ")}, zf, cf, m, pc, leak⟩ w hpc hg hw
  simp only [view] at hpc hg hw ⊢
  subst hpc
  {("subst hg" if len(consts) == 1 else "obtain ⟨" + ", ".join("h" + x for x in consts) + "⟩ := hg; subst " + " ".join("h" + x for x in consts)) if consts else "clear hg"}
  run_code [read_word hw, write_word hw]
  split
  · rename_i h
    have h4 : ¬ ({end} - {index} = 4) := by bv_decide
    simp only [h4, ↓reduceIte, decide_false]
    refine ⟨_, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> close
  · rename_i h
    have h4 : {end} - {index} = 4 := by bv_decide
    simp only [h4, ↓reduceIte, decide_true]
    refine ⟨_, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> close

/-- What a whole call shows an observer: a function of the slice's address and length and of the stack
pointer. The words and the seed are not among its arguments. -/
def leakOf (p sp : BitVec 64) : Nat → List Obs → List Obs
  | 0, seen => {empty_shows}seen
  | n + 1, seen => {post_shows}loopLeak view.obs p n ({pre_shows}seen)

/-- **The compiled `{name}` computes the Lean function `{name}`, for a slice of any length.**
Called with a slice of `ws.length` words at RDI (its bytes fewer than 2^63), the seed in EDX, a return
address on the stack, the eight bytes below it owned and the slice apart from both: it returns, with
`{name}.fold seed ws` in EAX, `{name}.scan seed ws` where the slice was, the stack pointer popped, RBX and
RBP as they were, no byte changed outside the slice and those eight, and a trace that is `leakOf` of the
slice's address and length and the stack pointer. -/
theorem {name}_is_its_lean_function (ws : List (BitVec 32)) (seed : BitVec 32)
    ({regs} : BitVec 64) (zf cf : Option Bool) (m : Mem) (leak : List Obs)
    (hlen : rsi = BitVec.ofNat 64 ws.length) (hn : 4 * ws.length < 2 ^ 63)
    (hseed : rdx.setWidth 32 = seed)
    (hws : Holds m rdi ws)
    (hret : m.read rsp 64 = some 0)
    (hstack : Owned8 m (rsp - 8))
    (hapart : ∀ x, (x - rdi).toNat < 4 * ws.length → 16 ≤ (x - (rsp - 8)).toNat) :
    ∃ s', Returns prog {state(f"0x{entry:X}", "leak")} s' ∧
      s'.rax.setWidth 32 = {name}.fold seed ws ∧ s'.rsp = rsp + 8 ∧ s'.rbx = rbx ∧ s'.rbp = rbp ∧
      Holds s'.mem rdi ({name}.scan seed ws) ∧
      (∀ x, 4 * ws.length ≤ (x - rdi).toNat → 8 ≤ (x - (rsp - 8)).toNat → s'.mem x = m x) ∧
      s'.leak = leakOf rdi rsp ws.length leak := by
  subst hseed
  have hpopm : (m.put64 (rsp - 8) rbp).read (rsp - 8) 64 = some rbp := read_put64 _ _ _
  have hretm : (m.put64 (rsp - 8) rbp).read (rsp - 8 + 8) 64 = some 0 := by
    rw [read_congr (m := m) _ (fun x hx => put64_other _ _ _ x (by bv_omega)), show rsp - 8 + 8 = rsp by bv_decide]
    exact hret
  cases ws with
  | nil =>
    -- An empty slice: {len(empty)} instructions.
    simp only [List.length_nil] at hlen
    subst hlen
    have hz : (BitVec.ofNat 64 0 &&& BitVec.ofNat 64 0 == 0) = true := by decide
    have h : ∃ s', steps prog {len(empty)} {state(f"0x{entry:X}", "leak", rsi="BitVec.ofNat 64 0")} = some s' ∧
        s'.pc = done ∧ s'.rax.setWidth 32 = rdx.setWidth 32 ∧ s'.rsp = rsp + 8 ∧ s'.rbx = rbx ∧ s'.rbp = rbp ∧
        s'.mem = m.put64 (rsp - 8) rbp ∧ s'.leak = leakOf rdi rsp 0 leak := by
      run_code [write_quad hstack, hz, hpopm, hretm]
      refine ⟨_, rfl, rfl, ?_, ?_, rfl, rfl, rfl, rfl⟩ <;> (simp only []; bv_decide)
    obtain ⟨s', hs, hpc, hax, hsp, hbx, hbp, hm, hl⟩ := h
    exact ⟨s', ⟨{len(empty)}, hs, hpc⟩, hax, hsp, hbx, hbp, trivial, fun x _ h8 => by rw [hm, put64_other _ _ _ x h8], hl⟩
  | cons w rest =>
    simp only [List.length_cons] at hlen hn hapart ⊢
    -- {len(pre)} instructions to the loop's head.
    have hnz : (rsi &&& rsi == 0) = false := by subst hlen; simp; bv_omega
    have hpre : ∃ s1, steps prog {len(pre)} {state(f"0x{entry:X}", "leak")} = some s1 ∧
        view.pc s1 = view.head ∧ view.good s1 ∧ view.acc s1 = rdx.setWidth 32 ∧ view.ptr s1 = rdi ∧
        view.left s1 = rsi * 4 ∧ view.mem s1 = m.put64 (rsp - 8) rbp ∧ view.kept s1 = (rbx, rsp - 8, rsp - 8) ∧
        view.leak s1 = {on_rsp(pre_shows)}leak := by
      run_code [write_quad hstack, hnz]
      refine ⟨_, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> close
    obtain ⟨s1, hs1, hpc1, hg1, hacc1, hptr1, hleft1, hmem1, hk1, hl1⟩ := hpre
    -- The loop, by the rule.
    have hws1 : Holds (view.mem s1) (view.ptr s1) (w :: rest) := by
      rw [hptr1, hmem1]
      exact holds_congr _ _ (by simp only [List.length_cons]; omega)
        (fun x hx => put64_other _ _ _ x (by simp only [List.length_cons] at hx; have := hapart x hx; omega)) hws
    obtain ⟨s2, hs2, hpc2, hout2, hh2, hf2, hk2, hl2⟩ :=
      loop_rule view {name}.step turn rest w s1 hpc1 hg1 hws1 (by rw [hleft1]; subst hlen; bv_omega) hn
    rw [hptr1, hacc1] at hh2
    rw [hptr1, hmem1] at hf2
    rw [hptr1, hl1] at hl2
    rw [hacc1] at hout2
    rw [hk1] at hk2
    obtain ⟨rax2, rcx2, rdx2, rbx2, rsp2, rbp2, rsi2, rdi2, r82, r92, zf2, cf2, m2, pc2, leak2⟩ := s2
    have hpc2' : pc2 = 0x{exit_:X} := hpc2
    have hk2' : (rbx2, rsp2, rbp2) = (rbx, rsp - 8, rsp - 8) := hk2
    simp only [Prod.mk.injEq] at hk2'
    obtain ⟨hb, hsp, hbp⟩ := hk2'
    subst hpc2' hsp hbp
    subst rbx2
    have hf2' : ∀ x, 4 * (rest.length + 1) ≤ (x - rdi).toNat → m2 x = (m.put64 (rsp - 8) rbp) x := hf2
    -- Outside the slice the loop changed nothing: the saved RBP and the return address are there.
    have hout : ∀ x, (x - (rsp - 8)).toNat < 16 → 4 * (rest.length + 1) ≤ (x - rdi).toNat := fun x hx =>
      Nat.le_of_not_lt (fun h => by have := hapart x h; omega)
    have hpop : m2.read (rsp - 8) 64 = some rbp := by
      rw [read_congr (m := m.put64 (rsp - 8) rbp) _ (fun x hx => hf2' x (hout x (by omega)))]; exact hpopm
    have hret2 : m2.read (rsp - 8 + 8) 64 = some 0 := by
      rw [read_congr (m := m.put64 (rsp - 8) rbp) _ (fun x hx => hf2' x (hout x (by bv_omega)))]; exact hretm
    -- {len(post)} more instructions: out of the frame, return.
    have hpost : ∃ s', steps prog {len(post)} {state2} = some s' ∧
        s'.pc = done ∧ s'.rax = rax2 ∧ s'.rsp = rsp + 8 ∧ s'.rbx = rbx ∧ s'.rbp = rbp ∧ s'.mem = m2 ∧
        s'.leak = {on_rsp(post_shows)}leak2 := by
      run_code [hpop, hret2]
      refine ⟨_, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (first | rfl | (simp only []; bv_decide))
    obtain ⟨s', hs', hpc', hax', hsp', hbx', hbp', hm', hl'⟩ := hpost
    refine ⟨s', ⟨{len(pre)} + ({len(body)} * (rest.length + 1) + {len(post)}), ?_, hpc'⟩, ?_, hsp', hbx', hbp', ?_, ?_, ?_⟩
    · rw [steps_add, hs1, Option.bind_some, steps_add,
        show steps prog ({len(body)} * (rest.length + 1)) s1 = _ from hs2, Option.bind_some, hs']
    · rw [hax']; exact hout2
    · rw [hm']; exact hh2
    · intro x hx hx8
      rw [hm', hf2' x hx, put64_other _ _ _ x hx8]
    · rw [hl']
      have e : leak2 = _ := hl2
      rw [e]; rfl

#print axioms {name}_is_its_lean_function

end {cap}
'''


def main():
    p = argparse.ArgumentParser()
    p.add_argument("--target", default="x86_64-apple-darwin")
    p.add_argument("--objdump", default="llvm-objdump")
    p.add_argument("--opt", default="s", help="rustc's opt-level")
    p.add_argument("--flag", action="append", default=[], help="another flag for rustc, e.g. -Cllvm-args=-unroll-runtime=false")
    p.add_argument("--rust", help="compile this Rust in place of what Lean prints (to test that a wrong printer is caught)")
    a = p.parse_args()
    run = lambda *c, **k: subprocess.run(c, cwd=here, check=True, capture_output=True, text=True, **k).stdout
    if not a.rust: run("lake", "build", "Fold")
    printed = pathlib.Path(a.rust).read_text() if a.rust else "#![allow(unused_parens)]\n" + run("lake", "env", "lean", "--run", "Lang.lean")
    (here / "gen.rs").write_text(printed)
    run("rustc", "--edition", "2021", "--target", a.target, "-C", f"opt-level={a.opt}", *a.flag, "-C", "panic=abort",
        "--crate-type", "lib", "--emit", "obj", "-o", "gen.o", "gen.rs")
    listing = run(a.objdump, "-d", "--x86-asm-syntax=intel", "gen.o")
    (here / "gen.listing").write_text(listing)
    names = []
    for name, rows in functions(listing).items():
        cap = name.capitalize(); names.append(cap)
        (here / f"Code_{cap}.lean").write_text(code_file(name, rows))
        (here / f"Proof_{cap}.lean").write_text(proof_file(name, rows))
        print(f"{name}: {len(rows)} instructions")
    libs = ["Bytes", "Fold", "Rule", "Lang", "Attr", "X86", "MemX", "Run"] + [f"{k}_{n}" for n in names for k in ("Code", "Proof")]
    (here / "lakefile.toml").write_text('name = "gen"\ndefaultTargets = [' + ", ".join(f'"Proof_{n}"' for n in names) + "]\n"
                                         + "".join(f'[[lean_lib]]\nname = "{l}"\n' for l in libs))


main()
