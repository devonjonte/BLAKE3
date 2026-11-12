#!/usr/bin/env python3
"""A function's checked entry: its code and the proof that it meets `CONTRACT.checked`.

usage: check_fn.py asm   SOURCE.ode NAME CHECKS                      (prints assembly to append to NAME's)
       check_fn.py proof SOURCE.ode NAME CHECKS ROWS FN_ENTRY OUT.lean

What a function requires of its arguments is stated once, in its contract's `accepts` (Lean, for a
reader). CHECKS is what `#checks CONTRACT` (Checks.lean) read out of that field: one comparison a line.
From those lines this makes the checked entry `b3l_NAME_checked`: it tests each comparison, returns
REFUSED if one fails, and otherwise jumps to the function itself. Then, from the lifter's reading of the
assembled entry (ROWS), the proof: one run for each way through the tests, handed to
Abi.checked_accepted or Abi.checked_refused. Nobody writes the tests or the proof; Lean checks that the
entry meets `(CONTRACT ...).checked REFUSED`. Nothing here is trusted."""
import re, sys
import odec

mode, src, name, checks_path = sys.argv[1:5]
REFUSED = 2**64 - 1
ABI = ["rdi", "rsi", "rdx", "rcx", "r8", "r9"]
REGS = "rax rcx rdx rbx rsp rbp rsi rdi r8 r9 r12 r13 r14 r15".split()
clauses, _, stripped = odec.contracts_of(open(src).read())
source, _, _ = odec.kernels(stripped)
P = odec.Parser(odec.tokens(source)); P.top()
params = next(f for f in P.fns if f[0] == name)[1]
meets = next(rest for w, rest in clauses[name]["head"] if w == "meets")
mm = re.match(r"^([\w.]+)\((.*)\)$", meets); CNAME = mm.group(1)
ghosts = [(g.split(":")[0].strip(), g.split(":", 1)[1].strip()) for g in mm.group(2).split(",") if g.strip()]

checks = []       # (op, left, right); an operand is ("arg", i) or ("num", n)
for line in open(checks_path):
    m = re.search(r"check (le|lt) (\S+) (\S+)", line)
    if not m: continue
    def operand(t):
        return ("num", int(t[1:])) if t[0] == "#" else ("arg", int(t[1:].split(":")[0]))
    checks.append((m.group(1), operand(m.group(2)), operand(m.group(3))))
assert checks, f"{CNAME} accepts everything: it needs no checked entry"


def asm_op(o):
    if o[0] == "arg": return ABI[o[1]]
    assert o[1] < 2**31, "a number too large for a comparison's immediate: not yet"; return str(o[1])
def lean_op(o): return params[o[1]] if o[0] == "arg" else f"{o[1]}#64"
def prop(c): return f"{lean_op(c[1])} {'≤' if c[0] == 'le' else '<'} {lean_op(c[2])}"
def first_second(c):
    """The comparison the machine makes: `cmp A, B` sets carry when A < B (unsigned)."""
    return (c[2], c[1]) if c[0] == "le" else (c[1], c[2])       # le L R: passes when not (R < L); lt L R: passes when L < R
def carry_when_passing(c): return c[0] == "lt"

if mode == "asm":
    L = [f".global b3l_{name}_checked", f".global _b3l_{name}_checked", ".p2align 4", f"b3l_{name}_checked:", f"_b3l_{name}_checked:"]
    fail = f".Lb3l_{name}_refuse"
    for i, c in enumerate(checks):
        a, b = first_second(c); assert a[0] == "arg", "a comparison whose first operand is a number: not yet"
        L.append(f"    cmp {asm_op(a)}, {asm_op(b)}")
        if carry_when_passing(c): L.append(f"    jae {fail}")
        else: L += [f"    jae .Lb3l_{name}_ok{i}", f"    jmp {fail}", f".Lb3l_{name}_ok{i}:"]
    L += [f"    jmp b3l_{name}", f"{fail}:", f"    mov rax, -1", "    ret"]
    print("\n".join(L))
    sys.exit(0)

rows_path, fn_entry, out_path = sys.argv[5], int(sys.argv[6], 0), sys.argv[7]
rows = [l.rstrip("\n").split("\t") for l in open(rows_path)]
code = {int(a, 16): (ins, int(n, 16)) for a, n, ins in rows}
ENTRY = int(rows[0][0], 16)


def steps(outcomes):
    """Instructions run when the tests come out as given (True = passes), until the function's entry or the return."""
    pc, n, k = ENTRY, 0, 0
    while True:
        if pc == fn_entry: return n
        ins, nxt = code[pc]; n += 1
        if ins == ".ret": return n
        m = re.match(r"\.(jae|jmp) 0x([0-9A-F]+)", ins)
        if not m: pc = nxt
        elif m.group(1) == "jmp": pc = int(m.group(2), 16)
        else:
            taken = outcomes[k] != carry_when_passing(checks[k]); k += 1      # jae: taken when there is no carry
            pc = int(m.group(2), 16) if taken else nxt


def fact(i, passes):
    a, b = first_second(checks[i])
    return f"({lean_op(a)}).ult ({lean_op(b)}) = {'true' if passes == carry_when_passing(checks[i]) else 'false'}"


CARGS = " ".join(params + [g for g, _ in ghosts])
ALL = f"({' '.join(params)} : BitVec 64) " + " ".join(f"({g} : {t})" for g, t in ghosts)
ACCEPTS = " ∧ ".join(prop(c) for c in checks)
XS = ", ".join(f"x{i}" for i in range(16))
n = len(checks)
L = ["import Cells", "import AbiProof", f"import Proof_{name}", "open X86 Cells", "",
     f"/-! # The checked entry of `{name}` meets `{CNAME} … |>.checked`", "",
     f"Written by check_fn.py from what `#checks {CNAME}` read in the contract; not edited by hand, and not to be read",
     "but for the theorem's statement: Lean checks the rest. -/", "",
     f"namespace Checked_{name}", "", "set_option maxRecDepth 1000000", "set_option maxHeartbeats 0", "",
     f"/-- **The checked entry of `{name}`, as assembled, meets the contract's checked form, whatever its arguments:**",
     f"it does as `{CNAME}` says where that accepts them, and returns {REFUSED} having changed nothing where it does not. -/",
     f"theorem {name}_checked_meets : ∀ {ALL},",
     f"    Abi.Meets Code_{name}.prog 0x{ENTRY:X} (({CNAME} {CARGS}).checked {REFUSED}#64) := by",
     f"  intro {CARGS} s ra hpc hargs hra hstack hap _ hreq",
     f"  obtain ⟨{', '.join(REGS)}, zf, cf, {XS}, mem, pc⟩ := s",
     "  have hargs0 := hargs",
     f"  simp only [{CNAME}, Abi.Contract.checked, List.length_cons, List.length_nil, List.take, List.cons.injEq, and_true] at hargs0",
     f"  obtain ⟨{', '.join(f'ha{i}' for i in range(len(params)))}⟩ := hargs0",
     "  simp only at hpc", f"  subst pc {' '.join(ABI[:len(params)])}",
     "  have hra' := hra", "  simp only at hra'"]
def accepted_path():
    hs = f"⟨{', '.join(f'h{j}' for j in range(n))}⟩" if n > 1 else "h0"
    return [f"exact Abi.checked_accepted (Proof_{name}.{name}_meets {CARGS}) (K := {steps([True] * n)}) (by run_fn [{', '.join(f'c{j}' for j in range(n))}]; rfl)",
            f"  (show {ACCEPTS} from {hs}) hargs hra hstack hap hreq"]


def refused_path(i):
    part = ".2" * i + (".1" if i < n - 1 else "")
    return [f"exact Abi.checked_refused (K := {steps([True] * i + [False])}) (by run_fn [{', '.join(f'c{j}' for j in range(i + 1))}]; rfl)",
            f"  (fun h => absurd (show {ACCEPTS} from h){part} h{i}) hreq"]


def tests(i, ind):
    """Test i passes or fails; the tests before it passed."""
    if i == n: return [ind + l for l in accepted_path()]
    yes = [f"have c{i} : {fact(i, True)} := by bv_decide"]
    no = [f"have c{i} : {fact(i, False)} := by bv_decide"] + refused_path(i)
    rest = tests(i + 1, ind + "  ")
    return [f"{ind}by_cases h{i} : {prop(checks[i])}", f"{ind}· {yes[0]}"] + rest + [f"{ind}· {no[0]}"] + [f"{ind}  {l}" for l in no[1:]]


L += tests(0, "  ")
L += ["", f"#print axioms {name}_checked_meets", "", f"end Checked_{name}", ""]
with open(out_path, "w") as f:
    f.write("\n".join(L))
print(f"{name}_checked: {len(rows)} instructions at 0x{ENTRY:X}, {n} tests ({ACCEPTS}); wrote {out_path}")
