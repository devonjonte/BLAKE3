"""llvm-objdump's listing of some functions -> a Lean program for X86.lean.

Each function is placed at its own base address; a call goes to the function its relocation names.
An instruction or operand form this does not know stops it: nothing is skipped.
usage: lift.py OUT.lean NAME BASE:LISTING [BASE:LISTING ...]"""
import re, sys

R64 = "rax rcx rdx rbx rsp rbp rsi rdi".split()
REG = {}
for i, r in enumerate(R64):
    REG[r] = (r, 64); REG["e" + r[1:]] = (r, 32)
for r8, r in dict(al="rax", cl="rcx", dl="rdx", bl="rbx", sil="rsi", dil="rdi", spl="rsp", bpl="rbp").items():
    REG[r8] = (r, 8)
PTR = {"byte": 8, "dword": 32, "qword": 64}
CC = {"e": "e", "ne": "ne", "ae": "ae"}

def bv(n):
    return f"0x{n & (2**64 - 1):X}"

def operand(text):
    """(lean term, width or None)"""
    text = text.strip()
    if text in REG:
        r, w = REG[text]; return f"(.reg .{r})", w
    m = re.fullmatch(r"(?:(byte|dword|qword) ptr )?\[(\w+)(?: ([+-]) (0x[0-9a-f]+))?\]", text)
    if m:
        base, w0 = REG[m.group(2)]; assert w0 == 64, text
        d = int(m.group(4), 16) if m.group(4) else 0
        if m.group(3) == "-": d = -d
        return f"(.mem .{base} {bv(d)})", PTR.get(m.group(1))
    m = re.fullmatch(r"(-?)0x([0-9a-f]+)", text)
    if m:
        v = int(m.group(2), 16); return f"(.imm {bv(-v if m.group(1) else v)})", None
    raise SystemExit(f"unknown operand: {text!r}")

def reg_only(text):
    r, w = REG[text.strip()]; return r, w

def lift(base, listing, symbols):
    """[(address, next, lean instruction, source text)], and the function's name"""
    rows, name, lines = [], None, open(listing).read().splitlines()
    insns = []
    for line in lines:
        m = re.match(r"^[0-9a-f]+ <(.+)>:$", line)
        if m: name = m.group(1); continue
        m = re.match(r"^\s+([0-9a-f]+):((?: [0-9a-f]{2})+)\s+(\S+)\s*(.*)$", line)
        if m:
            insns.append([int(m.group(1), 16), len(m.group(2).split()), m.group(3), m.group(4).strip(), None, m.group(2).strip()]); continue
        m = re.match(r"^\s+[0-9a-f]+:\s+R_X86_64_PLT32\s+(\S+)-0x4$", line)
        if m: insns[-1][4] = m.group(1); continue
    for at, size, op, args, reloc, raw in insns:
        a = [x.strip() for x in args.split(",")] if args else []
        nxt = base + at + size
        if op in ("mov", "and", "or", "xor", "add", "sub", "test", "cmp"):
            (d, wd), (s, ws) = operand(a[0]), operand(a[1]); w = wd or ws; assert w and (not wd or not ws or wd == ws), args
            ins = f".{op} {w} {d} {s}"
        elif op == "movzx":
            r, w = reg_only(a[0]); s, ws = operand(a[1]); assert w == 32 and ws == 8, args; ins = f".movzx {ws} .{r} {s}"
        elif op == "lea":
            r, w = reg_only(a[0]); m = re.fullmatch(r"\[(\w+) \+ (0x[0-9a-f]+)\]", a[1]); assert w == 64 and m, args
            ins = f".lea .{r} .{REG[m.group(1)][0]} {bv(int(m.group(2), 16))}"
        elif op == "xchg":
            (x, wx), (y, wy) = reg_only(a[0]), reg_only(a[1]); assert wx == wy == 64, args; ins = f".xchg .{x} .{y}"
        elif op == "not":
            d, w = operand(a[0]); assert w; ins = f".not {w} {d}"
        elif op in ("shr", "shl"):
            d, w = operand(a[0]); n = int(a[1], 16); assert w and 0 < n < w; ins = f".{op} {w} {d} {n}"
        elif op.startswith("set") and op[3:] in CC:
            d, w = operand(a[0]); assert w == 8; ins = f".setcc .{CC[op[3:]]} {d}"
        elif op.startswith("cmov") and op[4:] in CC:
            r, w = reg_only(a[0]); s, ws = operand(a[1]); assert w == 32 and ws in (32, None); ins = f".cmovcc .{CC[op[4:]]} .{r} {s}"
        elif op.startswith("j") and op[1:] in CC:
            ins = f".jcc .{CC[op[1:]]} {bv(base + int(a[0].split()[0], 16))}"
        elif op == "call":
            assert reloc in symbols, f"call to an unknown function: {reloc}"; ins = f".call {bv(symbols[reloc])}"
        elif op in ("ret", "cpuid", "xgetbv"):
            assert not a; ins = f".{op}"
        elif op in ("push", "pop"):
            r, w = reg_only(a[0]); assert w == 64; ins = f".{op} .{r}"
        else:
            raise SystemExit(f"unknown instruction: {op} {args}")
        rows.append((base + at, nxt, ins, f"{raw:<24} {op} {args}"))
    return rows, name

def main():
    out, ns, parts = sys.argv[1], sys.argv[2], [p.split(":", 1) for p in sys.argv[3:]]
    names = {}
    for base, listing in parts:
        for line in open(listing):
            m = re.match(r"^[0-9a-f]+ <(.+)>:$", line)
            if m: names[m.group(1)] = int(base, 16)
    text = ["import X86", "", "/-! The compiled functions, as llvm-objdump reads them. Written by lift.py; not edited by hand. -/", "", f"namespace {ns}", "open X86", "",
            "def table : List (Nat × Instr × Nat) := ["]
    lemmas, count = [], 0
    for base, listing in parts:
        rows, name = lift(int(base, 16), listing, names)
        text.append(f"  -- {name}")
        for at, nxt, ins, src in rows:
            text.append(f"  (0x{at:X}, {ins}, 0x{nxt:X}),  -- {src}"); count += 1
            lemmas.append(f"@[simp] theorem at_{at:X} : prog 0x{at:X} = some ({ins}, 0x{nxt:X}) := rfl")
    text[-1] = text[-1].replace("),  -- ", ")   -- ", 1)
    text += ["]", "", "/-- The instruction at an address, and the address after it. -/", "def prog (pc : Nat) : Option (Instr × Nat) := table.lookup pc", ""] + lemmas + ["", f"end {ns}", ""]
    with open(out, "w") as f:
        f.write("\n".join(text))
    print(count, "instructions")

main()
