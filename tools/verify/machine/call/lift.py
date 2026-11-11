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
for r in ("r8", "r14"):
    REG[r] = (r, 64); REG[r + "d"] = (r, 32); REG[r + "b"] = (r, 8)
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
    m = re.fullmatch(r"(?:(byte|dword|qword) ptr )?\[(\w+) \+ (\w+)\]", text)
    if m and m.group(3) in REG:
        (base, w0), (index, w1) = REG[m.group(2)], REG[m.group(3)]; assert w0 == w1 == 64, text
        return f"(.memi .{base} .{index})", PTR.get(m.group(1))
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
        m = re.match(r"^\s+[0-9a-f]+:\s+(?:R_X86_64_PLT32\s+(\S+)-0x4|X86_64_RELOC_BRANCH\s+(\S+))$", line)
        if m: insns[-1][4] = m.group(1) or m.group(2); continue
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
        elif op == "rol":
            r, w = reg_only(a[0]); n = int(a[1], 16); assert w == 32 and 1 < n < 32; ins = f".rol32 .{r} {n}"
        elif op.startswith("set") and op[3:] in CC:
            d, w = operand(a[0]); assert w == 8; ins = f".setcc .{CC[op[3:]]} {d}"
        elif op.startswith("cmov") and op[4:] in CC:
            r, w = reg_only(a[0]); s, ws = operand(a[1]); assert w == 32 and ws in (32, None); ins = f".cmovcc .{CC[op[4:]]} .{r} {s}"
        elif op.startswith("j") and op[1:] in CC:
            ins = f".jcc .{CC[op[1:]]} {bv(base + int(a[0].split()[0], 16))}"
        elif op in ("call", "jmp"):
            if reloc is None and op == "jmp": ins = f".jmp {bv(base + int(a[0].split()[0], 16))}"
            else:
                assert reloc in symbols, f"{op} to an unknown function: {reloc}"; ins = f".{op} {bv(symbols[reloc])}"
                d = (symbols[reloc] - nxt) & 0xFFFFFFFF
                raw = raw.split()[0] + " " + " ".join(f"{(d >> (8 * i)) & 0xFF:02x}" for i in range(4))
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
            m = re.match(r"^([0-9a-f]+) <(.+)>:$", line)
            if m: names[m.group(2)] = int(base, 16) + int(m.group(1), 16)
    text = ["import X86", "import Decode", "", "/-! The compiled functions' bytes, as the linker places them (a call's displacement filled in), and what",
            "the decoder makes of each instruction. Written by lift.py from llvm-objdump's listing; the listing is a hint:", "each line below is checked by Lean against `Decode.lean`. -/", "",
            "set_option maxRecDepth 100000", f"namespace {ns}", "open X86", ""]
    lemmas, image, count, first, at_end = [], [], 0, None, None
    for base, listing in parts:
        rows, name = lift(int(base, 16), listing, names)
        for at, nxt, ins, src in rows:
            if first is None: first = at
            assert at_end is None or at == at_end, f"a gap before 0x{at:X}"
            at_end = nxt
            raw = src[:24].split()
            assert len(raw) == nxt - at, src
            image += [int(b, 16) for b in raw]; count += 1
            lemmas.append(f"theorem at_{at:X} : prog 0x{at:X} = some ({ins}, 0x{nxt:X}) := by decide  -- {src[24:].strip()}")
    text += [f"def base : Nat := 0x{first:X}", "", "/-- The bytes, from `base` on. -/", "def image : List Nat := ["]
    text += ["  " + ", ".join(f"0x{b:02X}" for b in image[i:i + 16]) + ("," if i + 16 < len(image) else "") for i in range(0, len(image), 16)]
    text += ["]", "", "/-- The instruction at an address, and the address after it: the decoder on the bytes from there. -/",
             "def prog (pc : Nat) : Option (Instr × Nat) := if base ≤ pc then decode pc (image.drop (pc - base)) else none", ""] + lemmas + ["", f"end {ns}", ""]
    with open(out, "w") as f:
        f.write("\n".join(text))
    print(count, "instructions")

main()
