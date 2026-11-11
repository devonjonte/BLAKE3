#!/usr/bin/env python3
"""llvm-objdump's listing of `Hash::to_hex` -> Code.lean for X86.lean.

The one RIP-relative `lea` (the address of the sixteen characters "0123456789abcdef", by its
relocation) becomes a move of `T`, the table's address, which the program takes as a parameter.
An instruction or operand form this does not know stops it.
usage: lift_hex.py LISTING OUT.lean"""
import re, sys

R64 = "rax rcx rdx rbx rsp rbp rsi rdi r8 r9".split()
REG = {}
for r in R64[:8]:
    REG[r] = (r, 64); REG["e" + r[1:]] = (r, 32)
for r in R64[8:]:
    REG[r] = (r, 64); REG[r + "d"] = (r, 32); REG[r + "b"] = (r, 8)
for r8, r in dict(al="rax", cl="rcx", dl="rdx", bl="rbx", sil="rsi", dil="rdi").items():
    REG[r8] = (r, 8)
PTR = {"byte": 8, "dword": 32, "qword": 64, "xmmword": 128}
bv = lambda n: f"0x{n & (2**64 - 1):X}"

def operand(text):
    """(lean term, width or None)"""
    text = text.strip()
    if text in REG:
        r, w = REG[text]; return f"(.reg .{r})", w
    m = re.fullmatch(r"(\w+) ptr \[(.+)\]", text)
    if m:
        w, inner = PTR[m.group(1)], m.group(2)
        g = re.fullmatch(r"(\w+)(?: ([+-]) (0x[0-9a-f]+))?", inner)
        if g:
            d = int(g.group(3), 16) * (-1 if g.group(2) == "-" else 1) if g.group(3) else 0
            return f"(.mem .{REG[g.group(1)][0]} {bv(d)})", w
        g = re.fullmatch(r"(\w+) \+ (?:(\d)\*)?(\w+)(?: ([+-]) (0x[0-9a-f]+))?", inner)
        if g:
            base, index = REG[g.group(1)][0], REG[g.group(3)][0]
            d = int(g.group(5), 16) * (-1 if g.group(4) == "-" else 1) if g.group(5) else 0
            if not g.group(2) and not g.group(5): return f"(.memi .{base} .{index})", w
            return f"(.mems .{base} .{index} {g.group(2) or 1} {bv(d)})", w
    m = re.fullmatch(r"(-?)0x([0-9a-f]+)", text)
    if m:
        v = int(m.group(2), 16); return f"(.imm {bv(-v if m.group(1) else v)})", None
    raise SystemExit(f"unknown operand: {text!r}")

def main():
    rows, lines = [], open(sys.argv[1]).read().splitlines()
    for n, line in enumerate(lines):
        m = re.match(r"^\s+([0-9a-f]+):((?: [0-9a-f]{2})+)\s+(\S+)\s*(.*)$", line)
        if not m: continue
        at, size, op, args = int(m.group(1), 16), len(m.group(2).split()), m.group(3), m.group(4).split("#")[0].strip()
        a = [x.strip() for x in args.split(",")] if args else []
        if op == "lea":
            assert a[1] == "[rip]" and "R_X86_64_PC32" in lines[n + 1] and ".Lanon." in lines[n + 1], line
            ins = f".mov 64 (.reg .{REG[a[0]][0]}) (.imm T)"
        elif op in ("mov", "and", "add", "cmp"):
            (d, wd), (s, ws) = operand(a[0]), operand(a[1]); w = wd or ws; assert w and (not wd or not ws or wd == ws), line
            ins = f".{op} {w} {d} {s}"
        elif op == "movzx":
            (r, w), (s, ws) = REG[a[0]], operand(a[1]); assert w == 32 and ws == 8, line; ins = f".movzx8 .{r} {s}"
        elif op == "shr":
            d, w = operand(a[0]); ins = f".shr {w} {d} {int(a[1], 16)}"
        elif op == "movups":
            if re.fullmatch(r"xmm\d+", a[0]):
                s, w = operand(a[1]); assert w == 128; ins = f".loadv {int(a[0][3:])} {s}"
            else:
                d, w = operand(a[0]); assert w == 128; ins = f".storev {d} {int(a[1][3:])}"
        elif op == "jne": ins = f".jcc .ne {bv(0x1000 + int(a[0].split()[0], 16))}"
        elif op in ("nop", "ret"): ins = f".{op}"
        else: raise SystemExit(f"unknown instruction: {line}")
        rows.append((0x1000 + at, 0x1000 + at + size, ins, f"{m.group(2).strip():<24} {op} {args}"))
    out = ["import X86", "import Attr", "",
           "/-! `blake3_servil_core::Hash::to_hex` as rustc 1.99.1 compiled it (the two-crate trial, release) and",
           "llvm-objdump reads it. Written by lift_hex.py; not edited by hand. `T` is the address of the table. -/", "",
           "namespace Code", "open X86", "", "def table (T : BitVec 64) : List (Nat × Instr × Nat) := ["]
    for i, (at, nxt, ins, src) in enumerate(rows):
        out.append(f"  (0x{at:X}, {ins}, 0x{nxt:X}){',' if i + 1 < len(rows) else ' '}  -- {src}")
    out += ["]", "", "def prog (T : BitVec 64) (pc : Nat) : Option (Instr × Nat) := (table T).lookup pc", ""]
    out += [f"@[code_at] theorem at_{at:X} (T : BitVec 64) : prog T 0x{at:X} = some ({ins}, 0x{nxt:X}) := rfl" for at, nxt, ins, _ in rows]
    out += ["", "end Code", ""]
    open(sys.argv[2], "w").write("\n".join(out))
    print(len(rows), "instructions")

main()
