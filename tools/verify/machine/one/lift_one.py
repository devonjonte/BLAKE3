"""llvm-objdump's listing of one function -> a table of instructions for Machine.lean.

usage: lift_one.py LISTING FUNCTION BASE OUT.lean NAMESPACE [--object OBJ] [--call SYMBOL=ADDRESS ...]

The function is placed at BASE. A RIP-relative vector load is resolved to the 16 bytes its
relocation names in OBJ's data; a call through the GOT or the PLT goes to the address given
for its symbol. An instruction or operand form this does not know stops it: nothing is
skipped but NOPs after the function's last instruction."""
import os, re, subprocess, sys

listing, func, base, out, ns = sys.argv[1:6]
base = int(base, 16)
obj, calls = None, {}
panics_from = None   # the function's panic blocks start here: they are left out, so a jump to one is a fault
rest = sys.argv[6:]
while rest:
    if rest[0] == "--object": obj = rest[1]; rest = rest[2:]
    elif rest[0] == "--call": k, v = rest[1].split("=", 1); calls[k] = int(v, 16); rest = rest[2:]
    elif rest[0] == "--panics-from": panics_from = int(rest[1], 16); rest = rest[2:]
    else: raise SystemExit(f"unknown argument {rest[0]}")
OD = os.environ.get("OBJDUMP", "llvm-objdump")
symbols, data = {}, {}
if obj:
    for line in subprocess.run([OD, "-t", obj], capture_output=True, text=True, check=True).stdout.splitlines():
        f = line.split()
        if len(f) >= 5 and re.fullmatch(r"[0-9a-f]{16}", f[0]): symbols[f[-1]] = int(f[0], 16)
    for line in subprocess.run([OD, "-s", obj], capture_output=True, text=True, check=True).stdout.splitlines():
        m = re.match(r"^\s*([0-9a-f]+) ((?:[0-9a-f]+ )+)", line)
        if m:
            at = int(m.group(1), 16)
            for i, b in enumerate(bytes.fromhex(m.group(2).replace(" ", ""))): data[at + i] = b

G64 = "rax rcx rdx rbx rsp rbp rsi rdi r8 r9 r12 r13 r14 r15".split()
REG = {r: (r, 64) for r in G64}
for r in "rax rcx rdx rbx rsp rbp rsi rdi".split(): REG["e" + r[1:]] = (r, 32)
for r8, r in dict(al="rax", cl="rcx", dl="rdx", bl="rbx", sil="rsi", dil="rdi").items(): REG[r8] = (r, 8)
for r in "r8 r9 r12 r13 r14 r15".split(): REG[r + "d"] = (r, 32); REG[r + "b"] = (r, 8)
PTR = {"byte": 8, "dword": 32, "qword": 64}

def bv(n): return f"0x{n & (2**64 - 1):X}"
def xmm(t):
    m = re.fullmatch(r"xmm(\d+)", t.strip()); assert m, t; return int(m.group(1))
def is_xmm(t): return re.fullmatch(r"xmm\d+", t.strip()) is not None
def memref(t):
    """(base register, displacement) of `[reg]`, `[reg + d]`, `[reg - d]`"""
    m = re.fullmatch(r"\[(\w+)(?: ([+-]) (0x[0-9a-f]+))?\]", t.strip()); assert m, t
    r, w = REG[m.group(1)]; assert w == 64, t
    d = int(m.group(3), 16) if m.group(3) else 0
    return r, (-d if m.group(2) == "-" else d)
def const(sym):
    at = symbols[sym]; return "0x" + "".join(f"{data[at + i]:02X}" for i in reversed(range(16)))
def vsrc(t, reloc):
    t = t.strip()
    if is_xmm(t): return f"(.x {xmm(t)})", False
    assert t.startswith("xmmword ptr "), t
    if t == "xmmword ptr [rip]":
        assert reloc, "a RIP-relative load without a relocation"; return f"(.c {const(reloc)}#128)", False
    r, d = memref(t[len("xmmword ptr "):]); return f"(.m .{r} {bv(d)})", True
def opnd(t):
    """(lean operand, width or None)"""
    t = t.strip()
    if t in REG: r, w = REG[t]; return f"(.reg .{r})", w
    m = re.fullmatch(r"(byte|dword|qword) ptr (\[.*\])", t)
    if m: r, d = memref(m.group(2)); return f"(.mem .{r} {bv(d)})", PTR[m.group(1)]
    m = re.fullmatch(r"(-?)0x([0-9a-f]+)", t)
    if m: v = int(m.group(2), 16); return f"(.imm {bv(-v if m.group(1) else v)})", None
    raise SystemExit(f"unknown operand: {t!r}")

inside, insns = False, []
for line in open(listing):
    m = re.match(r"^[0-9a-f]+ <(.+)>:$", line.rstrip())
    if m: inside = m.group(1) == func; continue
    if not inside: continue
    m = re.match(r"^\s+([0-9a-f]+):((?: [0-9a-f]{2})+)\s+(\S+)\s*([^#]*)", line)
    if m: insns.append([int(m.group(1), 16), len(m.group(2).split()), m.group(3), m.group(4).strip(), None, m.group(2).strip()]); continue
    m = re.match(r"^\s+[0-9a-f]+:\s+(?:X86_64_RELOC_SIGNED\s+(\S+)|R_X86_64_(?:GOTPCREL|PLT32)\s+(.+)-0x4)$", line.rstrip())
    if m and insns: insns[-1][4] = m.group(1) or m.group(2)
assert insns, f"{func} is not in {listing}"
start = insns[0][0]
ALIGNED = ("movaps", "movdqa", "vmovaps", "vmovdqa")
UNALIGNED = ("movups", "movdqu", "vmovups", "vmovdqu")
rows, ended = [], False
for at, size, op, args, reloc, raw in insns:
    a = [x.strip() for x in args.split(",")] if args else []
    if panics_from is not None and at - start >= panics_from:
        continue
    if ended:
        assert op.startswith("nop") or op in ("int3", "ud2"), f"code after the return: {op}"; continue
    at2, nxt = base + at - start, base + at - start + size
    mi = re.fullmatch(r"xmmword ptr \[(\w+) \+ (\w+)(?: \+ (0x[0-9a-f]+))?\]", a[1]) if len(a) > 1 else None
    if op in ALIGNED + UNALIGNED and mi and mi.group(2) in REG and is_xmm(a[0]):
        ins = f".movvi {'true' if op in ALIGNED else 'false'} {xmm(a[0])} .{REG[mi.group(1)][0]} .{REG[mi.group(2)][0]} {bv(int(mi.group(3), 16) if mi.group(3) else 0)}"
    elif op in ALIGNED + UNALIGNED:
        if is_xmm(a[0]):
            s, mem = vsrc(a[1], reloc); ins = f".movv {'true' if (op in ALIGNED and mem) else 'false'} {xmm(a[0])} {s}"
        else:
            assert a[0].startswith("xmmword ptr "), args
            r, d = memref(a[0][len("xmmword ptr "):]); ins = f".storev {'true' if op in ALIGNED else 'false'} .{r} {bv(d)} {xmm(a[1])}"
    elif op in ("movq", "vmovq"): r, w = REG[a[1]]; assert w == 64; ins = f".movq {xmm(a[0])} .{r}"
    elif op in ("paddd", "pxor", "por", "pshufb", "punpcklqdq", "punpckldq", "punpckhdq"): ins = f".{op} {xmm(a[0])} {vsrc(a[1], reloc)[0]}"
    elif op in ("pslld", "psrld"): ins = f".{op} {xmm(a[0])} {int(a[1], 16)}"
    elif op in ("pshufd", "shufps", "pblendw"): ins = f".{op} {xmm(a[0])} {vsrc(a[1], reloc)[0]} {int(a[2], 16)}"
    elif op == "vpshufd": ins = f".pshufd {xmm(a[0])} {vsrc(a[1], reloc)[0]} {int(a[2], 16)}"
    elif op in ("vpaddd", "vpxord", "vpxor", "vpunpcklqdq", "vpunpckldq", "vpunpckhdq"):
        ins = f".{op.replace('vpxord', 'vpxor')} {xmm(a[0])} {xmm(a[1])} {vsrc(a[2], reloc)[0]}"
    elif op == "vprord": ins = f".vprord {xmm(a[0])} {vsrc(a[1], reloc)[0]} {int(a[2], 16)}"
    elif op in ("vshufps", "vpblendd"): ins = f".{op} {xmm(a[0])} {xmm(a[1])} {vsrc(a[2], reloc)[0]} {int(a[3], 16)}"
    elif op in ("mov", "or", "add", "sub", "cmp", "and", "xor"):
        (d, wd), (s, ws) = opnd(a[0]), opnd(a[1]); w = wd or ws; assert w and (not wd or not ws or wd == ws), args
        ins = f".{op} {w} {d} {s}"
    elif op == "movzx":
        r, w = REG[a[0]]; s, ws = opnd(a[1]); assert w == 32 and ws == 8, args; ins = f".movzx8 .{r} {s}"
    elif op == "shl": r, w = REG[a[0]]; assert w == 64; ins = f".shl64 .{r} {int(a[1], 16)}"
    elif op == "dec":
        r, w = REG[a[0]]; assert w in (8, 64); ins = f".decb .{r}" if w == 8 else f".dec64 .{r}"
    elif op == "lea":
        r, w = REG[a[0]]; assert w == 64; b, d = memref(a[1]); ins = f".lea .{r} .{b} {bv(d)}"
    elif op.startswith("nop"): ins = ".nop"
    elif op in ("push", "pop"): r, w = REG[a[0]]; assert w == 64; ins = f".{op} .{r}"
    elif op in ("je", "jne", "jmp", "jbe", "jae"): ins = f".{op} 0x{base + int(a[0].split()[0], 16) - start:X}"
    elif op == "call":
        assert reloc in calls, f"call to a function with no address given: {reloc}"; ins = f".call 0x{calls[reloc]:X}"
    elif op == "ret": ins = ".ret"; ended = True
    else: raise SystemExit(f"unknown instruction: {op} {args}")
    rows.append((at2, nxt, ins, f"{raw:<26} {op} {args}"))
text = ["import Machine", "", f"/-! `{func[:90]}`, as llvm-objdump reads it, placed at 0x{base:X}. Written by lift_one.py. -/", "",
        "set_option maxRecDepth 100000", f"namespace {ns}", "open X86", "", f"def entry : Nat := 0x{base:X}", "", "def table : List (Nat × Instr × Nat) := ["]
text += [f"  (0x{at:X}, {ins}, 0x{nxt:X}){',' if i + 1 < len(rows) else ''}  -- {s}" for i, (at, nxt, ins, s) in enumerate(rows)]
text += ["]", "", f"end {ns}", ""]
open(out, "w").write("\n".join(text))
open(out + ".rows", "w").write("\n".join(f"{at:X}\t{nxt:X}\t{ins}" for at, nxt, ins, _ in rows) + "\n")
print(len(rows), "instructions")
