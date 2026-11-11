import Std.Tactic.BVDecide

/-! # A small x86-64 for one SSE4.1 kernel

The instructions `blake3_servil_compress_in_place_sse41` uses, each as the Intel manual gives it.
Memory here is 128-bit cells by address (a first cut: no two cells overlap, which the byte memory
of the loop experiment does not assume). -/

namespace Simd

abbrev V := BitVec 128

/-- Doubleword `i` of a vector (0 is the lowest). -/
def dw (v : V) (i : Nat) : BitVec 32 := v.extractLsb' (32 * i) 32
/-- A vector from its doublewords, lowest first. -/
def mk4 (a b c e : BitVec 32) : V := e ++ c ++ b ++ a
/-- Byte `i` of a vector. -/
def by8 (v : V) (i : Nat) : BitVec 8 := v.extractLsb' (8 * i) 8
/-- Word (16 bits) `i` of a vector. -/
def w16 (v : V) (i : Nat) : BitVec 16 := v.extractLsb' (16 * i) 16

def map2 (f : BitVec 32 → BitVec 32 → BitVec 32) (x y : V) : V :=
  mk4 (f (dw x 0) (dw y 0)) (f (dw x 1) (dw y 1)) (f (dw x 2) (dw y 2)) (f (dw x 3) (dw y 3))
def map1 (f : BitVec 32 → BitVec 32) (x : V) : V := mk4 (f (dw x 0)) (f (dw x 1)) (f (dw x 2)) (f (dw x 3))

/-- PSHUFB: byte `i` of the result is 0 where the mask byte's top bit is set, and otherwise the
byte of `x` its low four bits name. -/
def shufb1 (x m : V) (i : Nat) : BitVec 8 :=
  if (by8 m i).getLsbD 7 then 0 else (x >>> (((by8 m i) &&& 15).setWidth 128 <<< 3)).setWidth 8
def pshufb (x m : V) : V :=
  shufb1 x m 15 ++ shufb1 x m 14 ++ shufb1 x m 13 ++ shufb1 x m 12 ++ shufb1 x m 11 ++ shufb1 x m 10 ++ shufb1 x m 9 ++
    shufb1 x m 8 ++ shufb1 x m 7 ++ shufb1 x m 6 ++ shufb1 x m 5 ++ shufb1 x m 4 ++ shufb1 x m 3 ++ shufb1 x m 2 ++
    shufb1 x m 1 ++ shufb1 x m 0

/-- PSHUFD: doubleword `i` of the result is the doubleword of `y` that bits `2i+1:2i` of `imm` name. -/
def pshufd (y : V) (imm : Nat) : V :=
  mk4 (dw y (imm % 4)) (dw y (imm / 4 % 4)) (dw y (imm / 16 % 4)) (dw y (imm / 64 % 4))
/-- SHUFPS: the low two doublewords from `x`, the high two from `y`, each named by two bits of `imm`. -/
def shufps (x y : V) (imm : Nat) : V :=
  mk4 (dw x (imm % 4)) (dw x (imm / 4 % 4)) (dw y (imm / 16 % 4)) (dw y (imm / 64 % 4))
/-- PBLENDW: word `i` from `y` where bit `i` of `imm` is set, else from `x`. -/
def blend1 (x y : V) (imm i : Nat) : BitVec 16 := if imm / 2 ^ i % 2 = 1 then w16 y i else w16 x i
def pblendw (x y : V) (imm : Nat) : V :=
  blend1 x y imm 7 ++ blend1 x y imm 6 ++ blend1 x y imm 5 ++ blend1 x y imm 4 ++ blend1 x y imm 3 ++
    blend1 x y imm 2 ++ blend1 x y imm 1 ++ blend1 x y imm 0
def punpcklqdq (x y : V) : V := y.extractLsb' 0 64 ++ x.extractLsb' 0 64
def punpckldq (x y : V) : V := mk4 (dw x 0) (dw y 0) (dw x 1) (dw y 1)
def punpckhdq (x y : V) : V := mk4 (dw x 2) (dw y 2) (dw x 3) (dw y 3)

inductive Reg | rax | rcx | rdx | rsi | rdi | r8 | rsp
  deriving DecidableEq

/-- A vector operand: a register, a cell of memory, or a constant the code names (a RIP-relative
load of read-only data, which the lifter resolves). -/
inductive Src
  | x (i : Nat)
  | m (base : Reg) (disp : BitVec 64)
  | c (v : V)

inductive Instr
  | movv (dst : Nat) (src : Src)
  | storev (base : Reg) (disp : BitVec 64) (src : Nat)
  | movq (dst : Nat) (r : Reg)
  | paddd (dst : Nat) (src : Src)
  | pxor (dst : Nat) (src : Src)
  | por (dst : Nat) (src : Src)
  | pshufb (dst : Nat) (src : Src)
  | pslld (dst : Nat) (n : Nat)
  | psrld (dst : Nat) (n : Nat)
  | pshufd (dst : Nat) (src : Src) (imm : Nat)
  | shufps (dst : Nat) (src : Src) (imm : Nat)
  | pblendw (dst : Nat) (src : Src) (imm : Nat)
  | punpcklqdq (dst : Nat) (src : Src)
  | punpckldq (dst : Nat) (src : Src)
  | punpckhdq (dst : Nat) (src : Src)
  | shl64 (r : Reg) (n : Nat)
  | add64 (dst src : Reg)
  | movb (r : Reg) (v : BitVec 8)
  | decb (r : Reg)
  | je (target : Nat)
  | jmp (target : Nat)
  | ret

structure State where
  rax : BitVec 64
  rcx : BitVec 64
  rdx : BitVec 64
  rsi : BitVec 64
  rdi : BitVec 64
  r8 : BitVec 64
  rsp : BitVec 64
  zf : Option Bool
  x0 : V
  x1 : V
  x2 : V
  x3 : V
  x4 : V
  x5 : V
  x6 : V
  x7 : V
  x8 : V
  x9 : V
  x10 : V
  x11 : V
  x12 : V
  x13 : V
  x14 : V
  x15 : V
  /-- The 128-bit cells this program owns, by address. -/
  mem : BitVec 64 → Option V
  /-- The return address. -/
  ra : Nat
  pc : Nat

def State.get (s : State) : Reg → BitVec 64
  | .rax => s.rax | .rcx => s.rcx | .rdx => s.rdx | .rsi => s.rsi | .rdi => s.rdi | .r8 => s.r8 | .rsp => s.rsp

def State.set (s : State) (r : Reg) (v : BitVec 64) : State :=
  match r with
  | .rax => { s with rax := v } | .rcx => { s with rcx := v } | .rdx => { s with rdx := v } | .rsi => { s with rsi := v }
  | .rdi => { s with rdi := v } | .r8 => { s with r8 := v } | .rsp => { s with rsp := v }

def State.xmm (s : State) : Nat → V
  | 0 => s.x0 | 1 => s.x1 | 2 => s.x2 | 3 => s.x3 | 4 => s.x4 | 5 => s.x5 | 6 => s.x6 | 7 => s.x7
  | 8 => s.x8 | 9 => s.x9 | 10 => s.x10 | 11 => s.x11 | 12 => s.x12 | 13 => s.x13 | 14 => s.x14 | _ => s.x15

def State.setx (s : State) (i : Nat) (v : V) : State :=
  match i with
  | 0 => { s with x0 := v } | 1 => { s with x1 := v } | 2 => { s with x2 := v } | 3 => { s with x3 := v }
  | 4 => { s with x4 := v } | 5 => { s with x5 := v } | 6 => { s with x6 := v } | 7 => { s with x7 := v }
  | 8 => { s with x8 := v } | 9 => { s with x9 := v } | 10 => { s with x10 := v } | 11 => { s with x11 := v }
  | 12 => { s with x12 := v } | 13 => { s with x13 := v } | 14 => { s with x14 := v } | _ => { s with x15 := v }

def src (s : State) : Src → Option V
  | .x i => some (s.xmm i)
  | .m b d => s.mem (s.get b + d)
  | .c v => some v

/-- One instruction at `s.pc`, the next one at `next` unless it jumps. -/
def step (i : Instr) (next : Nat) (s : State) : Option State :=
  let s := { s with pc := next }
  match i with
  | .movv d x => do some (s.setx d (← src s x))
  | .storev b disp x => if (s.mem (s.get b + disp)).isSome
      then some { s with mem := fun a => if a = s.get b + disp then some (s.xmm x) else s.mem a } else none
  | .movq d r => some (s.setx d ((s.get r).setWidth 128))
  | .paddd d x => do some (s.setx d (map2 (· + ·) (s.xmm d) (← src s x)))
  | .pxor d x => do some (s.setx d (s.xmm d ^^^ (← src s x)))
  | .por d x => do some (s.setx d (s.xmm d ||| (← src s x)))
  | .pshufb d x => do some (s.setx d (pshufb (s.xmm d) (← src s x)))
  | .pslld d n => some (s.setx d (map1 (· <<< n) (s.xmm d)))
  | .psrld d n => some (s.setx d (map1 (· >>> n) (s.xmm d)))
  | .pshufd d x imm => do some (s.setx d (pshufd (← src s x) imm))
  | .shufps d x imm => do some (s.setx d (shufps (s.xmm d) (← src s x) imm))
  | .pblendw d x imm => do some (s.setx d (pblendw (s.xmm d) (← src s x) imm))
  | .punpcklqdq d x => do some (s.setx d (punpcklqdq (s.xmm d) (← src s x)))
  | .punpckldq d x => do some (s.setx d (punpckldq (s.xmm d) (← src s x)))
  | .punpckhdq d x => do some (s.setx d (punpckhdq (s.xmm d) (← src s x)))
  | .shl64 r n => some ({ s with zf := none }.set r (s.get r <<< n))
  | .add64 d x => some ({ s with zf := some (s.get d + s.get x == 0) }.set d (s.get d + s.get x))
  | .movb r v => some (s.set r ((s.get r &&& ~~~(0xFF : BitVec 64)) ||| v.setWidth 64))
  | .decb r =>
    let v := (s.get r).setWidth 8 - 1
    some ({ s with zf := some (v == 0) }.set r ((s.get r &&& ~~~(0xFF : BitVec 64)) ||| v.setWidth 64))
  | .je t => do some (if (← s.zf) then { s with pc := t } else s)
  | .jmp t => some { s with pc := t }
  | .ret => some { s with rsp := s.rsp + 8, pc := s.ra }

/-- Exactly `k` instructions. -/
def steps (prog : Nat → Option (Instr × Nat)) : Nat → State → Option State
  | 0, s => some s
  | k + 1, s =>
    match prog s.pc with
    | none => none
    | some (i, next) => (step i next s).bind (steps prog k)

/-- Run until the return (`pc = 0`): the state there and the instructions it took. -/
def run (prog : Nat → Option (Instr × Nat)) : Nat → Nat → State → Option (State × Nat)
  | 0, _, _ => none
  | fuel + 1, n, s =>
    if s.pc = 0 then some (s, n)
    else match prog s.pc with
      | none => none
      | some (i, next) => (step i next s).bind (run prog fuel (n + 1))

end Simd
