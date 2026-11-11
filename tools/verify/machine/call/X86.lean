import Std.Tactic.BVDecide

/-! # A small x86-64, second version: memory the caller owns

As the first (tools/verify/machine/X86.lean), with memory as the bytes a program may touch:
`mem a = none` is a byte it does not own, and reading or writing one is a fault. So a theorem
that a run ends says which bytes it needed, and its final memory says which it changed. -/

namespace X86

inductive Reg | rax | rcx | rdx | rbx | rsp | rbp | rsi | rdi | r8 | r14
  deriving DecidableEq, Repr

/-- The bytes this program owns. -/
abbrev Mem := BitVec 64 → Option (BitVec 8)

/-- What an observer of time and cache may learn from one instruction: an address it reads or
writes, and where a conditional jump or a return goes. (Every instruction modelled here takes
the same time whatever its operands' values; one that does not, a division, is not modelled.) -/
inductive Obs
  | addr (a : BitVec 64)
  | pc (n : Nat)

structure State where
  rax : BitVec 64
  rcx : BitVec 64
  rdx : BitVec 64
  rbx : BitVec 64
  rsp : BitVec 64
  rbp : BitVec 64
  rsi : BitVec 64
  rdi : BitVec 64
  r8 : BitVec 64
  r14 : BitVec 64
  zf : Option Bool
  cf : Option Bool
  mem : Mem
  pc : Nat
  /-- Everything observed so far, newest first. -/
  leak : List Obs

def State.get (s : State) : Reg → BitVec 64
  | .rax => s.rax | .rcx => s.rcx | .rdx => s.rdx | .rbx => s.rbx
  | .rsp => s.rsp | .rbp => s.rbp | .rsi => s.rsi | .rdi => s.rdi | .r8 => s.r8 | .r14 => s.r14

def State.set (s : State) (r : Reg) (v : BitVec 64) : State :=
  match r with
  | .rax => { s with rax := v } | .rcx => { s with rcx := v } | .rdx => { s with rdx := v } | .rbx => { s with rbx := v }
  | .rsp => { s with rsp := v } | .rbp => { s with rbp := v } | .rsi => { s with rsi := v } | .rdi => { s with rdi := v }
  | .r8 => { s with r8 := v } | .r14 => { s with r14 := v }

def trunc (w : Nat) (v : BitVec 64) : BitVec 64 :=
  match w with
  | 8 => v &&& 0xFF
  | 32 => v &&& 0xFFFFFFFF
  | _ => v

inductive Opnd
  | reg (r : Reg)
  | mem (base : Reg) (disp : BitVec 64)
  /-- `[base + index]` -/
  | memi (base index : Reg)
  | imm (v : BitVec 64)
  deriving DecidableEq

inductive Cond | e | ne
  deriving DecidableEq

inductive Instr
  | mov (w : Nat) (dst src : Opnd)
  | xor (w : Nat) (dst src : Opnd)
  | add (w : Nat) (dst src : Opnd)
  | test (w : Nat) (a b : Opnd)
  | cmp (w : Nat) (a b : Opnd)
  | shl (w : Nat) (dst : Opnd) (n : Nat)
  | rol32 (dst : Reg) (n : Nat)
  | jcc (c : Cond) (target : Nat)
  | jmp (target : Nat)
  | call (target : Nat)
  | ret
  | push (r : Reg)
  | pop (r : Reg)
  deriving DecidableEq

def byte (v : BitVec 64) (i : Nat) : BitVec 8 := (v >>> (8 * i)).setWidth 8

def Mem.read8 (m : Mem) (a : BitVec 64) : Option (BitVec 64) := (m a).map (BitVec.setWidth 64)

/-- `w` bits at `a`, little-endian (w is 8, 32 or 64). -/
def Mem.read (m : Mem) (a : BitVec 64) : Nat → Option (BitVec 64)
  | 8 => m.read8 a
  | 32 => do
    let b0 ← m.read8 a; let b1 ← m.read8 (a + 1); let b2 ← m.read8 (a + 2); let b3 ← m.read8 (a + 3)
    pure (b0 ||| (b1 <<< 8) ||| (b2 <<< 16) ||| (b3 <<< 24))
  | _ => do
    let b0 ← m.read8 a; let b1 ← m.read8 (a + 1); let b2 ← m.read8 (a + 2); let b3 ← m.read8 (a + 3)
    let b4 ← m.read8 (a + 4); let b5 ← m.read8 (a + 5); let b6 ← m.read8 (a + 6); let b7 ← m.read8 (a + 7)
    pure (b0 ||| (b1 <<< 8) ||| (b2 <<< 16) ||| (b3 <<< 24) ||| (b4 <<< 32) ||| (b5 <<< 40) ||| (b6 <<< 48) ||| (b7 <<< 56))

/-- One byte put at `a`, whoever owns it. -/
def Mem.put8 (m : Mem) (a : BitVec 64) (v : BitVec 8) : Mem := fun x => if x = a then some v else m x

/-- One byte written at `a`: a fault unless the program owns it. -/
def Mem.write8 (m : Mem) (a : BitVec 64) (v : BitVec 8) : Option Mem :=
  if (m a).isSome then some (m.put8 a v) else none

def Mem.write (m : Mem) (a : BitVec 64) (v : BitVec 64) : Nat → Option Mem
  | 8 => m.write8 a (byte v 0)
  | 32 => do
    let m ← m.write8 a (byte v 0); let m ← m.write8 (a + 1) (byte v 1)
    let m ← m.write8 (a + 2) (byte v 2); m.write8 (a + 3) (byte v 3)
  | _ => do
    let m ← m.write8 a (byte v 0); let m ← m.write8 (a + 1) (byte v 1)
    let m ← m.write8 (a + 2) (byte v 2); let m ← m.write8 (a + 3) (byte v 3)
    let m ← m.write8 (a + 4) (byte v 4); let m ← m.write8 (a + 5) (byte v 5)
    let m ← m.write8 (a + 6) (byte v 6); m.write8 (a + 7) (byte v 7)

def addr (s : State) : Opnd → BitVec 64
  | .mem b d => s.get b + d
  | .memi b i => s.get b + s.get i
  | _ => 0

def read (s : State) (w : Nat) : Opnd → Option (BitVec 64)
  | .reg r => some (trunc w (s.get r))
  | .imm v => some (trunc w v)
  | o => s.mem.read (addr s o) w

/-- Writing 32 bits of a register clears its upper half; writing 8 keeps the other 56. -/
def write (s : State) (w : Nat) (o : Opnd) (v : BitVec 64) : Option State :=
  match o with
  | .reg r => some (s.set r (match w with
      | 8 => (s.get r &&& ~~~(0xFF : BitVec 64)) ||| (v &&& 0xFF)
      | 32 => v &&& 0xFFFFFFFF
      | _ => v))
  | .imm _ => none
  | o => do some { s with mem := (← s.mem.write (addr s o) v w) }

/-- The address an operand names, as an observation. -/
def seen (s : State) : Opnd → List Obs
  | .mem b d => [.addr (s.get b + d)]
  | .memi b i => [.addr (s.get b + s.get i)]
  | _ => []

/-- The addresses an instruction touches, from the state before it. -/
def touched (s : State) : Instr → List Obs
  | .mov _ d x | .xor _ d x | .add _ d x | .test _ d x | .cmp _ d x => seen s d ++ seen s x
  | .shl _ d _ => seen s d
  | .rol32 _ _ | .jcc _ _ | .jmp _ => []
  | .ret | .pop _ => [.addr s.rsp]
  | .push _ | .call _ => [.addr (s.rsp - 8)]

def holds (s : State) : Cond → Option Bool
  | .e => s.zf
  | .ne => s.zf.map (!·)

def logic (s : State) (w : Nat) (v : BitVec 64) : State :=
  { s with zf := some (trunc w v == 0), cf := some false }

/-- One instruction at `s.pc`, the next one at `next` unless it jumps. -/
def step (i : Instr) (next : Nat) (s : State) : Option State :=
  let s := { s with pc := next, leak := touched s i ++ s.leak }
  match i with
  | .mov w d x => do write s w d (← read s w x)
  | .xor w d x => do let v := (← read s w d) ^^^ (← read s w x); write (logic s w v) w d v
  | .test w a b => do let v := (← read s w a) &&& (← read s w b); some (logic s w v)
  | .add w d x => do
    let a ← read s w d; let b ← read s w x; let v := trunc w (a + b)
    write { s with zf := some (v == 0), cf := some (v.ult a) } w d v
  | .cmp w a b => do
    let a ← read s w a; let b ← read s w b
    some { s with zf := some (trunc w (a - b) == 0), cf := some (a.ult b) }
  | .shl w d n => do let v := trunc w ((← read s w d) <<< n); write { s with zf := some (v == 0), cf := none } w d v
  -- A rotate by a count other than 1 leaves ZF alone; CF is the bit rotated in, left unmodelled.
  | .rol32 r n => some ({ s with cf := none }.set r ((((s.get r).setWidth 32).rotateLeft n).setWidth 64))
  | .jcc c t => do some (if (← holds s c) then { s with pc := t, leak := .pc t :: s.leak } else { s with leak := .pc next :: s.leak })
  | .jmp t => some { s with pc := t }
  | .call t => do some { s with rsp := s.rsp - 8, mem := (← s.mem.write (s.rsp - 8) (BitVec.ofNat 64 next) 64), pc := t }
  | .ret => do
    let to := (← s.mem.read s.rsp 64).toNat
    some { s with rsp := s.rsp + 8, pc := to, leak := .pc to :: s.leak }
  | .push r => do some { s with rsp := s.rsp - 8, mem := (← s.mem.write (s.rsp - 8) (s.get r) 64) }
  | .pop r => do some ({ s with rsp := s.rsp + 8 }.set r (← s.mem.read s.rsp 64))

/-- Exactly `k` instructions. -/
def steps (prog : Nat → Option (Instr × Nat)) : Nat → State → Option State
  | 0, s => some s
  | k + 1, s =>
    match prog s.pc with
    | none => none
    | some (i, next) => (step i next s).bind (steps prog k)

end X86
