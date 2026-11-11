import Std.Tactic.BVDecide

/-! # A small AArch64: the nine instructions of a compiled loop

The same shape as the x86-64 models: a state, the instructions, one step, and memory as the
bytes the program owns. A program is its 32-bit words, read by `decode`: anything it does not
know is a fault. (Arm ARM, C6.2: CBZ, UBFM, LDR, EOR, STR, SUBS, B.cond, ORR, RET.) -/

namespace A64

inductive Reg | x0 | x1 | x2 | x8 | x9 | x30
  deriving DecidableEq

abbrev Mem := BitVec 64 → Option (BitVec 8)

/-- What an observer of time and cache may learn: an address read or written, and where a
conditional branch or a return goes. -/
inductive Obs
  | addr (a : BitVec 64)
  | pc (n : Nat)

structure State where
  x0 : BitVec 64
  x1 : BitVec 64
  x2 : BitVec 64
  x8 : BitVec 64
  x9 : BitVec 64
  x30 : BitVec 64
  /-- The Z flag, or `none` where nothing has set it. -/
  z : Option Bool
  mem : Mem
  pc : Nat
  leak : List Obs

def State.get (s : State) : Reg → BitVec 64
  | .x0 => s.x0 | .x1 => s.x1 | .x2 => s.x2 | .x8 => s.x8 | .x9 => s.x9 | .x30 => s.x30

def State.set (s : State) (r : Reg) (v : BitVec 64) : State :=
  match r with
  | .x0 => { s with x0 := v } | .x1 => { s with x1 := v } | .x2 => { s with x2 := v }
  | .x8 => { s with x8 := v } | .x9 => { s with x9 := v } | .x30 => { s with x30 := v }

inductive Instr
  | cbz (rt : Reg) (target : Nat)
  | lsl (rd rn : Reg) (n : Nat)
  /-- LDR Wt, [Xn, #off] -/
  | ldr32 (rt rn : Reg) (off : BitVec 64)
  /-- EOR Wd, Wn, Wm, ROR #n -/
  | eor32ror (rd rn rm : Reg) (n : Nat)
  /-- STR Wt, [Xn], #step: store at Xn, then Xn += step -/
  | str32post (rt rn : Reg) (step : BitVec 64)
  | subs (rd rn : Reg) (imm : BitVec 64)
  | bne (target : Nat)
  | mov (rd rm : Reg)
  | ret
  deriving DecidableEq

def byte (v : BitVec 64) (i : Nat) : BitVec 8 := (v >>> (8 * i)).setWidth 8
def Mem.read8 (m : Mem) (a : BitVec 64) : Option (BitVec 64) := (m a).map (BitVec.setWidth 64)

/-- 32 bits at `a`, little-endian. -/
def Mem.read32 (m : Mem) (a : BitVec 64) : Option (BitVec 64) := do
  let b0 ← m.read8 a; let b1 ← m.read8 (a + 1); let b2 ← m.read8 (a + 2); let b3 ← m.read8 (a + 3)
  pure (b0 ||| (b1 <<< 8) ||| (b2 <<< 16) ||| (b3 <<< 24))

def Mem.put8 (m : Mem) (a : BitVec 64) (v : BitVec 8) : Mem := fun x => if x = a then some v else m x
def Mem.write8 (m : Mem) (a : BitVec 64) (v : BitVec 8) : Option Mem :=
  if (m a).isSome then some (m.put8 a v) else none
def Mem.write32 (m : Mem) (a : BitVec 64) (v : BitVec 64) : Option Mem := do
  let m ← m.write8 a (byte v 0); let m ← m.write8 (a + 1) (byte v 1)
  let m ← m.write8 (a + 2) (byte v 2); m.write8 (a + 3) (byte v 3)

/-- One instruction at `s.pc`; the next is four bytes on unless it branches. -/
def step (i : Instr) (s : State) : Option State :=
  let s := { s with pc := s.pc + 4 }
  match i with
  | .cbz rt t => some (if s.get rt = (0 : BitVec 64) then { s with pc := t, leak := .pc t :: s.leak } else { s with leak := .pc s.pc :: s.leak })
  | .lsl rd rn n => some (s.set rd (s.get rn <<< n))
  | .ldr32 rt rn off =>
    (s.mem.read32 (s.get rn + off)).map fun v => State.set { s with leak := .addr (s.get rn + off) :: s.leak } rt v
  | .eor32ror rd rn rm n =>
    some (s.set rd (((s.get rn).setWidth 32 ^^^ ((s.get rm).setWidth 32).rotateRight n).setWidth 64))
  | .str32post rt rn stp =>
    (s.mem.write32 (s.get rn) (s.get rt)).map fun m =>
      State.set { s with mem := m, leak := .addr (s.get rn) :: s.leak } rn (s.get rn + stp)
  | .subs rd rn imm => some (State.set { s with z := some (s.get rn - imm == 0) } rd (s.get rn - imm))
  | .bne t => s.z.map fun z => if z then { s with leak := .pc s.pc :: s.leak } else { s with pc := t, leak := .pc t :: s.leak }
  | .mov rd rm => some (s.set rd (s.get rm))
  | .ret => some { s with pc := s.x30.toNat, leak := .pc s.x30.toNat :: s.leak }

/-- A register by its number: the six this model has. -/
def regOf : Nat → Option Reg
  | 0 => some .x0 | 1 => some .x1 | 2 => some .x2 | 8 => some .x8 | 9 => some .x9 | 30 => some .x30 | _ => none

/-- A branch's 19-bit offset in instructions, as an address from `pc`. -/
def rel19 (pc imm : Nat) : Nat := if imm < 2 ^ 18 then pc + 4 * imm else pc + 4 * imm - 2 ^ 21

/-- One instruction word at `pc`. -/
def decode (pc w : Nat) : Option Instr :=
  let rd := w % 32
  let rn := w / 32 % 32
  let rm := w / 65536 % 32
  if w = 0xD65F03C0 then some .ret
  else if w / 2 ^ 24 = 0xB4 then (regOf rd).map fun r => .cbz r (rel19 pc (w / 32 % 2 ^ 19))
  else if w / 2 ^ 24 = 0x54 ∧ w % 32 = 1 then some (.bne (rel19 pc (w / 32 % 2 ^ 19)))
  else if w / 2 ^ 22 = 0x34D then
    -- UBFM Xd, Xn, #immr, #imms with imms + 1 = immr is LSL Xd, Xn, #(64 - immr)
    let immr := w / 65536 % 64
    let imms := w / 1024 % 64
    if imms + 1 = immr then (regOf rd).bind fun d => (regOf rn).map fun n => .lsl d n (64 - immr) else none
  else if w / 2 ^ 22 = 0x2E5 then (regOf rd).bind fun t => (regOf rn).map fun n => .ldr32 t n (BitVec.ofNat 64 (4 * (w / 1024 % 4096)))
  else if w / 2 ^ 21 = 0x256 then
    -- EOR Wd, Wn, Wm, ROR #imm6
    (regOf rd).bind fun d => (regOf rn).bind fun n => (regOf rm).map fun m => .eor32ror d n m (w / 1024 % 64)
  else if w / 2 ^ 21 = 0x5C0 ∧ w / 1024 % 4 = 1 ∧ w / 2 ^ 20 % 2 = 0 then
    (regOf rd).bind fun t => (regOf rn).map fun n => .str32post t n (BitVec.ofNat 64 (w / 4096 % 256))
  else if w / 2 ^ 22 = 0x3C4 then (regOf rd).bind fun d => (regOf rn).map fun n => .subs d n (BitVec.ofNat 64 (w / 1024 % 4096))
  else if w / 2 ^ 21 = 0x550 ∧ rn = 31 ∧ w / 1024 % 64 = 0 then (regOf rd).bind fun d => (regOf rm).map fun m => .mov d m
  else none

/-- The instruction at `pc` in the program whose words are `image`, from address `base`. -/
def at_ (base : Nat) (image : List Nat) (pc : Nat) : Option Instr :=
  if base ≤ pc ∧ pc % 4 = 0 then (image[(pc - base) / 4]?).bind (decode pc) else none

/-- Exactly `k` instructions. -/
def steps (prog : Nat → Option Instr) : Nat → State → Option State
  | 0, s => some s
  | k + 1, s =>
    match prog s.pc with
    | none => none
    | some i => (step i s).bind (steps prog k)

end A64
