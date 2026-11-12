import Abi
import Std.Data.HashMap
open X86

/-! # Trying a function on an example

The machine model runs. So does the specification. Before anything is proved, and whenever a proof
fails, a function can be run on a concrete example and the result compared with what its contract says:
an example on which the contract is broken is evidence anyone can run again. This file is the part that
is the same for every function: memory to run in, the run, and what every contract asks of a return.
It is a test, not a proof: the checkers of a layout (`Sample`) are not proved against the layout. -/

namespace Try

/-- For a layout: how to put a value into memory at an address, and how to test that memory holds it. -/
structure Sample (α : Type) where
  put : Mem → BitVec 64 → α → Mem
  check : Mem → BitVec 64 → α → Bool

/-- Memory with these bytes at `a`, owned. -/
def fill (m : Mem) (a : BitVec 64) (bs : Array (BitVec 8)) : Mem :=
  fun x => if h : (x - a).toNat < bs.size then some bs[(x - a).toNat] else m x

/-- The `n` bytes at `a`, if the program owns them all. -/
def bytes? (m : Mem) (a : BitVec 64) (n : Nat) : Option (List (BitVec 8)) :=
  (List.range n).mapM fun i => m (a + BitVec.ofNat 64 i)

def le64 (v : BitVec 64) : List (BitVec 8) := (List.range 8).map fun i => (v >>> (8 * i)).setWidth 8

/-- How a run ended. -/
inductive Outcome
  | returned (s : State) (steps : Nat)
  | faulted (pc : Nat) (steps : Nat)
  | outOfFuel (pc : Nat)

/-- The bytes at the addresses given (every byte the program owns), as a table. The machine's memory is a
function, and every write wraps it once more; a long run reads through all of them unless the memory
is made a table again now and then. (The table is built once, here, not at each lookup: `Mem` is a
function type, so a definition returning one would rebuild it for every byte read.) -/
def tableOf (m : Mem) (owned : Array (BitVec 64)) : Std.HashMap (BitVec 64) (BitVec 8) :=
  owned.foldl (fun t a => match m a with | some b => t.insert a b | none => t) {}

def ofTable (table : Std.HashMap (BitVec 64) (BitVec 8)) : Mem := fun x => table[x]?

/-- Run until the program counter is the caller's return address. -/
def run (prog : Nat → Option (Instr × Nat)) (ra : Nat) (owned : Array (BitVec 64)) : Nat → Nat → State → Outcome
  | 0, _, s => .outOfFuel s.pc
  | fuel + 1, n, s =>
    if s.pc = ra then .returned s n else
    let s := if n % 128 = 127 then (let table := tableOf s.mem owned; { s with mem := ofTable table }) else s
    match prog s.pc with
    | none => .faulted s.pc n
    | some (i, next) =>
      match step i next s with
      | none => .faulted s.pc n
      | some s' => run prog ra owned fuel (n + 1) s'

def stackTop : BitVec 64 := 0x7FFFF000#64
def returnAddress : BitVec 64 := 0x0DEAD000#64

/-- The machine at a call of the function at `entry`: the arguments in their registers, the return address
on the stack, the contract's budget of stack below it owned, and marks in the registers a callee keeps. -/
def start (c : Abi.Contract) (entry : Nat) (m : Mem) : State :=
  let m := fill m (stackTop - c.stack) (Array.replicate c.stack.toNat 0#8)
  let m := fill m stackTop (le64 returnAddress).toArray
  let arg (i : Nat) : BitVec 64 := c.args.getD i 0xA5A5A5A5A5A5A5A5#64
  { rax := 0x1111#64, rcx := arg 3, rdx := arg 2, rbx := 0xB0B0#64, rsp := stackTop, rbp := 0xB1B1#64, rsi := arg 1, rdi := arg 0,
    r8 := arg 4, r9 := arg 5, r12 := 0xC2C2#64, r13 := 0xC3C3#64, r14 := 0xC4C4#64, r15 := 0xC5C5#64, zf := none, cf := none,
    x0 := 0, x1 := 0, x2 := 0, x3 := 0, x4 := 0, x5 := 0, x6 := 0, x7 := 0, x8 := 0, x9 := 0, x10 := 0, x11 := 0, x12 := 0, x13 := 0,
    x14 := 0, x15 := 0, mem := m, pc := entry }

def apartB (a n b k : BitVec 64) : Bool := decide (n ≤ b - a) && decide (k ≤ a - b)

def allApartB : List (BitVec 64 × BitVec 64) → Bool
  | [] => true
  | r :: rest => rest.all (fun q => apartB r.1 r.2 q.1 q.2) && allApartB rest

/-- Every address the function may own: its stack, the return address, and the contract's pieces. -/
def owned (c : Abi.Contract) : Array (BitVec 64) :=
  (((stackTop - c.stack, c.stack + 8#64) :: c.regions).flatMap fun r => (List.range r.2.toNat).map fun i => r.1 + BitVec.ofNat 64 i).toArray

/-- The stack and the contract's pieces of memory are apart. -/
def apart (c : Abi.Contract) : Bool := allApartB ((stackTop - c.stack, c.stack + 8#64) :: c.regions)

def sameBytes (m m' : Mem) (a : BitVec 64) (n : Nat) : Bool :=
  (List.range n).all fun i => m (a + BitVec.ofNat 64 i) == m' (a + BitVec.ofNat 64 i)

/-- What every contract asks of the state a function returns in. -/
def returnChecks (c : Abi.Contract) (s0 s' : State) : List (String × Bool) :=
  [("the stack pointer is popped", s'.rsp == s0.rsp + 8#64),
   ("the caller's registers are kept", s'.rbx == s0.rbx && s'.rbp == s0.rbp && s'.r12 == s0.r12 && s'.r13 == s0.r13 && s'.r14 == s0.r14 && s'.r15 == s0.r15),
   ("memory the function only reads is unchanged", c.reads.all fun p => sameBytes s0.mem s'.mem p.addr p.size.toNat),
   ("the bytes beside its pieces and above its stack are unchanged",
      c.regions.all (fun r => sameBytes s0.mem s'.mem (r.1 - 64#64) 64 && sameBytes s0.mem s'.mem (r.1 + r.2) 64) &&
      sameBytes s0.mem s'.mem stackTop 72)]

/-- Why a run stopped at `pc`. -/
def why (prog : Nat → Option (Instr × Nat)) (pc : Nat) : String :=
  let at_ := "0x" ++ String.mk (Nat.toDigits 16 pc)
  match prog pc with
  | none => s!"it reaches {at_}, where there is no instruction (a trap, or a jump out of the code)"
  | some _ => s!"the instruction at {at_} faults (memory the program does not own, or a misaligned vector)"

def firstFailure (cs : List (String × Bool)) : Option String := (cs.find? (fun c => !c.2)).map (·.1)

end Try
