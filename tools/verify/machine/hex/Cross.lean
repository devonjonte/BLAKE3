import X86
import CrossTable
open X86

/-! Test vectors for the cross-check of `X86.lean` against a CPU: each instruction of the proved
programs, on random states, with what the model says it leaves. `cross.c` runs the same bytes on
the processor, with a buffer mapped at the same address the model uses. -/

def hexs (w : Nat) (v : Nat) : String :=
  let s := String.ofList (Nat.toDigits 16 v)
  "".pushn '0' (w - s.length) ++ s

def next (x : Nat) : Nat := (x * 6364136223846793005 + 1442695040888963407) % 2 ^ 64
def r64 (seed i : Nat) : BitVec 64 := BitVec.ofNat 64 (next (next (seed * 1000003 + i)) / 2 ^ 7 + next (seed + 31 * i) * 2 ^ 37)

/-- Where the buffer is, in the model and (mapped there) on the machine: 512 bytes around `base`. -/
def base : BitVec 64 := 0x20001000
def inWindow (a : BitVec 64) : Bool := (a - (base - 256)).ult 512

/-- The buffer's byte at `a` before the instruction: a function both sides compute. -/
def fill (seed : Nat) (a : BitVec 64) : BitVec 8 := BitVec.ofNat 8 ((a.toNat * 2654435761 + seed * 40503) / 256)

/-- The registers an instruction uses in an address: the first of an operand is given the buffer's
address, a second a small number. -/
def roles : Opnd → List (Reg × Bool)
  | .mem b _ => [(b, true)]
  | .memi b i => [(b, true), (i, false)]
  | .mems b i _ _ => [(b, true), (i, false)]
  | _ => []

def operands : Instr → List Opnd
  | .mov _ d x | .xor _ d x | .and _ d x | .or _ d x | .add _ d x | .test _ d x | .cmp _ d x => [d, x]
  | .shl _ d _ | .shr _ d _ | .not _ d | .storev d _ => [d]
  | .movzx8 _ x | .loadv _ x => [x]
  | _ => []

def state0 (seed : Nat) : State :=
  { rax := r64 seed 0, rcx := r64 seed 1, rdx := r64 seed 2, rbx := r64 seed 3, rsp := base, rbp := r64 seed 5,
    rsi := r64 seed 6, rdi := r64 seed 7, r8 := r64 seed 8, r9 := r64 seed 9,
    x0 := (r64 seed 10).setWidth 128 <<< 64 ||| (r64 seed 11).setWidth 128,
    x1 := (r64 seed 12).setWidth 128 <<< 64 ||| (r64 seed 13).setWidth 128,
    x2 := (r64 seed 14).setWidth 128 <<< 64 ||| (r64 seed 15).setWidth 128,
    zf := some (seed % 2 == 1), cf := some (seed / 2 % 2 == 1),
    mem := (fun a => if inWindow a then some (fill seed a) else none), pc := 1, leak := [] }

def state (i : Instr) (seed : Nat) : State :=
  ((operands i).flatMap roles).foldl (fun s (r, isBase) => s.set r (if isBase then base else (r64 seed 20) &&& 0x1F)) (state0 seed)

def flag : Option Bool → String
  | some true => "1" | some false => "0" | none => "-"

def render (s : State) : String :=
  " ".intercalate ([s.rax, s.rcx, s.rdx, s.rbx, s.rsp, s.rbp, s.rsi, s.rdi, s.r8, s.r9].map (fun v => hexs 16 v.toNat) ++
    [s.x0, s.x1, s.x2].map (fun v => hexs 32 v.toNat) ++ [flag s.zf, flag s.cf])

def window (s : State) : String :=
  String.join ((List.range 512).map fun k => match s.mem (base - 256 + BitVec.ofNat 64 k) with
    | some v => hexs 2 v.toNat | none => "??")

/-- Left to the proofs: jumps, the return, and the stack's push and pop. -/
def skipped : Instr → Bool
  | .jcc _ _ | .jmp _ | .ret | .push _ | .pop _ => true
  | _ => false

def main (args : List String) : IO Unit := do
  let trials := (args.head? >>= String.toNat?).getD 40
  for (i, b) in crossTable do
    if skipped i then
      IO.println s!"skip {b}"
    else
      for t in List.range trials do
        let seed := b.length * 7919 + t * 104729 + (b.toList.foldl (fun n c => (n * 31 + c.toNat) % 1000003) 7)
        let s := state i seed
        match step i 2 s with
        | none => IO.println s!"fault {b}"
        | some s' => IO.println s!"test {b} {seed} {render s} {render s'} {window s'}"
