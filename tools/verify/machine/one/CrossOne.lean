import Machine
import CrossOneTable
open X86

/-! Test vectors for the cross-check of `Machine.lean` against a CPU: each instruction of the programs
proved on it (both one-block kernels, the parent functions, `merge`), on random states, with what the
model says it leaves. `cross_one.c` runs the same bytes on the processor, with a buffer mapped at the
address the model uses. -/

def hexs (w : Nat) (v : Nat) : String :=
  let s := String.ofList (Nat.toDigits 16 v)
  "".pushn '0' (w - s.length) ++ s

def next (x : Nat) : Nat := (x * 6364136223846793005 + 1442695040888963407) % 2 ^ 64
def r64 (seed i : Nat) : BitVec 64 := BitVec.ofNat 64 (next (next (seed * 1000003 + i)) / 2 ^ 7 + next (seed + 31 * i) * 2 ^ 37)
def r128 (seed i : Nat) : V := (r64 seed (2 * i + 100)).setWidth 128 <<< 64 ||| (r64 seed (2 * i + 101)).setWidth 128

/-- Where the buffer is, in the model and (mapped there) on the machine: 1024 bytes around `base`. -/
def base : BitVec 64 := 0x20001000
def inWindow (a : BitVec 64) : Bool := (a - (base - 512)).ult 1024
def fill (seed : Nat) (a : BitVec 64) : BitVec 8 := BitVec.ofNat 8 ((a.toNat * 2654435761 + seed * 40503) / 256)

/-- The registers an instruction uses in an address: a base gets the buffer's address, moved by up to
fifteen bytes so that the address the instruction forms is a multiple of sixteen (an aligned move
needs that); an index gets a small multiple of sixteen. -/
def roles : Instr → List (Reg × Option (BitVec 64))
  | .movv _ _ (.m b d) | .paddd _ (.m b d) | .pxor _ (.m b d) | .por _ (.m b d) | .pshufb _ (.m b d) => [(b, some d)]
  | .storev _ b d _ => [(b, some d)]
  | .movvi _ _ b i d => [(b, some d), (i, none)]
  | .mov _ d x | .or _ d x | .add _ d x | .sub _ d x | .cmp _ d x | .and _ d x | .xor _ d x =>
    (match d with | .mem b e => [(b, some e)] | _ => []) ++ (match x with | .mem b e => [(b, some e)] | _ => [])
  | .movzx8 _ (.mem b d) => [(b, some d)]
  | _ => []

def state0 (seed : Nat) : State :=
  { rax := r64 seed 0, rcx := r64 seed 1, rdx := r64 seed 2, rbx := r64 seed 3, rsp := base, rbp := r64 seed 5,
    rsi := r64 seed 6, rdi := r64 seed 7, r8 := r64 seed 8, r9 := r64 seed 9, r12 := r64 seed 10, r13 := r64 seed 11,
    r14 := r64 seed 12, r15 := r64 seed 13,
    zf := some (seed % 2 == 1), cf := some (seed / 2 % 2 == 1),
    x0 := r128 seed 0, x1 := r128 seed 1, x2 := r128 seed 2, x3 := r128 seed 3, x4 := r128 seed 4, x5 := r128 seed 5,
    x6 := r128 seed 6, x7 := r128 seed 7, x8 := r128 seed 8, x9 := r128 seed 9, x10 := r128 seed 10, x11 := r128 seed 11,
    x12 := r128 seed 12, x13 := r128 seed 13, x14 := r128 seed 14, x15 := r128 seed 15,
    mem := (fun a => if inWindow a then some (fill seed a) else none), pc := 1 }

def state (i : Instr) (seed : Nat) : State :=
  (roles i).foldl (fun s (r, d) => s.set r (match d with
    | some d => base + ((0 - d) &&& 15)
    | none => ((r64 seed 20) &&& 0x7) <<< 4)) (state0 seed)

def flag : Option Bool → String
  | some true => "1" | some false => "0" | none => "-"

def render (s : State) : String :=
  " ".intercalate ([s.rax, s.rcx, s.rdx, s.rbx, s.rsp, s.rbp, s.rsi, s.rdi, s.r8, s.r9, s.r12, s.r13, s.r14, s.r15].map (fun v => hexs 16 v.toNat) ++
    (List.range 16).map (fun i => hexs 32 (s.xmm i).toNat) ++ [flag s.zf, flag s.cf])

def window (s : State) : String :=
  String.join ((List.range 1024).map fun k => match s.mem (base - 512 + BitVec.ofNat 64 k) with
    | some v => hexs 2 v.toNat | none => "??")

/-- Left to the proofs: jumps, calls, the return, the stack's push and pop, and the loads of constants
the linker places. -/
def skipped : Instr → Bool
  | .je _ | .jne _ | .jbe _ | .jae _ | .jmp _ | .call _ | .ret | .push _ | .pop _ => true
  | .movv _ _ (.c _) | .paddd _ (.c _) | .pxor _ (.c _) | .por _ (.c _) | .pshufb _ (.c _) => true
  | .vpaddd _ _ (.c _) | .vpxor _ _ (.c _) | .vpblendd _ _ (.c _) _ | .vshufps _ _ (.c _) _ => true
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
