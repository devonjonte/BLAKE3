import X86
import CrossTable
open X86

/-! Test vectors for the cross-check of this folder's `X86.lean` (the model under the detection
theorem) against a CPU: each instruction of the proved program and of three other builds of it
(other-compilers/), on random states, with what the model says it leaves. `hex/cross.c` runs the same
bytes on the processor. CPUID and XGETBV are not here (what they return is the theorem's `Cpu`), nor
jumps, calls, returns, push and pop. -/

def hexs (w : Nat) (v : Nat) : String :=
  let s := String.ofList (Nat.toDigits 16 v)
  "".pushn '0' (w - s.length) ++ s

def next (x : Nat) : Nat := (x * 6364136223846793005 + 1442695040888963407) % 2 ^ 64
def r64 (seed i : Nat) : BitVec 64 := BitVec.ofNat 64 (next (next (seed * 1000003 + i)) / 2 ^ 7 + next (seed + 31 * i) * 2 ^ 37)

/-- Where the buffer is, in the model and (mapped there) on the machine: 512 bytes around `base`. -/
def base : BitVec 64 := 0x20001000
def fill (seed : Nat) (a : BitVec 64) : BitVec 8 := BitVec.ofNat 8 ((a.toNat * 2654435761 + seed * 40503) / 256)

/-- This model's memory is the bytes written: the buffer, written. -/
def buffer (seed : Nat) : List (BitVec 64 × BitVec 8) :=
  (List.range 512).map fun k => let a := base - 256 + BitVec.ofNat 64 k; (a, fill seed a)

def memBase : Opnd → List Reg
  | .mem b _ => [b]
  | _ => []

/-- The registers an instruction uses as the base of a memory operand: they get the buffer's address. -/
def bases : Instr → List Reg
  | .mov _ d x | .and _ d x | .or _ d x | .xor _ d x | .add _ d x | .sub _ d x | .test _ d x | .cmp _ d x => memBase d ++ memBase x
  | .movzx _ _ x | .cmovcc _ _ x => memBase x
  | .not _ d | .shr _ d _ | .shl _ d _ | .setcc _ d => memBase d
  | _ => []

def state (i : Instr) (seed : Nat) : State :=
  (bases i).foldl (fun s r => s.set r base)
    { rax := r64 seed 0, rcx := r64 seed 1, rdx := r64 seed 2, rbx := r64 seed 3, rsp := base, rbp := r64 seed 5,
      rsi := r64 seed 6, rdi := r64 seed 7, zf := some (seed % 2 == 1), cf := some (seed / 2 % 2 == 1),
      mem := buffer seed, pc := 1 }

def flag : Option Bool → String
  | some true => "1" | some false => "0" | none => "-"

/-- In `hex/cross.c`'s layout: ten registers (R8 and R9 are not in this model: any value, unchanged),
three vector registers (the same), ZF and CF. -/
def render (seed : Nat) (s : State) : String :=
  " ".intercalate ([s.rax, s.rcx, s.rdx, s.rbx, s.rsp, s.rbp, s.rsi, s.rdi, r64 seed 8, r64 seed 9].map (fun v => hexs 16 v.toNat) ++
    [10, 12, 14].map (fun k => hexs 32 (((r64 seed k).setWidth 128 <<< 64 ||| (r64 seed (k + 1)).setWidth 128 : BitVec 128)).toNat) ++
    [flag s.zf, flag s.cf])

def window (s : State) : String :=
  String.join ((List.range 512).map fun k => match s.mem.lookup (base - 256 + BitVec.ofNat 64 k) with
    | some v => hexs 2 v.toNat | none => "??")

def skipped : Instr → Bool
  | .jcc _ _ | .call _ | .ret | .push _ | .pop _ | .cpuid | .xgetbv => true
  | _ => false

def noCpu : Cpu := ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, 0⟩

def main (args : List String) : IO Unit := do
  let trials := (args.head? >>= String.toNat?).getD 40
  for (i, b) in crossTable do
    if skipped i then
      IO.println s!"skip {b}"
    else
      for t in List.range trials do
        let seed := b.length * 7919 + t * 104729 + (b.toList.foldl (fun n c => (n * 31 + c.toNat) % 1000003) 7)
        let s := state i seed
        match step noCpu i 2 s with
        | none => IO.println s!"fault {b}"
        | some s' => IO.println s!"test {b} {seed} {render seed s} {render seed s'} {window s'}"
