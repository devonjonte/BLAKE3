import Simd
import Code
import CodeSse
open Simd

/-! Test vectors for the cross-check of `Simd.lean` against a CPU: each instruction of the two
kernels, on random states, with what the model says it leaves. `cross.c` runs the same bytes. -/

def hex (w : Nat) (v : Nat) : String :=
  let s := String.ofList (Nat.toDigits 16 v)
  "".pushn '0' (w - s.length) ++ s

/-- A splitmix-like stream of 64-bit values. -/
def next (x : Nat) : Nat := (x * 6364136223846793005 + 1442695040888963407) % 2 ^ 64
def r64 (seed i : Nat) : BitVec 64 := BitVec.ofNat 64 (next (next (seed * 1000003 + i)) / 2 ^ 7 + next (seed + 31 * i) * 2 ^ 37)
def r128 (seed i : Nat) : V := (r64 seed (2 * i + 100)).setWidth 128 <<< 64 ||| (r64 seed (2 * i + 101)).setWidth 128

def cells : List (BitVec 64) := [0x1000, 0x1010, 0x2000, 0x2010, 0x2020, 0x2030]

def state (seed : Nat) : State :=
  { rax := r64 seed 0, rcx := r64 seed 1, rdx := r64 seed 2, rsi := 0x2000, rdi := 0x1000, r8 := r64 seed 3, rsp := 0x8000, zf := none,
    x0 := r128 seed 0, x1 := r128 seed 1, x2 := r128 seed 2, x3 := r128 seed 3, x4 := r128 seed 4, x5 := r128 seed 5,
    x6 := r128 seed 6, x7 := r128 seed 7, x8 := r128 seed 8, x9 := r128 seed 9, x10 := r128 seed 10, x11 := r128 seed 11,
    x12 := r128 seed 12, x13 := r128 seed 13, x14 := r128 seed 14, x15 := r128 seed 15,
    mem := fun a => if a = 0x1000 then some (r128 seed 20) else if a = 0x1010 then some (r128 seed 21)
      else if a = 0x2000 then some (r128 seed 22) else if a = 0x2010 then some (r128 seed 23)
      else if a = 0x2020 then some (r128 seed 24) else if a = 0x2030 then some (r128 seed 25) else none,
    ra := 0, pc := 1 }

def render (s : State) : String :=
  " ".intercalate ([s.rax, s.rcx, s.rdx, s.r8].map (fun v => hex 16 v.toNat) ++
    (List.range 16).map (fun i => hex 32 (s.xmm i).toNat) ++
    cells.map (fun a => match s.mem a with | some v => hex 32 v.toNat | none => "?"))

/-- Left to the proofs: jumps and the return, and the loads the linker fixes up. -/
def skipped : Instr → Bool
  | .je _ | .jmp _ | .ret => true
  | .movv _ (.c _) => true
  | _ => false

def emit (name : String) (table : List (Nat × Instr × Nat)) (bytes : List String) (trials : Nat) : IO Unit := do
  for ((_, i, _), b) in table.zip bytes do
    if skipped i then
      IO.println s!"skip {name} {b}"
    else
      for t in List.range trials do
        let s := state (b.length * 7919 + t * 104729 + name.length)
        match step i 2 s with
        | none => IO.println s!"fault {name} {b}"
        | some s' =>
          let zf := match s'.zf with | some true => "1" | some false => "0" | none => "-"
          let kept := if s'.rdi = 0x1000 ∧ s'.rsi = 0x2000 then "kept" else "MOVED"
          IO.println s!"test {name} {b} {render s} {render s'} {zf} {kept}"

def main : IO Unit := do
  emit "avx512" Code.table Code.bytes 40
  emit "sse41" CodeSse.table CodeSse.bytes 40
