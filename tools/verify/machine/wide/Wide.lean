import Std.Tactic.BVDecide

/-! # Thirty-two ZMM registers and the three instructions of a wide round

`blake3_servil_hash_many_avx512` keeps each of the sixteen state words of sixteen inputs in one
ZMM register: lane `i` of a register belongs to input `i`. A round is 112 instructions, each
VPADDD, VPXORD or VPRORD on registers. -/

namespace Wide

abbrev Z := BitVec 512

/-- Lane `i` of a register: its doubleword `i`. -/
def lane (v : Z) (i : Nat) : BitVec 32 := v.extractLsb' (32 * i) 32

/-- A register from its sixteen lanes. -/
def pack (f : Nat → BitVec 32) : Z := f 15 ++ f 14 ++ f 13 ++ f 12 ++ f 11 ++ f 10 ++ f 9 ++ f 8 ++ f 7 ++ f 6 ++ f 5 ++ f 4 ++ f 3 ++ f 2 ++ f 1 ++ f 0

def map2 (f : BitVec 32 → BitVec 32 → BitVec 32) (a b : Z) : Z := pack fun i => f (lane a i) (lane b i)
def map1 (f : BitVec 32 → BitVec 32) (a : Z) : Z := pack fun i => f (lane a i)

theorem lane_pack (f : Nat → BitVec 32) : ∀ i, i < 16 → lane (pack f) i = f i
  | 0, _ => by simp only [lane, pack, Nat.reduceMul]; bv_decide
  | 1, _ => by simp only [lane, pack, Nat.reduceMul]; bv_decide
  | 2, _ => by simp only [lane, pack, Nat.reduceMul]; bv_decide
  | 3, _ => by simp only [lane, pack, Nat.reduceMul]; bv_decide
  | 4, _ => by simp only [lane, pack, Nat.reduceMul]; bv_decide
  | 5, _ => by simp only [lane, pack, Nat.reduceMul]; bv_decide
  | 6, _ => by simp only [lane, pack, Nat.reduceMul]; bv_decide
  | 7, _ => by simp only [lane, pack, Nat.reduceMul]; bv_decide
  | 8, _ => by simp only [lane, pack, Nat.reduceMul]; bv_decide
  | 9, _ => by simp only [lane, pack, Nat.reduceMul]; bv_decide
  | 10, _ => by simp only [lane, pack, Nat.reduceMul]; bv_decide
  | 11, _ => by simp only [lane, pack, Nat.reduceMul]; bv_decide
  | 12, _ => by simp only [lane, pack, Nat.reduceMul]; bv_decide
  | 13, _ => by simp only [lane, pack, Nat.reduceMul]; bv_decide
  | 14, _ => by simp only [lane, pack, Nat.reduceMul]; bv_decide
  | 15, _ => by simp only [lane, pack, Nat.reduceMul]; bv_decide
  | n + 16, h => absurd h (by omega)

/-- A lane-wise instruction does to each lane what it does to a word. -/
theorem lane_map2 (f : BitVec 32 → BitVec 32 → BitVec 32) (a b : Z) (i : Nat) (h : i < 16) :
    lane (map2 f a b) i = f (lane a i) (lane b i) := lane_pack _ i h
theorem lane_map1 (f : BitVec 32 → BitVec 32) (a : Z) (i : Nat) (h : i < 16) :
    lane (map1 f a) i = f (lane a i) := lane_pack _ i h

inductive Instr
  | vpaddd (dst a b : Nat)
  | vpxord (dst a b : Nat)
  | vprord (dst a : Nat) (n : Nat)

structure State where
  z0 : Z
  z1 : Z
  z2 : Z
  z3 : Z
  z4 : Z
  z5 : Z
  z6 : Z
  z7 : Z
  z8 : Z
  z9 : Z
  z10 : Z
  z11 : Z
  z12 : Z
  z13 : Z
  z14 : Z
  z15 : Z
  z16 : Z
  z17 : Z
  z18 : Z
  z19 : Z
  z20 : Z
  z21 : Z
  z22 : Z
  z23 : Z
  z24 : Z
  z25 : Z
  z26 : Z
  z27 : Z
  z28 : Z
  z29 : Z
  z30 : Z
  z31 : Z
  pc : Nat

def State.z (s : State) : Nat → Z
  | 0 => s.z0 | 1 => s.z1 | 2 => s.z2 | 3 => s.z3 | 4 => s.z4 | 5 => s.z5 | 6 => s.z6 | 7 => s.z7
  | 8 => s.z8 | 9 => s.z9 | 10 => s.z10 | 11 => s.z11 | 12 => s.z12 | 13 => s.z13 | 14 => s.z14 | 15 => s.z15
  | 16 => s.z16 | 17 => s.z17 | 18 => s.z18 | 19 => s.z19 | 20 => s.z20 | 21 => s.z21 | 22 => s.z22 | 23 => s.z23
  | 24 => s.z24 | 25 => s.z25 | 26 => s.z26 | 27 => s.z27 | 28 => s.z28 | 29 => s.z29 | 30 => s.z30
  | _ => s.z31

def State.setz (s : State) (i : Nat) (v : Z) : State :=
  match i with
  | 0 => { s with z0 := v } | 1 => { s with z1 := v } | 2 => { s with z2 := v } | 3 => { s with z3 := v }
  | 4 => { s with z4 := v } | 5 => { s with z5 := v } | 6 => { s with z6 := v } | 7 => { s with z7 := v }
  | 8 => { s with z8 := v } | 9 => { s with z9 := v } | 10 => { s with z10 := v } | 11 => { s with z11 := v }
  | 12 => { s with z12 := v } | 13 => { s with z13 := v } | 14 => { s with z14 := v } | 15 => { s with z15 := v }
  | 16 => { s with z16 := v } | 17 => { s with z17 := v } | 18 => { s with z18 := v } | 19 => { s with z19 := v }
  | 20 => { s with z20 := v } | 21 => { s with z21 := v } | 22 => { s with z22 := v } | 23 => { s with z23 := v }
  | 24 => { s with z24 := v } | 25 => { s with z25 := v } | 26 => { s with z26 := v } | 27 => { s with z27 := v }
  | 28 => { s with z28 := v } | 29 => { s with z29 := v } | 30 => { s with z30 := v }
  | _ => { s with z31 := v }

def step (i : Instr) (next : Nat) (s : State) : State :=
  let s := { s with pc := next }
  match i with
  | .vpaddd d a b => s.setz d (map2 (· + ·) (s.z a) (s.z b))
  | .vpxord d a b => s.setz d (map2 (· ^^^ ·) (s.z a) (s.z b))
  | .vprord d a n => s.setz d (map1 (·.rotateRight n) (s.z a))

/-- Exactly `k` instructions. -/
def steps (prog : Nat → Option (Instr × Nat)) : Nat → State → Option State
  | 0, s => some s
  | k + 1, s =>
    match prog s.pc with
    | none => none
    | some (i, next) => steps prog k (step i next s)

theorem steps_mk (prog : Nat → Option (Instr × Nat)) (k : Nat) (z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23 z24 z25 z26 z27 z28 z29 z30 z31 : Z) (pc : Nat) :
    steps prog (k + 1) ⟨z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15, z16, z17, z18, z19, z20, z21, z22, z23, z24, z25, z26, z27, z28, z29, z30, z31, pc⟩ =
      match prog pc with
      | none => none
      | some (i, next) => steps prog k (step i next ⟨z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15, z16, z17, z18, z19, z20, z21, z22, z23, z24, z25, z26, z27, z28, z29, z30, z31, pc⟩) := rfl

theorem steps_zero (prog : Nat → Option (Instr × Nat)) (s : State) : steps prog 0 s = some s := rfl

theorem steps_add (prog : Nat → Option (Instr × Nat)) (a b : Nat) (s : State) :
    steps prog (a + b) s = (steps prog a s).bind (steps prog b) := by
  induction a generalizing s with
  | zero => simp [steps]
  | succ a ih =>
    rw [Nat.add_right_comm]
    simp only [steps]
    cases prog s.pc with
    | none => rfl
    | some x => exact ih _

end Wide
