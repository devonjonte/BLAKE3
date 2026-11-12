#!/usr/bin/env python3
"""Write HexNeonQuiet.lean: an observer over Google's AArch64 model, and the theorem that the NEON hex
kernel's 32 instructions show the same on two machines that differ only in what memory holds and in the
vector registers. usage: gen_quiet.py OUT.lean"""
import sys
from pathlib import Path

WORDS = ("ad400420 4f00e5e4 4f00e525 4f01e4e6 4f01e607 6f0c0402 4e241c00 6f0c0423 4e241c21 4e003850 4e007851 "
         "4e013872 4e017873 6e253600 6e253621 6e253642 6e253663 4e261c00 4e261c21 4e261c42 4e261c63 4e278610 "
         "4e278631 4e278652 4e278673 4e208610 4e218631 4e228652 4e238673 ad004410 ad014c12 d65f03c0").split()
# what the model's decoder gives for each word (checked below by `decide +kernel`, one theorem a word)
INS = """.ldpSimd .Q128 0x00#5 0x01#5 (.Offset (.gpr 0x01#5) 0x0#64)
.simdImmShift true false 0x0#4 0x0#3 0x1c#5 0x0f#5 0x04#5
.simdImmShift true false 0x0#4 0x0#3 0x1c#5 0x09#5 0x05#5
.simdImmShift true false 0x0#4 0x1#3 0x1c#5 0x07#5 0x06#5
.simdImmShift true false 0x0#4 0x1#3 0x1c#5 0x10#5 0x07#5
.simdImmShift true true 0x1#4 0x4#3 0x00#5 0x00#5 0x02#5
.simdThreeSame true false 0x0#2 0x04#5 0x03#5 0x00#5 0x00#5
.simdImmShift true true 0x1#4 0x4#3 0x00#5 0x01#5 0x03#5
.simdThreeSame true false 0x0#2 0x04#5 0x03#5 0x01#5 0x01#5
.simdPermute true 0x0#2 0x00#5 0x3#3 0x02#5 0x10#5
.simdPermute true 0x0#2 0x00#5 0x7#3 0x02#5 0x11#5
.simdPermute true 0x0#2 0x01#5 0x3#3 0x03#5 0x12#5
.simdPermute true 0x0#2 0x01#5 0x7#3 0x03#5 0x13#5
.simdThreeSame true true 0x0#2 0x05#5 0x06#5 0x10#5 0x00#5
.simdThreeSame true true 0x0#2 0x05#5 0x06#5 0x11#5 0x01#5
.simdThreeSame true true 0x0#2 0x05#5 0x06#5 0x12#5 0x02#5
.simdThreeSame true true 0x0#2 0x05#5 0x06#5 0x13#5 0x03#5
.simdThreeSame true false 0x0#2 0x06#5 0x03#5 0x00#5 0x00#5
.simdThreeSame true false 0x0#2 0x06#5 0x03#5 0x01#5 0x01#5
.simdThreeSame true false 0x0#2 0x06#5 0x03#5 0x02#5 0x02#5
.simdThreeSame true false 0x0#2 0x06#5 0x03#5 0x03#5 0x03#5
.simdThreeSame true false 0x0#2 0x07#5 0x10#5 0x10#5 0x10#5
.simdThreeSame true false 0x0#2 0x07#5 0x10#5 0x11#5 0x11#5
.simdThreeSame true false 0x0#2 0x07#5 0x10#5 0x12#5 0x12#5
.simdThreeSame true false 0x0#2 0x07#5 0x10#5 0x13#5 0x13#5
.simdThreeSame true false 0x0#2 0x00#5 0x10#5 0x10#5 0x10#5
.simdThreeSame true false 0x0#2 0x01#5 0x10#5 0x11#5 0x11#5
.simdThreeSame true false 0x0#2 0x02#5 0x10#5 0x12#5 0x12#5
.simdThreeSame true false 0x0#2 0x03#5 0x10#5 0x13#5 0x13#5
.stpSimd .Q128 0x10#5 0x11#5 (.Offset (.gpr 0x00#5) 0x0#64)
.stpSimd .Q128 0x12#5 0x13#5 (.Offset (.gpr 0x00#5) 0x20#64)
.ret (.gpr 0x1e#5)""".split("\n")
assert len(WORDS) == 32 and len(INS) == 32

HEAD = r'''import Arm64
open Arm64

/-! # The NEON `hex` kernel shows nothing of the hash

Google's model has no observer of time or of the cache. This file adds one, small enough to read, and
proves: **two machines that agree on the general registers, the stack pointer, the program counter and on
which memory is mapped with which permissions, and differ in any way in what memory holds and in the
vector registers, show the same while the kernel's 32 instructions run** (`hex_neon_quiet`). The hash and
everything computed from it live in what memory holds and in the vector registers.

What is ours and must be read: `Obs`, `obsInstr`, `runObs`, `SameMap`, `Agree`, `hexWords`. The rest is
their trusted `decode` and `execInst`. What this does not say: that an instruction's own time is
independent of its operands (Arm's DIT promises that of these instructions when PSTATE.DIT is set); and
it speaks of the 32 words run in order, not yet of the model's `Step` fetching them from memory.
Written by `gen_quiet.py`. Axioms: Lean's three. -/

set_option maxRecDepth 100000

/-- What an observer of time and of the cache sees. -/
inductive Obs where
  /-- An instruction is fetched at this address. -/
  | at (pc : BitVec 64)
  /-- This many bytes are read from this address. -/
  | read (a : BitVec 64) (n : Nat)
  /-- This many bytes are written at this address. -/
  | write (a : BitVec 64) (n : Nat)
  /-- Control goes to this address. -/
  | jump (to : BitVec 64)
  deriving DecidableEq, Repr

/-- What one instruction shows before it runs, for the kinds of instruction our kernels use: its
memory accesses and where it sends control. `none`: this observer has no account of the instruction. -/
def obsInstr (i : Instr) (s : State) : Option (List Obs) :=
  match i with
  | .ldpSimd sz _ _ addr => some [.read (evalAddrMode s addr).1 (2 * sz.bytes)]
  | .stpSimd sz _ _ addr => some [.write (evalAddrMode s addr).1 (2 * sz.bytes)]
  | .simdImmShift .. => some []
  | .simdThreeSame .. => some []
  | .simdPermute .. => some []
  | .ret rn => some [.jump (s.readReg64 rn)]
  | _ => none

/-- What is seen while these instruction words run in order, each decoded and executed by the model.
A machine that has stopped (a fault) shows nothing more. -/
def runObs : List (BitVec 32) → State → Option (List Obs)
  | [], _ => some []
  | w :: ws, s =>
    match s.status with
    | .Running =>
      match decode w with
      | none => none
      | some i =>
        match obsInstr i s with
        | none => none
        | some o => (runObs ws (execInst i s)).map fun rest => Obs.at s.pc :: (o ++ rest)
    | _ => some []

/-- Two memories map the same addresses with the same permissions; what they hold is free. -/
def SameMap (m m' : Memory) : Prop := ∀ a, (m.cells a).map (·.1) = (m'.cells a).map (·.1)

/-- Two machines agree on everything the kernel's observer could depend on but what memory holds and
the vector registers. -/
structure Agree (s s' : State) : Prop where
  regs : s.regs = s'.regs
  sp : s.sp = s'.sp
  pc : s.pc = s'.pc
  status : s.status = s'.status
  map : SameMap s.mem s'.mem

/-- The kernel's 32 instruction words (`hex_neon.S`, assembled). -/
def hexWords : List (BitVec 32) := [WORDLIST]

/-! ## The proof (not to be read) -/

theorem SameMap.perm {m m' : Memory} (h : SameMap m m') (a : BitVec 64) : m.perm a = m'.perm a := by
  have := h a
  unfold Memory.perm
  cases hc : m.cells a <;> cases hc' : m'.cells a <;> simp_all
  rename_i x y; obtain ⟨p, _⟩ := x; obtain ⟨p', _⟩ := y; simp_all
  cases p' <;> rfl

theorem SameMap.lazy {m m' : Memory} (h : SameMap m m') (a : BitVec 64) : m.isLazyFree a = m'.isLazyFree a := by
  have := h a
  unfold Memory.isLazyFree
  cases hc : m.cells a <;> cases hc' : m'.cells a <;> simp_all
  rename_i x y; obtain ⟨p, _⟩ := x; obtain ⟨p', _⟩ := y; simp_all
  cases p' <;> rfl

theorem SameMap.allPerm {m m' : Memory} (h : SameMap m m') (p : Option Perm → Bool) :
    ∀ (n : Nat) (a : BitVec 64), m.allPerm p a n = m'.allPerm p a n
  | 0, _ => rfl
  | n + 1, a => by simp only [Memory.allPerm, h.perm a, SameMap.allPerm h p n]

theorem SameMap.allNoLazy {m m' : Memory} (h : SameMap m m') :
    ∀ (n : Nat) (a : BitVec 64), m.allNoLazyFree a n = m'.allNoLazyFree a n
  | 0, _ => rfl
  | n + 1, a => by simp only [Memory.allNoLazyFree, h.lazy a, SameMap.allNoLazy h n]

theorem SameMap.canRead {m m' : Memory} (h : SameMap m m') (a : BitVec 64) (n : Nat) : m.canRead a n = m'.canRead a n := by
  simp only [Memory.canRead, h.allPerm, h.allNoLazy]

theorem SameMap.canWrite {m m' : Memory} (h : SameMap m m') (a : BitVec 64) (n : Nat) : m.canWrite a n = m'.canWrite a n := by
  simp only [Memory.canWrite, h.allPerm]

theorem SameMap.write8 {m m' : Memory} (h : SameMap m m') (a : BitVec 64) (v v' : BitVec 8) :
    SameMap (m.write8 a v) (m'.write8 a v') := by
  intro b
  have hb := h b
  simp only [Memory.write8, Memory.rawPerm]
  by_cases e : b = a
  · subst e
    simp only [ite_true, Option.map_some]
    cases hc : m.cells b <;> cases hc' : m'.cells b <;> simp_all
  · simp only [e, ite_false]; exact hb

theorem SameMap.write128 {m m' : Memory} (h : SameMap m m') (a : BitVec 64) (v v' : BitVec 128) :
    SameMap (m.write128 a v) (m'.write128 a v') := by
  simp only [Memory.write128, Memory.write64]
  repeat' apply SameMap.write8
  exact h

theorem readReg_agree {s s' : State} (h : Agree s s') (r : Reg) : s.readReg64 r = s'.readReg64 r := by
  cases r <;> simp [State.readReg64, h.regs, h.sp]

/-- An instruction that changes only vector registers and goes on to the next. -/
def RegOnly (i : Instr) : Prop :=
  ∀ s, (execInst i s).regs = s.regs ∧ (execInst i s).sp = s.sp ∧ (execInst i s).pc = s.pc + 4#64 ∧
    (execInst i s).status = s.status ∧ (execInst i s).mem = s.mem

theorem cons_reg {w : BitVec 32} {i : Instr} {ws : List (BitVec 32)} {s s' : State}
    (hd : decode w = some i) (hp : RegOnly i) (ho : ∀ t, obsInstr i t = some [])
    (h : Agree s s') (k : ∀ t t', Agree t t' → runObs ws t = runObs ws t') :
    runObs (w :: ws) s = runObs (w :: ws) s' := by
  have a : Agree (execInst i s) (execInst i s') := by
    obtain ⟨r1, r2, r3, r4, r5⟩ := hp s
    obtain ⟨q1, q2, q3, q4, q5⟩ := hp s'
    exact ⟨by rw [r1, q1, h.regs], by rw [r2, q2, h.sp], by rw [r3, q3, h.pc], by rw [r4, q4, h.status],
      by rw [r5, q5]; exact h.map⟩
  simp only [runObs, hd, ho, ← h.status, ← h.pc, k _ _ a]

theorem cons_ldp {w : BitVec 32} {vt1 vt2 : BitVec 5} {off : BitVec 64} {ws : List (BitVec 32)} {s s' : State}
    (hd : decode w = some (.ldpSimd .Q128 vt1 vt2 (.Offset (.gpr 0x01#5) off)))
    (h : Agree s s') (k : ∀ t t', Agree t t' → runObs ws t = runObs ws t') :
    runObs (w :: ws) s = runObs (w :: ws) s' := by
  have e : ∀ t : State, execInst (.ldpSimd .Q128 vt1 vt2 (.Offset (.gpr 0x01#5) off)) t =
      if !(t.mem.canRead (t.readReg64 (.gpr 0x01#5) + off) 16 &&
          t.mem.canRead (t.readReg64 (.gpr 0x01#5) + off + 16#64) 16) then
        t.setStatus (.Exception "permission fault")
      else ((t.writeVReg128 vt1 (t.mem.readSimdSized .Q128 (t.readReg64 (.gpr 0x01#5) + off))).writeVReg128 vt2
        (t.mem.readSimdSized .Q128 (t.readReg64 (.gpr 0x01#5) + off + 16#64))).advancePC := fun _ => rfl
  have hr := readReg_agree h (.gpr 0x01#5)
  have a : Agree (execInst (.ldpSimd .Q128 vt1 vt2 (.Offset (.gpr 0x01#5) off)) s)
      (execInst (.ldpSimd .Q128 vt1 vt2 (.Offset (.gpr 0x01#5) off)) s') := by
    rw [e s, e s', hr, h.map.canRead, h.map.canRead]
    split
    · exact ⟨h.regs, h.sp, h.pc, rfl, h.map⟩
    · exact ⟨h.regs, h.sp, by show s.pc + 4#64 = s'.pc + 4#64; rw [h.pc], h.status, h.map⟩
  have o : ∀ t : State, obsInstr (.ldpSimd .Q128 vt1 vt2 (.Offset (.gpr 0x01#5) off)) t =
      some [.read (t.readReg64 (.gpr 0x01#5) + off) 32] := fun _ => rfl
  simp only [runObs, hd, o, hr, ← h.status, ← h.pc, k _ _ a]

theorem cons_stp {w : BitVec 32} {vt1 vt2 : BitVec 5} {off : BitVec 64} {ws : List (BitVec 32)} {s s' : State}
    (hd : decode w = some (.stpSimd .Q128 vt1 vt2 (.Offset (.gpr 0x00#5) off)))
    (h : Agree s s') (k : ∀ t t', Agree t t' → runObs ws t = runObs ws t') :
    runObs (w :: ws) s = runObs (w :: ws) s' := by
  have e : ∀ t : State, execInst (.stpSimd .Q128 vt1 vt2 (.Offset (.gpr 0x00#5) off)) t =
      if !(t.mem.canWrite (t.readReg64 (.gpr 0x00#5) + off) 16 &&
          t.mem.canWrite (t.readReg64 (.gpr 0x00#5) + off + 16#64) 16) then
        t.setStatus (.Exception "permission fault")
      else (t.setMem ((t.mem.write128 (t.readReg64 (.gpr 0x00#5) + off) (t.readVReg128 vt1)).write128
        (t.readReg64 (.gpr 0x00#5) + off + 16#64) (t.readVReg128 vt2))).advancePC := fun _ => rfl
  have hr := readReg_agree h (.gpr 0x00#5)
  have a : Agree (execInst (.stpSimd .Q128 vt1 vt2 (.Offset (.gpr 0x00#5) off)) s)
      (execInst (.stpSimd .Q128 vt1 vt2 (.Offset (.gpr 0x00#5) off)) s') := by
    rw [e s, e s', hr, h.map.canWrite, h.map.canWrite]
    split
    · exact ⟨h.regs, h.sp, h.pc, rfl, h.map⟩
    · exact ⟨h.regs, h.sp, by show s.pc + 4#64 = s'.pc + 4#64; rw [h.pc], h.status,
        (h.map.write128 _ _ _).write128 _ _ _⟩
  have o : ∀ t : State, obsInstr (.stpSimd .Q128 vt1 vt2 (.Offset (.gpr 0x00#5) off)) t =
      some [.write (t.readReg64 (.gpr 0x00#5) + off) 32] := fun _ => rfl
  simp only [runObs, hd, o, hr, ← h.status, ← h.pc, k _ _ a]

theorem seen_cons {w : BitVec 32} {i : Instr} {ws : List (BitVec 32)}
    (hd : decode w = some i) (ho : ∀ t, (obsInstr i t).isSome) (k : ∀ t, (runObs ws t).isSome) :
    ∀ s, (runObs (w :: ws) s).isSome := by
  intro s
  unfold runObs
  split
  · simp only [hd]
    have := ho s
    cases hq : obsInstr i s with
    | none => rw [hq] at this; cases this
    | some o =>
      have := k (execInst i s)
      cases hr : runObs ws (execInst i s) with
      | none => rw [hr] at this; cases this
      | some rest => rfl
  · rfl

theorem cons_ret {w : BitVec 32} {r : Reg} {s s' : State} (hd : decode w = some (.ret r)) (h : Agree s s') :
    runObs [w] s = runObs [w] s' := by
  have o : ∀ t : State, obsInstr (.ret r) t = some [.jump (t.readReg64 r)] := fun _ => rfl
  simp only [runObs, hd, o, readReg_agree h r, ← h.status, ← h.pc]

'''

out = HEAD.replace("WORDLIST", ", ".join("0x" + w for w in WORDS))
for k, (w, i) in enumerate(zip(WORDS, INS)):
    out += f"theorem d{k} : decode 0x{w}#32 = some ({i}) := by decide +kernel\n"
    if 1 <= k <= 28:
        out += f"theorem p{k} : RegOnly ({i}) := fun _ => ⟨rfl, rfl, rfl, rfl, rfl⟩\n"
out += """
/-- **While the kernel runs, two machines that agree on everything but what memory holds and the vector
registers show the same.** -/
theorem hex_neon_quiet (s s' : State) (h : Agree s s') : runObs hexWords s = runObs hexWords s' := by
  unfold hexWords
  refine cons_ldp d0 h ?_; intro s s' h
"""
for k in range(1, 29):
    out += f"  refine cons_reg d{k} p{k} (fun _ => rfl) h ?_; intro s s' h\n"
out += """  refine cons_stp d29 h ?_; intro s s' h
  refine cons_stp d30 h ?_; intro s s' h
  exact cons_ret d31 h

/-- **Every one of the 32 instructions is one the observer has an account of**: something is always
seen, so the theorem above is not about two runs both unobserved. -/
theorem hex_neon_observed : ∀ s : State, (runObs hexWords s).isSome := by
  unfold hexWords
SEENLINES  exact fun _ => rfl

#print axioms hex_neon_quiet
#print axioms hex_neon_observed
"""
out = out.replace("SEENLINES", "".join(f"  refine seen_cons d{k} (fun _ => rfl) ?_\n" for k in range(32)))
with open(sys.argv[1], "w") as f:
    f.write(out)
