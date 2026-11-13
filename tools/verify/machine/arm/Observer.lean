import Arm64
open Arm64

/-! # An observer of time and of the cache, over Google's AArch64 model

Their model has no account of side channels. This file adds a small one, for straight-line kernels:
what is seen while instruction words run (`runObs`), and what it means for two machines to differ only
in what an observer must not learn (`Agree`): what memory holds, and the vector registers.

To be read: `Obs`, `obsInstr`, `runObs`, `SameMap`, `Agree`. The lemmas after them are for the compiler's
proofs (`Quiet_NAME.lean`). What this does not say: that an instruction's own time is independent of its
operands (Arm's DIT promises that of these instructions when PSTATE.DIT is set); and `runObs` runs
words in order, it does not yet follow the model's `Step` fetching them from memory. -/

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
  | .simdTbl .. => some []
  | .simdInsDup .. => some []
  | .moveWide .. => some []
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

/-- Two machines agree on everything a kernel's observer could depend on but what memory holds and
the vector registers. -/
structure Agree (s s' : State) : Prop where
  regs : s.regs = s'.regs
  sp : s.sp = s'.sp
  pc : s.pc = s'.pc
  status : s.status = s'.status
  map : SameMap s.mem s'.mem

/-! ## Lemmas for the compiler's proofs (not to be read) -/

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

/-- An instruction that works on the general registers alone (what it leaves in them depends on nothing
else) and goes on to the next. -/
def GprOnly (i : Instr) : Prop :=
  ∀ s s', s.regs = s'.regs →
    (execInst i s).regs = (execInst i s').regs ∧ (execInst i s).sp = s.sp ∧ (execInst i s).pc = s.pc + 4#64 ∧
    (execInst i s).status = s.status ∧ (execInst i s).mem = s.mem

theorem cons_gpr {w : BitVec 32} {i : Instr} {ws : List (BitVec 32)} {s s' : State}
    (hd : decode w = some i) (hp : GprOnly i) (ho : ∀ t, obsInstr i t = some [])
    (h : Agree s s') (k : ∀ t t', Agree t t' → runObs ws t = runObs ws t') :
    runObs (w :: ws) s = runObs (w :: ws) s' := by
  have a : Agree (execInst i s) (execInst i s') := by
    obtain ⟨r1, r2, r3, r4, r5⟩ := hp s s' h.regs
    obtain ⟨_, q2, q3, q4, q5⟩ := hp s' s' rfl
    exact ⟨r1, by rw [r2, q2, h.sp], by rw [r3, q3, h.pc], by rw [r4, q4, h.status],
      by rw [r5, q5]; exact h.map⟩
  simp only [runObs, hd, ho, ← h.status, ← h.pc, k _ _ a]

/-- A constant moved into one of X0 to X30 (`movz`, `movk`, `movn`) is such an instruction. -/
theorem moveWide_gprOnly (w : RegWidth) (op : MoveWideOp) (idx : BitVec 5) (imm : BitVec 16) (hw : Nat)
    (hi : (idx == 31#5) = false) : GprOnly (.moveWide w op (.gpr idx) imm hw) := by
  intro s s' h
  have e : ∀ t : State, execInst (.moveWide w op (.gpr idx) imm hw) t = execMoveWide w op (.gpr idx) imm hw t :=
    fun _ => rfl
  rw [e s, e s']
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> cases op <;> cases w <;>
    simp [execMoveWide, State.writeReg, State.writeReg64, State.readReg, State.readReg32,
      State.readReg64, State.advancePC, hi, h]

/-- A load of two vectors at a general register plus a constant. -/
theorem cons_ldp {w : BitVec 32} {vt1 vt2 r : BitVec 5} {off : BitVec 64} {ws : List (BitVec 32)} {s s' : State}
    (hd : decode w = some (.ldpSimd .Q128 vt1 vt2 (.Offset (.gpr r) off)))
    (h : Agree s s') (k : ∀ t t', Agree t t' → runObs ws t = runObs ws t') :
    runObs (w :: ws) s = runObs (w :: ws) s' := by
  have e : ∀ t : State, execInst (.ldpSimd .Q128 vt1 vt2 (.Offset (.gpr r) off)) t =
      if !(t.mem.canRead (t.readReg64 (.gpr r) + off) 16 &&
          t.mem.canRead (t.readReg64 (.gpr r) + off + 16#64) 16) then
        t.setStatus (.Exception "permission fault")
      else ((t.writeVReg128 vt1 (t.mem.readSimdSized .Q128 (t.readReg64 (.gpr r) + off))).writeVReg128 vt2
        (t.mem.readSimdSized .Q128 (t.readReg64 (.gpr r) + off + 16#64))).advancePC := fun _ => rfl
  have hr := readReg_agree h (.gpr r)
  have a : Agree (execInst (.ldpSimd .Q128 vt1 vt2 (.Offset (.gpr r) off)) s)
      (execInst (.ldpSimd .Q128 vt1 vt2 (.Offset (.gpr r) off)) s') := by
    rw [e s, e s', hr, h.map.canRead, h.map.canRead]
    split
    · exact ⟨h.regs, h.sp, h.pc, rfl, h.map⟩
    · exact ⟨h.regs, h.sp, by show s.pc + 4#64 = s'.pc + 4#64; rw [h.pc], h.status, h.map⟩
  have o : ∀ t : State, obsInstr (.ldpSimd .Q128 vt1 vt2 (.Offset (.gpr r) off)) t =
      some [.read (t.readReg64 (.gpr r) + off) 32] := fun _ => rfl
  simp only [runObs, hd, o, hr, ← h.status, ← h.pc, k _ _ a]

/-- A store of two vectors at a general register plus a constant. -/
theorem cons_stp {w : BitVec 32} {vt1 vt2 r : BitVec 5} {off : BitVec 64} {ws : List (BitVec 32)} {s s' : State}
    (hd : decode w = some (.stpSimd .Q128 vt1 vt2 (.Offset (.gpr r) off)))
    (h : Agree s s') (k : ∀ t t', Agree t t' → runObs ws t = runObs ws t') :
    runObs (w :: ws) s = runObs (w :: ws) s' := by
  have e : ∀ t : State, execInst (.stpSimd .Q128 vt1 vt2 (.Offset (.gpr r) off)) t =
      if !(t.mem.canWrite (t.readReg64 (.gpr r) + off) 16 &&
          t.mem.canWrite (t.readReg64 (.gpr r) + off + 16#64) 16) then
        t.setStatus (.Exception "permission fault")
      else (t.setMem ((t.mem.write128 (t.readReg64 (.gpr r) + off) (t.readVReg128 vt1)).write128
        (t.readReg64 (.gpr r) + off + 16#64) (t.readVReg128 vt2))).advancePC := fun _ => rfl
  have hr := readReg_agree h (.gpr r)
  have a : Agree (execInst (.stpSimd .Q128 vt1 vt2 (.Offset (.gpr r) off)) s)
      (execInst (.stpSimd .Q128 vt1 vt2 (.Offset (.gpr r) off)) s') := by
    rw [e s, e s', hr, h.map.canWrite, h.map.canWrite]
    split
    · exact ⟨h.regs, h.sp, h.pc, rfl, h.map⟩
    · exact ⟨h.regs, h.sp, by show s.pc + 4#64 = s'.pc + 4#64; rw [h.pc], h.status,
        (h.map.write128 _ _ _).write128 _ _ _⟩
  have o : ∀ t : State, obsInstr (.stpSimd .Q128 vt1 vt2 (.Offset (.gpr r) off)) t =
      some [.write (t.readReg64 (.gpr r) + off) 32] := fun _ => rfl
  simp only [runObs, hd, o, hr, ← h.status, ← h.pc, k _ _ a]

/-- The return, last. -/
theorem cons_ret {w : BitVec 32} {r : Reg} {s s' : State} (hd : decode w = some (.ret r)) (h : Agree s s') :
    runObs [w] s = runObs [w] s' := by
  have o : ∀ t : State, obsInstr (.ret r) t = some [.jump (t.readReg64 r)] := fun _ => rfl
  simp only [runObs, hd, o, readReg_agree h r, ← h.status, ← h.pc]

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
