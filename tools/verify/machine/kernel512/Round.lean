import Flat
open Simd Flat Blake3Generic

/-- One round of the specification: its eight G's. -/
def rnd (v : Vector (BitVec 32) 16) (m : Vector (BitVec 32) 16) : Vector (BitVec 32) 16 :=
  G (G (G (G (G (G (G (G v 0 4 8 12 m[0] m[1]) 1 5 9 13 m[2] m[3]) 2 6 10 14 m[4] m[5]) 3 7 11 15 m[6] m[7]) 0 5 10 15 m[8] m[9]) 1 6 11 12 m[10] m[11]) 2 7 8 13 m[12] m[13]) 3 4 9 14 m[14] m[15]


/-- The state's four rows are the sixteen words of `v`. -/
def Rows (s : State) (v : Vector (BitVec 32) 16) : Prop :=
  s.x0 = mk4 v[0] v[1] v[2] v[3] ∧ s.x1 = mk4 v[4] v[5] v[6] v[7] ∧ s.x2 = mk4 v[8] v[9] v[10] v[11] ∧ s.x3 = mk4 v[12] v[13] v[14] v[15]

/-- The message words where the round's instructions expect them. -/
def Msgs (s : State) (m : Vector (BitVec 32) 16) : Prop :=
  s.x4 = mk4 m[0] m[2] m[4] m[6] ∧ s.x5 = mk4 m[1] m[3] m[5] m[7] ∧ s.x6 = mk4 m[14] m[8] m[10] m[12] ∧ s.x7 = mk4 m[15] m[9] m[11] m[13]

/-- What a part of the kernel leaves alone. -/
def Kept (s s' : State) : Prop :=
  s'.rdi = s.rdi ∧ s'.rsp = s.rsp ∧ s'.mem = s.mem ∧ s'.ra = s.ra ∧ s'.x14 = s.x14 ∧ s'.x15 = s.x15

macro "open_ops" : tactic => `(tactic|
  simp only [map2, map1, pshufb, shufb1, pshufd, shufps, pblendw, blend1, vpblendd, blendd1, punpcklqdq, punpckldq, punpckhdq, dw, mk4, by8, w16,
    Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reducePow, ↓reduceIte, Nat.reduceEqDiff])

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- **A round.** The 34 instructions from the loop's head are the specification's round on the rows. -/
theorem body (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 : BitVec 32) (s : State) (hpc : s.pc = 0x3764)
    (hv : Rows s #v[v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15]) (hm : Msgs s #v[m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15]):
    ∃ s', steps Code.prog 34 s = some s' ∧ s'.pc = 0x381A ∧ Rows s' (rnd #v[v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15] #v[m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15]) ∧
      Msgs s' #v[m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15] ∧ Kept s s' ∧ s'.rax = s.rax := by
  obtain ⟨rax, rcx, rdx, rsi, rdi, r8, rsp, zf, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, mem, ra, pc⟩ := s
  obtain ⟨hv0, hv1, hv2, hv3⟩ := hv
  obtain ⟨hm0, hm1, hm2, hm3⟩ := hm
  simp only at hpc hv0 hv1 hv2 hv3 hm0 hm1 hm2 hm3
  subst hpc hv0 hv1 hv2 hv3 hm0 hm1 hm2 hm3
  run_kernel
  refine ⟨_, rfl, rfl, ⟨?_, ?_, ?_, ?_⟩, ⟨rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩
  all_goals (simp only [rnd]; eval_spec; open_ops; bv_decide (config := { timeout := 900 }))
