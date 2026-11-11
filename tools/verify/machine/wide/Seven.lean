import RoundsProof
open Wide Blake3Generic

/-! # The seven rounds of the sixteen-lane loop are the specification's seven rounds, lane by lane -/

theorem round1' (s : State) (hpc : s.pc = 0x4F1) (l : Nat) (hl : l < 16) :
    ∃ s', steps Rounds.prog 112 s = some s' ∧ s'.pc = 0x7B1 ∧
      #v[lane s'.z0 l, lane s'.z1 l, lane s'.z2 l, lane s'.z3 l, lane s'.z4 l, lane s'.z5 l, lane s'.z6 l, lane s'.z7 l, lane s'.z8 l, lane s'.z9 l, lane s'.z10 l, lane s'.z11 l, lane s'.z12 l, lane s'.z13 l, lane s'.z14 l, lane s'.z15 l] = rnd #v[lane s.z0 l, lane s.z1 l, lane s.z2 l, lane s.z3 l, lane s.z4 l, lane s.z5 l, lane s.z6 l, lane s.z7 l, lane s.z8 l, lane s.z9 l, lane s.z10 l, lane s.z11 l, lane s.z12 l, lane s.z13 l, lane s.z14 l, lane s.z15 l] #v[lane s.z16 l, lane s.z17 l, lane s.z18 l, lane s.z19 l, lane s.z20 l, lane s.z21 l, lane s.z22 l, lane s.z23 l, lane s.z24 l, lane s.z25 l, lane s.z26 l, lane s.z27 l, lane s.z28 l, lane s.z29 l, lane s.z30 l, lane s.z31 l] ∧
      s'.z16 = s.z16 ∧ s'.z17 = s.z17 ∧ s'.z18 = s.z18 ∧ s'.z19 = s.z19 ∧ s'.z20 = s.z20 ∧ s'.z21 = s.z21 ∧ s'.z22 = s.z22 ∧ s'.z23 = s.z23 ∧ s'.z24 = s.z24 ∧ s'.z25 = s.z25 ∧ s'.z26 = s.z26 ∧ s'.z27 = s.z27 ∧ s'.z28 = s.z28 ∧ s'.z29 = s.z29 ∧ s'.z30 = s.z30 ∧ s'.z31 = s.z31 := by
  obtain ⟨z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15, z16, z17, z18, z19, z20, z21, z22, z23, z24, z25, z26, z27, z28, z29, z30, z31, pc⟩ := s
  simp only at hpc
  subst hpc
  exact round1 z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23 z24 z25 z26 z27 z28 z29 z30 z31 l hl

theorem round2' (s : State) (hpc : s.pc = 0x7B1) (l : Nat) (hl : l < 16) :
    ∃ s', steps Rounds.prog 112 s = some s' ∧ s'.pc = 0xA71 ∧
      #v[lane s'.z0 l, lane s'.z1 l, lane s'.z2 l, lane s'.z3 l, lane s'.z4 l, lane s'.z5 l, lane s'.z6 l, lane s'.z7 l, lane s'.z8 l, lane s'.z9 l, lane s'.z10 l, lane s'.z11 l, lane s'.z12 l, lane s'.z13 l, lane s'.z14 l, lane s'.z15 l] = rnd #v[lane s.z0 l, lane s.z1 l, lane s.z2 l, lane s.z3 l, lane s.z4 l, lane s.z5 l, lane s.z6 l, lane s.z7 l, lane s.z8 l, lane s.z9 l, lane s.z10 l, lane s.z11 l, lane s.z12 l, lane s.z13 l, lane s.z14 l, lane s.z15 l] #v[lane s.z18 l, lane s.z22 l, lane s.z19 l, lane s.z26 l, lane s.z23 l, lane s.z16 l, lane s.z20 l, lane s.z29 l, lane s.z17 l, lane s.z27 l, lane s.z28 l, lane s.z21 l, lane s.z25 l, lane s.z30 l, lane s.z31 l, lane s.z24 l] ∧
      s'.z16 = s.z16 ∧ s'.z17 = s.z17 ∧ s'.z18 = s.z18 ∧ s'.z19 = s.z19 ∧ s'.z20 = s.z20 ∧ s'.z21 = s.z21 ∧ s'.z22 = s.z22 ∧ s'.z23 = s.z23 ∧ s'.z24 = s.z24 ∧ s'.z25 = s.z25 ∧ s'.z26 = s.z26 ∧ s'.z27 = s.z27 ∧ s'.z28 = s.z28 ∧ s'.z29 = s.z29 ∧ s'.z30 = s.z30 ∧ s'.z31 = s.z31 := by
  obtain ⟨z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15, z16, z17, z18, z19, z20, z21, z22, z23, z24, z25, z26, z27, z28, z29, z30, z31, pc⟩ := s
  simp only at hpc
  subst hpc
  exact round2 z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23 z24 z25 z26 z27 z28 z29 z30 z31 l hl

theorem round3' (s : State) (hpc : s.pc = 0xA71) (l : Nat) (hl : l < 16) :
    ∃ s', steps Rounds.prog 112 s = some s' ∧ s'.pc = 0xD31 ∧
      #v[lane s'.z0 l, lane s'.z1 l, lane s'.z2 l, lane s'.z3 l, lane s'.z4 l, lane s'.z5 l, lane s'.z6 l, lane s'.z7 l, lane s'.z8 l, lane s'.z9 l, lane s'.z10 l, lane s'.z11 l, lane s'.z12 l, lane s'.z13 l, lane s'.z14 l, lane s'.z15 l] = rnd #v[lane s.z0 l, lane s.z1 l, lane s.z2 l, lane s.z3 l, lane s.z4 l, lane s.z5 l, lane s.z6 l, lane s.z7 l, lane s.z8 l, lane s.z9 l, lane s.z10 l, lane s.z11 l, lane s.z12 l, lane s.z13 l, lane s.z14 l, lane s.z15 l] #v[lane s.z19 l, lane s.z20 l, lane s.z26 l, lane s.z28 l, lane s.z29 l, lane s.z18 l, lane s.z23 l, lane s.z30 l, lane s.z22 l, lane s.z21 l, lane s.z25 l, lane s.z16 l, lane s.z27 l, lane s.z31 l, lane s.z24 l, lane s.z17 l] ∧
      s'.z16 = s.z16 ∧ s'.z17 = s.z17 ∧ s'.z18 = s.z18 ∧ s'.z19 = s.z19 ∧ s'.z20 = s.z20 ∧ s'.z21 = s.z21 ∧ s'.z22 = s.z22 ∧ s'.z23 = s.z23 ∧ s'.z24 = s.z24 ∧ s'.z25 = s.z25 ∧ s'.z26 = s.z26 ∧ s'.z27 = s.z27 ∧ s'.z28 = s.z28 ∧ s'.z29 = s.z29 ∧ s'.z30 = s.z30 ∧ s'.z31 = s.z31 := by
  obtain ⟨z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15, z16, z17, z18, z19, z20, z21, z22, z23, z24, z25, z26, z27, z28, z29, z30, z31, pc⟩ := s
  simp only at hpc
  subst hpc
  exact round3 z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23 z24 z25 z26 z27 z28 z29 z30 z31 l hl

theorem round4' (s : State) (hpc : s.pc = 0xD31) (l : Nat) (hl : l < 16) :
    ∃ s', steps Rounds.prog 112 s = some s' ∧ s'.pc = 0xFF1 ∧
      #v[lane s'.z0 l, lane s'.z1 l, lane s'.z2 l, lane s'.z3 l, lane s'.z4 l, lane s'.z5 l, lane s'.z6 l, lane s'.z7 l, lane s'.z8 l, lane s'.z9 l, lane s'.z10 l, lane s'.z11 l, lane s'.z12 l, lane s'.z13 l, lane s'.z14 l, lane s'.z15 l] = rnd #v[lane s.z0 l, lane s.z1 l, lane s.z2 l, lane s.z3 l, lane s.z4 l, lane s.z5 l, lane s.z6 l, lane s.z7 l, lane s.z8 l, lane s.z9 l, lane s.z10 l, lane s.z11 l, lane s.z12 l, lane s.z13 l, lane s.z14 l, lane s.z15 l] #v[lane s.z26 l, lane s.z23 l, lane s.z28 l, lane s.z25 l, lane s.z30 l, lane s.z19 l, lane s.z29 l, lane s.z31 l, lane s.z20 l, lane s.z16 l, lane s.z27 l, lane s.z18 l, lane s.z21 l, lane s.z24 l, lane s.z17 l, lane s.z22 l] ∧
      s'.z16 = s.z16 ∧ s'.z17 = s.z17 ∧ s'.z18 = s.z18 ∧ s'.z19 = s.z19 ∧ s'.z20 = s.z20 ∧ s'.z21 = s.z21 ∧ s'.z22 = s.z22 ∧ s'.z23 = s.z23 ∧ s'.z24 = s.z24 ∧ s'.z25 = s.z25 ∧ s'.z26 = s.z26 ∧ s'.z27 = s.z27 ∧ s'.z28 = s.z28 ∧ s'.z29 = s.z29 ∧ s'.z30 = s.z30 ∧ s'.z31 = s.z31 := by
  obtain ⟨z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15, z16, z17, z18, z19, z20, z21, z22, z23, z24, z25, z26, z27, z28, z29, z30, z31, pc⟩ := s
  simp only at hpc
  subst hpc
  exact round4 z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23 z24 z25 z26 z27 z28 z29 z30 z31 l hl

theorem round5' (s : State) (hpc : s.pc = 0xFF1) (l : Nat) (hl : l < 16) :
    ∃ s', steps Rounds.prog 112 s = some s' ∧ s'.pc = 0x12B1 ∧
      #v[lane s'.z0 l, lane s'.z1 l, lane s'.z2 l, lane s'.z3 l, lane s'.z4 l, lane s'.z5 l, lane s'.z6 l, lane s'.z7 l, lane s'.z8 l, lane s'.z9 l, lane s'.z10 l, lane s'.z11 l, lane s'.z12 l, lane s'.z13 l, lane s'.z14 l, lane s'.z15 l] = rnd #v[lane s.z0 l, lane s.z1 l, lane s.z2 l, lane s.z3 l, lane s.z4 l, lane s.z5 l, lane s.z6 l, lane s.z7 l, lane s.z8 l, lane s.z9 l, lane s.z10 l, lane s.z11 l, lane s.z12 l, lane s.z13 l, lane s.z14 l, lane s.z15 l] #v[lane s.z28 l, lane s.z29 l, lane s.z25 l, lane s.z27 l, lane s.z31 l, lane s.z26 l, lane s.z30 l, lane s.z24 l, lane s.z23 l, lane s.z18 l, lane s.z21 l, lane s.z19 l, lane s.z16 l, lane s.z17 l, lane s.z22 l, lane s.z20 l] ∧
      s'.z16 = s.z16 ∧ s'.z17 = s.z17 ∧ s'.z18 = s.z18 ∧ s'.z19 = s.z19 ∧ s'.z20 = s.z20 ∧ s'.z21 = s.z21 ∧ s'.z22 = s.z22 ∧ s'.z23 = s.z23 ∧ s'.z24 = s.z24 ∧ s'.z25 = s.z25 ∧ s'.z26 = s.z26 ∧ s'.z27 = s.z27 ∧ s'.z28 = s.z28 ∧ s'.z29 = s.z29 ∧ s'.z30 = s.z30 ∧ s'.z31 = s.z31 := by
  obtain ⟨z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15, z16, z17, z18, z19, z20, z21, z22, z23, z24, z25, z26, z27, z28, z29, z30, z31, pc⟩ := s
  simp only at hpc
  subst hpc
  exact round5 z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23 z24 z25 z26 z27 z28 z29 z30 z31 l hl

theorem round6' (s : State) (hpc : s.pc = 0x12B1) (l : Nat) (hl : l < 16) :
    ∃ s', steps Rounds.prog 112 s = some s' ∧ s'.pc = 0x1571 ∧
      #v[lane s'.z0 l, lane s'.z1 l, lane s'.z2 l, lane s'.z3 l, lane s'.z4 l, lane s'.z5 l, lane s'.z6 l, lane s'.z7 l, lane s'.z8 l, lane s'.z9 l, lane s'.z10 l, lane s'.z11 l, lane s'.z12 l, lane s'.z13 l, lane s'.z14 l, lane s'.z15 l] = rnd #v[lane s.z0 l, lane s.z1 l, lane s.z2 l, lane s.z3 l, lane s.z4 l, lane s.z5 l, lane s.z6 l, lane s.z7 l, lane s.z8 l, lane s.z9 l, lane s.z10 l, lane s.z11 l, lane s.z12 l, lane s.z13 l, lane s.z14 l, lane s.z15 l] #v[lane s.z25 l, lane s.z30 l, lane s.z27 l, lane s.z21 l, lane s.z24 l, lane s.z28 l, lane s.z31 l, lane s.z17 l, lane s.z29 l, lane s.z19 l, lane s.z16 l, lane s.z26 l, lane s.z18 l, lane s.z22 l, lane s.z20 l, lane s.z23 l] ∧
      s'.z16 = s.z16 ∧ s'.z17 = s.z17 ∧ s'.z18 = s.z18 ∧ s'.z19 = s.z19 ∧ s'.z20 = s.z20 ∧ s'.z21 = s.z21 ∧ s'.z22 = s.z22 ∧ s'.z23 = s.z23 ∧ s'.z24 = s.z24 ∧ s'.z25 = s.z25 ∧ s'.z26 = s.z26 ∧ s'.z27 = s.z27 ∧ s'.z28 = s.z28 ∧ s'.z29 = s.z29 ∧ s'.z30 = s.z30 ∧ s'.z31 = s.z31 := by
  obtain ⟨z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15, z16, z17, z18, z19, z20, z21, z22, z23, z24, z25, z26, z27, z28, z29, z30, z31, pc⟩ := s
  simp only at hpc
  subst hpc
  exact round6 z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23 z24 z25 z26 z27 z28 z29 z30 z31 l hl

theorem round7' (s : State) (hpc : s.pc = 0x1571) (l : Nat) (hl : l < 16) :
    ∃ s', steps Rounds.prog 112 s = some s' ∧ s'.pc = 0x1831 ∧
      #v[lane s'.z0 l, lane s'.z1 l, lane s'.z2 l, lane s'.z3 l, lane s'.z4 l, lane s'.z5 l, lane s'.z6 l, lane s'.z7 l, lane s'.z8 l, lane s'.z9 l, lane s'.z10 l, lane s'.z11 l, lane s'.z12 l, lane s'.z13 l, lane s'.z14 l, lane s'.z15 l] = rnd #v[lane s.z0 l, lane s.z1 l, lane s.z2 l, lane s.z3 l, lane s.z4 l, lane s.z5 l, lane s.z6 l, lane s.z7 l, lane s.z8 l, lane s.z9 l, lane s.z10 l, lane s.z11 l, lane s.z12 l, lane s.z13 l, lane s.z14 l, lane s.z15 l] #v[lane s.z27 l, lane s.z31 l, lane s.z21 l, lane s.z16 l, lane s.z17 l, lane s.z25 l, lane s.z24 l, lane s.z22 l, lane s.z30 l, lane s.z26 l, lane s.z18 l, lane s.z28 l, lane s.z19 l, lane s.z20 l, lane s.z23 l, lane s.z29 l] ∧
      s'.z16 = s.z16 ∧ s'.z17 = s.z17 ∧ s'.z18 = s.z18 ∧ s'.z19 = s.z19 ∧ s'.z20 = s.z20 ∧ s'.z21 = s.z21 ∧ s'.z22 = s.z22 ∧ s'.z23 = s.z23 ∧ s'.z24 = s.z24 ∧ s'.z25 = s.z25 ∧ s'.z26 = s.z26 ∧ s'.z27 = s.z27 ∧ s'.z28 = s.z28 ∧ s'.z29 = s.z29 ∧ s'.z30 = s.z30 ∧ s'.z31 = s.z31 := by
  obtain ⟨z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15, z16, z17, z18, z19, z20, z21, z22, z23, z24, z25, z26, z27, z28, z29, z30, z31, pc⟩ := s
  simp only at hpc
  subst hpc
  exact round7 z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23 z24 z25 z26 z27 z28 z29 z30 z31 l hl

set_option maxRecDepth 1000000 in
/-- **The 784 instructions of the sixteen-lane loop's rounds are, in every lane, the
specification's seven rounds** on that lane's state words and message words, the message
permuted between rounds as the specification permutes it. -/
theorem seven_rounds (V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12 V13 V14 V15 M0 M1 M2 M3 M4 M5 M6 M7 M8 M9 M10 M11 M12 M13 M14 M15 : Z) (l : Nat) (hl : l < 16) :
    ∃ s', steps Rounds.prog 784 ⟨V0, V1, V2, V3, V4, V5, V6, V7, V8, V9, V10, V11, V12, V13, V14, V15, M0, M1, M2, M3, M4, M5, M6, M7, M8, M9, M10, M11, M12, M13, M14, M15, 0x4F1⟩ = some s' ∧ s'.pc = 0x1831 ∧
      #v[lane s'.z0 l, lane s'.z1 l, lane s'.z2 l, lane s'.z3 l, lane s'.z4 l, lane s'.z5 l, lane s'.z6 l, lane s'.z7 l, lane s'.z8 l, lane s'.z9 l, lane s'.z10 l, lane s'.z11 l, lane s'.z12 l, lane s'.z13 l, lane s'.z14 l, lane s'.z15 l] = rounds7 #v[lane V0 l, lane V1 l, lane V2 l, lane V3 l, lane V4 l, lane V5 l, lane V6 l, lane V7 l, lane V8 l, lane V9 l, lane V10 l, lane V11 l, lane V12 l, lane V13 l, lane V14 l, lane V15 l] #v[lane M0 l, lane M1 l, lane M2 l, lane M3 l, lane M4 l, lane M5 l, lane M6 l, lane M7 l, lane M8 l, lane M9 l, lane M10 l, lane M11 l, lane M12 l, lane M13 l, lane M14 l, lane M15 l] ∧
      s'.z16 = M0 ∧ s'.z17 = M1 ∧ s'.z18 = M2 ∧ s'.z19 = M3 ∧ s'.z20 = M4 ∧ s'.z21 = M5 ∧ s'.z22 = M6 ∧ s'.z23 = M7 ∧ s'.z24 = M8 ∧ s'.z25 = M9 ∧ s'.z26 = M10 ∧ s'.z27 = M11 ∧ s'.z28 = M12 ∧ s'.z29 = M13 ∧ s'.z30 = M14 ∧ s'.z31 = M15 := by
  obtain ⟨s1, e1, p1, r1, k1_0, k1_1, k1_2, k1_3, k1_4, k1_5, k1_6, k1_7, k1_8, k1_9, k1_10, k1_11, k1_12, k1_13, k1_14, k1_15⟩ := round1' ⟨V0, V1, V2, V3, V4, V5, V6, V7, V8, V9, V10, V11, V12, V13, V14, V15, M0, M1, M2, M3, M4, M5, M6, M7, M8, M9, M10, M11, M12, M13, M14, M15, 0x4F1⟩ rfl l hl
  obtain ⟨s2, e2, p2, r2, k2_0, k2_1, k2_2, k2_3, k2_4, k2_5, k2_6, k2_7, k2_8, k2_9, k2_10, k2_11, k2_12, k2_13, k2_14, k2_15⟩ := round2' s1 p1 l hl
  obtain ⟨s3, e3, p3, r3, k3_0, k3_1, k3_2, k3_3, k3_4, k3_5, k3_6, k3_7, k3_8, k3_9, k3_10, k3_11, k3_12, k3_13, k3_14, k3_15⟩ := round3' s2 p2 l hl
  obtain ⟨s4, e4, p4, r4, k4_0, k4_1, k4_2, k4_3, k4_4, k4_5, k4_6, k4_7, k4_8, k4_9, k4_10, k4_11, k4_12, k4_13, k4_14, k4_15⟩ := round4' s3 p3 l hl
  obtain ⟨s5, e5, p5, r5, k5_0, k5_1, k5_2, k5_3, k5_4, k5_5, k5_6, k5_7, k5_8, k5_9, k5_10, k5_11, k5_12, k5_13, k5_14, k5_15⟩ := round5' s4 p4 l hl
  obtain ⟨s6, e6, p6, r6, k6_0, k6_1, k6_2, k6_3, k6_4, k6_5, k6_6, k6_7, k6_8, k6_9, k6_10, k6_11, k6_12, k6_13, k6_14, k6_15⟩ := round6' s5 p5 l hl
  obtain ⟨s7, e7, p7, r7, k7_0, k7_1, k7_2, k7_3, k7_4, k7_5, k7_6, k7_7, k7_8, k7_9, k7_10, k7_11, k7_12, k7_13, k7_14, k7_15⟩ := round7' s6 p6 l hl
  simp only at r1 k1_0 k1_1 k1_2 k1_3 k1_4 k1_5 k1_6 k1_7 k1_8 k1_9 k1_10 k1_11 k1_12 k1_13 k1_14 k1_15
  simp only [k1_0, k1_1, k1_2, k1_3, k1_4, k1_5, k1_6, k1_7, k1_8, k1_9, k1_10, k1_11, k1_12, k1_13, k1_14, k1_15] at r2 k2_0 k2_1 k2_2 k2_3 k2_4 k2_5 k2_6 k2_7 k2_8 k2_9 k2_10 k2_11 k2_12 k2_13 k2_14 k2_15
  rw [r1] at r2
  simp only [k2_0, k2_1, k2_2, k2_3, k2_4, k2_5, k2_6, k2_7, k2_8, k2_9, k2_10, k2_11, k2_12, k2_13, k2_14, k2_15, k1_0, k1_1, k1_2, k1_3, k1_4, k1_5, k1_6, k1_7, k1_8, k1_9, k1_10, k1_11, k1_12, k1_13, k1_14, k1_15] at r3 k3_0 k3_1 k3_2 k3_3 k3_4 k3_5 k3_6 k3_7 k3_8 k3_9 k3_10 k3_11 k3_12 k3_13 k3_14 k3_15
  rw [r2] at r3
  simp only [k3_0, k3_1, k3_2, k3_3, k3_4, k3_5, k3_6, k3_7, k3_8, k3_9, k3_10, k3_11, k3_12, k3_13, k3_14, k3_15, k2_0, k2_1, k2_2, k2_3, k2_4, k2_5, k2_6, k2_7, k2_8, k2_9, k2_10, k2_11, k2_12, k2_13, k2_14, k2_15, k1_0, k1_1, k1_2, k1_3, k1_4, k1_5, k1_6, k1_7, k1_8, k1_9, k1_10, k1_11, k1_12, k1_13, k1_14, k1_15] at r4 k4_0 k4_1 k4_2 k4_3 k4_4 k4_5 k4_6 k4_7 k4_8 k4_9 k4_10 k4_11 k4_12 k4_13 k4_14 k4_15
  rw [r3] at r4
  simp only [k4_0, k4_1, k4_2, k4_3, k4_4, k4_5, k4_6, k4_7, k4_8, k4_9, k4_10, k4_11, k4_12, k4_13, k4_14, k4_15, k3_0, k3_1, k3_2, k3_3, k3_4, k3_5, k3_6, k3_7, k3_8, k3_9, k3_10, k3_11, k3_12, k3_13, k3_14, k3_15, k2_0, k2_1, k2_2, k2_3, k2_4, k2_5, k2_6, k2_7, k2_8, k2_9, k2_10, k2_11, k2_12, k2_13, k2_14, k2_15, k1_0, k1_1, k1_2, k1_3, k1_4, k1_5, k1_6, k1_7, k1_8, k1_9, k1_10, k1_11, k1_12, k1_13, k1_14, k1_15] at r5 k5_0 k5_1 k5_2 k5_3 k5_4 k5_5 k5_6 k5_7 k5_8 k5_9 k5_10 k5_11 k5_12 k5_13 k5_14 k5_15
  rw [r4] at r5
  simp only [k5_0, k5_1, k5_2, k5_3, k5_4, k5_5, k5_6, k5_7, k5_8, k5_9, k5_10, k5_11, k5_12, k5_13, k5_14, k5_15, k4_0, k4_1, k4_2, k4_3, k4_4, k4_5, k4_6, k4_7, k4_8, k4_9, k4_10, k4_11, k4_12, k4_13, k4_14, k4_15, k3_0, k3_1, k3_2, k3_3, k3_4, k3_5, k3_6, k3_7, k3_8, k3_9, k3_10, k3_11, k3_12, k3_13, k3_14, k3_15, k2_0, k2_1, k2_2, k2_3, k2_4, k2_5, k2_6, k2_7, k2_8, k2_9, k2_10, k2_11, k2_12, k2_13, k2_14, k2_15, k1_0, k1_1, k1_2, k1_3, k1_4, k1_5, k1_6, k1_7, k1_8, k1_9, k1_10, k1_11, k1_12, k1_13, k1_14, k1_15] at r6 k6_0 k6_1 k6_2 k6_3 k6_4 k6_5 k6_6 k6_7 k6_8 k6_9 k6_10 k6_11 k6_12 k6_13 k6_14 k6_15
  rw [r5] at r6
  simp only [k6_0, k6_1, k6_2, k6_3, k6_4, k6_5, k6_6, k6_7, k6_8, k6_9, k6_10, k6_11, k6_12, k6_13, k6_14, k6_15, k5_0, k5_1, k5_2, k5_3, k5_4, k5_5, k5_6, k5_7, k5_8, k5_9, k5_10, k5_11, k5_12, k5_13, k5_14, k5_15, k4_0, k4_1, k4_2, k4_3, k4_4, k4_5, k4_6, k4_7, k4_8, k4_9, k4_10, k4_11, k4_12, k4_13, k4_14, k4_15, k3_0, k3_1, k3_2, k3_3, k3_4, k3_5, k3_6, k3_7, k3_8, k3_9, k3_10, k3_11, k3_12, k3_13, k3_14, k3_15, k2_0, k2_1, k2_2, k2_3, k2_4, k2_5, k2_6, k2_7, k2_8, k2_9, k2_10, k2_11, k2_12, k2_13, k2_14, k2_15, k1_0, k1_1, k1_2, k1_3, k1_4, k1_5, k1_6, k1_7, k1_8, k1_9, k1_10, k1_11, k1_12, k1_13, k1_14, k1_15] at r7 k7_0 k7_1 k7_2 k7_3 k7_4 k7_5 k7_6 k7_7 k7_8 k7_9 k7_10 k7_11 k7_12 k7_13 k7_14 k7_15
  rw [r6] at r7
  refine ⟨s7, ?_, p7, ?_, k7_0, k7_1, k7_2, k7_3, k7_4, k7_5, k7_6, k7_7, k7_8, k7_9, k7_10, k7_11, k7_12, k7_13, k7_14, k7_15⟩
  · rw [show 784 = 112 + (112 + (112 + (112 + (112 + (112 + 112))))) from rfl, steps_add, e1, Option.bind_some, steps_add, e2, Option.bind_some, steps_add, e3, Option.bind_some, steps_add, e4, Option.bind_some, steps_add, e5, Option.bind_some, steps_add, e6, Option.bind_some, e7]
  · simp only [rounds7, permute_lit]
    exact r7

#print axioms seven_rounds
