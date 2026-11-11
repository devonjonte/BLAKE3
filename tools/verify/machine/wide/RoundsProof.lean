import Wide
import Rounds
import Generic
open Wide Blake3Generic

instance : Rotr (BitVec 32) := ⟨fun x n => x.rotateRight n⟩

/-- One round of the specification: its eight G's. -/
def rnd (v : Vector (BitVec 32) 16) (m : Vector (BitVec 32) 16) : Vector (BitVec 32) 16 :=
  G (G (G (G (G (G (G (G v 0 4 8 12 m[0] m[1]) 1 5 9 13 m[2] m[3]) 2 6 10 14 m[4] m[5]) 3 7 11 15 m[6] m[7]) 0 5 10 15 m[8] m[9]) 1 6 11 12 m[10] m[11]) 2 7 8 13 m[12] m[13]) 3 4 9 14 m[14] m[15]

/-- The seven rounds, the message permuted between them. -/
def rounds7 (v m : Vector (BitVec 32) 16) : Vector (BitVec 32) 16 :=
  rnd (rnd (rnd (rnd (rnd (rnd (rnd v m) (PERMUTE m)) (PERMUTE (PERMUTE m))) (PERMUTE (PERMUTE (PERMUTE m))))
    (PERMUTE (PERMUTE (PERMUTE (PERMUTE m))))) (PERMUTE (PERMUTE (PERMUTE (PERMUTE (PERMUTE m))))))
    (PERMUTE (PERMUTE (PERMUTE (PERMUTE (PERMUTE (PERMUTE m))))))

theorem fv0 : (((0 : Fin 16) : Nat)) = 0 := rfl
theorem fv1 : (((1 : Fin 16) : Nat)) = 1 := rfl
theorem fv2 : (((2 : Fin 16) : Nat)) = 2 := rfl
theorem fv3 : (((3 : Fin 16) : Nat)) = 3 := rfl
theorem fv4 : (((4 : Fin 16) : Nat)) = 4 := rfl
theorem fv5 : (((5 : Fin 16) : Nat)) = 5 := rfl
theorem fv6 : (((6 : Fin 16) : Nat)) = 6 := rfl
theorem fv7 : (((7 : Fin 16) : Nat)) = 7 := rfl
theorem fv8 : (((8 : Fin 16) : Nat)) = 8 := rfl
theorem fv9 : (((9 : Fin 16) : Nat)) = 9 := rfl
theorem fv10 : (((10 : Fin 16) : Nat)) = 10 := rfl
theorem fv11 : (((11 : Fin 16) : Nat)) = 11 := rfl
theorem fv12 : (((12 : Fin 16) : Nat)) = 12 := rfl
theorem fv13 : (((13 : Fin 16) : Nat)) = 13 := rfl
theorem fv14 : (((14 : Fin 16) : Nat)) = 14 := rfl
theorem fv15 : (((15 : Fin 16) : Nat)) = 15 := rfl
theorem ofFn16 (f : Fin 16 → BitVec 32) : Vector.ofFn f = #v[f 0, f 1, f 2, f 3, f 4, f 5, f 6, f 7, f 8, f 9, f 10, f 11, f 12, f 13, f 14, f 15] := rfl

/-- The message permutation, on sixteen words written out. -/
theorem permute_lit (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : BitVec 32) :
    PERMUTE #v[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15] =
      #v[a2, a6, a3, a10, a7, a0, a4, a13, a1, a11, a12, a5, a9, a14, a15, a8] := by
  simp only [PERMUTE, PERMUTATION, ofFn16, fv0, fv1, fv2, fv3, fv4, fv5, fv6, fv7, fv8, fv9, fv10, fv11, fv12, fv13, fv14, fv15, Fin.isValue, Fin.getElem_fin,
    Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- Round 1: 112 instructions; message word `i` is in ZMM16+`[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15][i]`. -/
theorem round1 (V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12 V13 V14 V15 M0 M1 M2 M3 M4 M5 M6 M7 M8 M9 M10 M11 M12 M13 M14 M15 : Z) (l : Nat) (hl : l < 16) :
    ∃ s', steps Rounds.prog 112 ⟨V0, V1, V2, V3, V4, V5, V6, V7, V8, V9, V10, V11, V12, V13, V14, V15, M0, M1, M2, M3, M4, M5, M6, M7, M8, M9, M10, M11, M12, M13, M14, M15, 0x4F1⟩ = some s' ∧ s'.pc = 0x7B1 ∧
      #v[lane s'.z0 l, lane s'.z1 l, lane s'.z2 l, lane s'.z3 l, lane s'.z4 l, lane s'.z5 l, lane s'.z6 l, lane s'.z7 l, lane s'.z8 l, lane s'.z9 l, lane s'.z10 l, lane s'.z11 l, lane s'.z12 l, lane s'.z13 l, lane s'.z14 l, lane s'.z15 l] =
        rnd #v[lane V0 l, lane V1 l, lane V2 l, lane V3 l, lane V4 l, lane V5 l, lane V6 l, lane V7 l, lane V8 l, lane V9 l, lane V10 l, lane V11 l, lane V12 l, lane V13 l, lane V14 l, lane V15 l]
          #v[lane M0 l, lane M1 l, lane M2 l, lane M3 l, lane M4 l, lane M5 l, lane M6 l, lane M7 l, lane M8 l, lane M9 l, lane M10 l, lane M11 l, lane M12 l, lane M13 l, lane M14 l, lane M15 l] ∧
      s'.z16 = M0 ∧ s'.z17 = M1 ∧ s'.z18 = M2 ∧ s'.z19 = M3 ∧ s'.z20 = M4 ∧ s'.z21 = M5 ∧ s'.z22 = M6 ∧ s'.z23 = M7 ∧ s'.z24 = M8 ∧ s'.z25 = M9 ∧ s'.z26 = M10 ∧ s'.z27 = M11 ∧ s'.z28 = M12 ∧ s'.z29 = M13 ∧ s'.z30 = M14 ∧ s'.z31 = M15 := by
  simp (config := {maxSteps := 100000000, implicitDefEqProofs := false}) only [steps_mk, steps_zero, step, State.z, State.setz,
    Rounds.at_4F1, Rounds.at_4F7, Rounds.at_4FD, Rounds.at_503, Rounds.at_509, Rounds.at_50F, Rounds.at_515, Rounds.at_51B, Rounds.at_521, Rounds.at_527, Rounds.at_52D, Rounds.at_533, Rounds.at_539, Rounds.at_540, Rounds.at_547, Rounds.at_54E, Rounds.at_555, Rounds.at_55B, Rounds.at_561, Rounds.at_567, Rounds.at_56D, Rounds.at_573, Rounds.at_579, Rounds.at_57F, Rounds.at_585, Rounds.at_58C, Rounds.at_593, Rounds.at_59A, Rounds.at_5A1, Rounds.at_5A7, Rounds.at_5AD, Rounds.at_5B3, Rounds.at_5B9, Rounds.at_5BF, Rounds.at_5C5, Rounds.at_5CB, Rounds.at_5D1, Rounds.at_5D7, Rounds.at_5DD, Rounds.at_5E3, Rounds.at_5E9, Rounds.at_5F0, Rounds.at_5F7, Rounds.at_5FE, Rounds.at_605, Rounds.at_60B, Rounds.at_611, Rounds.at_617, Rounds.at_61D, Rounds.at_623, Rounds.at_629, Rounds.at_62F, Rounds.at_635, Rounds.at_63C, Rounds.at_643, Rounds.at_64A, Rounds.at_651, Rounds.at_657, Rounds.at_65D, Rounds.at_663, Rounds.at_669, Rounds.at_66F, Rounds.at_675, Rounds.at_67B, Rounds.at_681, Rounds.at_687, Rounds.at_68D, Rounds.at_693, Rounds.at_699, Rounds.at_6A0, Rounds.at_6A7, Rounds.at_6AE, Rounds.at_6B5, Rounds.at_6BB, Rounds.at_6C1, Rounds.at_6C7, Rounds.at_6CD, Rounds.at_6D3, Rounds.at_6D9, Rounds.at_6DF, Rounds.at_6E5, Rounds.at_6EC, Rounds.at_6F3, Rounds.at_6FA, Rounds.at_701, Rounds.at_707, Rounds.at_70D, Rounds.at_713, Rounds.at_719, Rounds.at_71F, Rounds.at_725, Rounds.at_72B, Rounds.at_731, Rounds.at_737, Rounds.at_73D, Rounds.at_743, Rounds.at_749, Rounds.at_750, Rounds.at_757, Rounds.at_75E, Rounds.at_765, Rounds.at_76B, Rounds.at_771, Rounds.at_777, Rounds.at_77D, Rounds.at_783, Rounds.at_789, Rounds.at_78F, Rounds.at_795, Rounds.at_79C, Rounds.at_7A3, Rounds.at_7AA]
  refine ⟨_, rfl, rfl, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  simp only [lane_map2 _ _ _ l hl, lane_map1 _ _ l hl]
  simp (config := {maxSteps := 100000000, implicitDefEqProofs := false}) only [rnd, G, Id.run, pure, Rotr.rotr,
    fv0, fv1, fv2, fv3, fv4, fv5, fv6, fv7, fv8, fv9, fv10, fv11, fv12, fv13, fv14, fv15,
    Vector.set_mk, List.set_toArray, List.set_cons_succ, List.set_cons_zero, Fin.isValue, Fin.getElem_fin,
    Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero,
    Vector.mk.injEq, Array.mk.injEq, List.cons.injEq, and_true]
  bv_decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- Round 2: 112 instructions; message word `i` is in ZMM16+`[2, 6, 3, 10, 7, 0, 4, 13, 1, 11, 12, 5, 9, 14, 15, 8][i]`. -/
theorem round2 (V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12 V13 V14 V15 M0 M1 M2 M3 M4 M5 M6 M7 M8 M9 M10 M11 M12 M13 M14 M15 : Z) (l : Nat) (hl : l < 16) :
    ∃ s', steps Rounds.prog 112 ⟨V0, V1, V2, V3, V4, V5, V6, V7, V8, V9, V10, V11, V12, V13, V14, V15, M0, M1, M2, M3, M4, M5, M6, M7, M8, M9, M10, M11, M12, M13, M14, M15, 0x7B1⟩ = some s' ∧ s'.pc = 0xA71 ∧
      #v[lane s'.z0 l, lane s'.z1 l, lane s'.z2 l, lane s'.z3 l, lane s'.z4 l, lane s'.z5 l, lane s'.z6 l, lane s'.z7 l, lane s'.z8 l, lane s'.z9 l, lane s'.z10 l, lane s'.z11 l, lane s'.z12 l, lane s'.z13 l, lane s'.z14 l, lane s'.z15 l] =
        rnd #v[lane V0 l, lane V1 l, lane V2 l, lane V3 l, lane V4 l, lane V5 l, lane V6 l, lane V7 l, lane V8 l, lane V9 l, lane V10 l, lane V11 l, lane V12 l, lane V13 l, lane V14 l, lane V15 l]
          #v[lane M2 l, lane M6 l, lane M3 l, lane M10 l, lane M7 l, lane M0 l, lane M4 l, lane M13 l, lane M1 l, lane M11 l, lane M12 l, lane M5 l, lane M9 l, lane M14 l, lane M15 l, lane M8 l] ∧
      s'.z16 = M0 ∧ s'.z17 = M1 ∧ s'.z18 = M2 ∧ s'.z19 = M3 ∧ s'.z20 = M4 ∧ s'.z21 = M5 ∧ s'.z22 = M6 ∧ s'.z23 = M7 ∧ s'.z24 = M8 ∧ s'.z25 = M9 ∧ s'.z26 = M10 ∧ s'.z27 = M11 ∧ s'.z28 = M12 ∧ s'.z29 = M13 ∧ s'.z30 = M14 ∧ s'.z31 = M15 := by
  simp (config := {maxSteps := 100000000, implicitDefEqProofs := false}) only [steps_mk, steps_zero, step, State.z, State.setz,
    Rounds.at_7B1, Rounds.at_7B7, Rounds.at_7BD, Rounds.at_7C3, Rounds.at_7C9, Rounds.at_7CF, Rounds.at_7D5, Rounds.at_7DB, Rounds.at_7E1, Rounds.at_7E7, Rounds.at_7ED, Rounds.at_7F3, Rounds.at_7F9, Rounds.at_800, Rounds.at_807, Rounds.at_80E, Rounds.at_815, Rounds.at_81B, Rounds.at_821, Rounds.at_827, Rounds.at_82D, Rounds.at_833, Rounds.at_839, Rounds.at_83F, Rounds.at_845, Rounds.at_84C, Rounds.at_853, Rounds.at_85A, Rounds.at_861, Rounds.at_867, Rounds.at_86D, Rounds.at_873, Rounds.at_879, Rounds.at_87F, Rounds.at_885, Rounds.at_88B, Rounds.at_891, Rounds.at_897, Rounds.at_89D, Rounds.at_8A3, Rounds.at_8A9, Rounds.at_8B0, Rounds.at_8B7, Rounds.at_8BE, Rounds.at_8C5, Rounds.at_8CB, Rounds.at_8D1, Rounds.at_8D7, Rounds.at_8DD, Rounds.at_8E3, Rounds.at_8E9, Rounds.at_8EF, Rounds.at_8F5, Rounds.at_8FC, Rounds.at_903, Rounds.at_90A, Rounds.at_911, Rounds.at_917, Rounds.at_91D, Rounds.at_923, Rounds.at_929, Rounds.at_92F, Rounds.at_935, Rounds.at_93B, Rounds.at_941, Rounds.at_947, Rounds.at_94D, Rounds.at_953, Rounds.at_959, Rounds.at_960, Rounds.at_967, Rounds.at_96E, Rounds.at_975, Rounds.at_97B, Rounds.at_981, Rounds.at_987, Rounds.at_98D, Rounds.at_993, Rounds.at_999, Rounds.at_99F, Rounds.at_9A5, Rounds.at_9AC, Rounds.at_9B3, Rounds.at_9BA, Rounds.at_9C1, Rounds.at_9C7, Rounds.at_9CD, Rounds.at_9D3, Rounds.at_9D9, Rounds.at_9DF, Rounds.at_9E5, Rounds.at_9EB, Rounds.at_9F1, Rounds.at_9F7, Rounds.at_9FD, Rounds.at_A03, Rounds.at_A09, Rounds.at_A10, Rounds.at_A17, Rounds.at_A1E, Rounds.at_A25, Rounds.at_A2B, Rounds.at_A31, Rounds.at_A37, Rounds.at_A3D, Rounds.at_A43, Rounds.at_A49, Rounds.at_A4F, Rounds.at_A55, Rounds.at_A5C, Rounds.at_A63, Rounds.at_A6A]
  refine ⟨_, rfl, rfl, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  simp only [lane_map2 _ _ _ l hl, lane_map1 _ _ l hl]
  simp (config := {maxSteps := 100000000, implicitDefEqProofs := false}) only [rnd, G, Id.run, pure, Rotr.rotr,
    fv0, fv1, fv2, fv3, fv4, fv5, fv6, fv7, fv8, fv9, fv10, fv11, fv12, fv13, fv14, fv15,
    Vector.set_mk, List.set_toArray, List.set_cons_succ, List.set_cons_zero, Fin.isValue, Fin.getElem_fin,
    Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero,
    Vector.mk.injEq, Array.mk.injEq, List.cons.injEq, and_true]
  bv_decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- Round 3: 112 instructions; message word `i` is in ZMM16+`[3, 4, 10, 12, 13, 2, 7, 14, 6, 5, 9, 0, 11, 15, 8, 1][i]`. -/
theorem round3 (V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12 V13 V14 V15 M0 M1 M2 M3 M4 M5 M6 M7 M8 M9 M10 M11 M12 M13 M14 M15 : Z) (l : Nat) (hl : l < 16) :
    ∃ s', steps Rounds.prog 112 ⟨V0, V1, V2, V3, V4, V5, V6, V7, V8, V9, V10, V11, V12, V13, V14, V15, M0, M1, M2, M3, M4, M5, M6, M7, M8, M9, M10, M11, M12, M13, M14, M15, 0xA71⟩ = some s' ∧ s'.pc = 0xD31 ∧
      #v[lane s'.z0 l, lane s'.z1 l, lane s'.z2 l, lane s'.z3 l, lane s'.z4 l, lane s'.z5 l, lane s'.z6 l, lane s'.z7 l, lane s'.z8 l, lane s'.z9 l, lane s'.z10 l, lane s'.z11 l, lane s'.z12 l, lane s'.z13 l, lane s'.z14 l, lane s'.z15 l] =
        rnd #v[lane V0 l, lane V1 l, lane V2 l, lane V3 l, lane V4 l, lane V5 l, lane V6 l, lane V7 l, lane V8 l, lane V9 l, lane V10 l, lane V11 l, lane V12 l, lane V13 l, lane V14 l, lane V15 l]
          #v[lane M3 l, lane M4 l, lane M10 l, lane M12 l, lane M13 l, lane M2 l, lane M7 l, lane M14 l, lane M6 l, lane M5 l, lane M9 l, lane M0 l, lane M11 l, lane M15 l, lane M8 l, lane M1 l] ∧
      s'.z16 = M0 ∧ s'.z17 = M1 ∧ s'.z18 = M2 ∧ s'.z19 = M3 ∧ s'.z20 = M4 ∧ s'.z21 = M5 ∧ s'.z22 = M6 ∧ s'.z23 = M7 ∧ s'.z24 = M8 ∧ s'.z25 = M9 ∧ s'.z26 = M10 ∧ s'.z27 = M11 ∧ s'.z28 = M12 ∧ s'.z29 = M13 ∧ s'.z30 = M14 ∧ s'.z31 = M15 := by
  simp (config := {maxSteps := 100000000, implicitDefEqProofs := false}) only [steps_mk, steps_zero, step, State.z, State.setz,
    Rounds.at_A71, Rounds.at_A77, Rounds.at_A7D, Rounds.at_A83, Rounds.at_A89, Rounds.at_A8F, Rounds.at_A95, Rounds.at_A9B, Rounds.at_AA1, Rounds.at_AA7, Rounds.at_AAD, Rounds.at_AB3, Rounds.at_AB9, Rounds.at_AC0, Rounds.at_AC7, Rounds.at_ACE, Rounds.at_AD5, Rounds.at_ADB, Rounds.at_AE1, Rounds.at_AE7, Rounds.at_AED, Rounds.at_AF3, Rounds.at_AF9, Rounds.at_AFF, Rounds.at_B05, Rounds.at_B0C, Rounds.at_B13, Rounds.at_B1A, Rounds.at_B21, Rounds.at_B27, Rounds.at_B2D, Rounds.at_B33, Rounds.at_B39, Rounds.at_B3F, Rounds.at_B45, Rounds.at_B4B, Rounds.at_B51, Rounds.at_B57, Rounds.at_B5D, Rounds.at_B63, Rounds.at_B69, Rounds.at_B70, Rounds.at_B77, Rounds.at_B7E, Rounds.at_B85, Rounds.at_B8B, Rounds.at_B91, Rounds.at_B97, Rounds.at_B9D, Rounds.at_BA3, Rounds.at_BA9, Rounds.at_BAF, Rounds.at_BB5, Rounds.at_BBC, Rounds.at_BC3, Rounds.at_BCA, Rounds.at_BD1, Rounds.at_BD7, Rounds.at_BDD, Rounds.at_BE3, Rounds.at_BE9, Rounds.at_BEF, Rounds.at_BF5, Rounds.at_BFB, Rounds.at_C01, Rounds.at_C07, Rounds.at_C0D, Rounds.at_C13, Rounds.at_C19, Rounds.at_C20, Rounds.at_C27, Rounds.at_C2E, Rounds.at_C35, Rounds.at_C3B, Rounds.at_C41, Rounds.at_C47, Rounds.at_C4D, Rounds.at_C53, Rounds.at_C59, Rounds.at_C5F, Rounds.at_C65, Rounds.at_C6C, Rounds.at_C73, Rounds.at_C7A, Rounds.at_C81, Rounds.at_C87, Rounds.at_C8D, Rounds.at_C93, Rounds.at_C99, Rounds.at_C9F, Rounds.at_CA5, Rounds.at_CAB, Rounds.at_CB1, Rounds.at_CB7, Rounds.at_CBD, Rounds.at_CC3, Rounds.at_CC9, Rounds.at_CD0, Rounds.at_CD7, Rounds.at_CDE, Rounds.at_CE5, Rounds.at_CEB, Rounds.at_CF1, Rounds.at_CF7, Rounds.at_CFD, Rounds.at_D03, Rounds.at_D09, Rounds.at_D0F, Rounds.at_D15, Rounds.at_D1C, Rounds.at_D23, Rounds.at_D2A]
  refine ⟨_, rfl, rfl, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  simp only [lane_map2 _ _ _ l hl, lane_map1 _ _ l hl]
  simp (config := {maxSteps := 100000000, implicitDefEqProofs := false}) only [rnd, G, Id.run, pure, Rotr.rotr,
    fv0, fv1, fv2, fv3, fv4, fv5, fv6, fv7, fv8, fv9, fv10, fv11, fv12, fv13, fv14, fv15,
    Vector.set_mk, List.set_toArray, List.set_cons_succ, List.set_cons_zero, Fin.isValue, Fin.getElem_fin,
    Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero,
    Vector.mk.injEq, Array.mk.injEq, List.cons.injEq, and_true]
  bv_decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- Round 4: 112 instructions; message word `i` is in ZMM16+`[10, 7, 12, 9, 14, 3, 13, 15, 4, 0, 11, 2, 5, 8, 1, 6][i]`. -/
theorem round4 (V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12 V13 V14 V15 M0 M1 M2 M3 M4 M5 M6 M7 M8 M9 M10 M11 M12 M13 M14 M15 : Z) (l : Nat) (hl : l < 16) :
    ∃ s', steps Rounds.prog 112 ⟨V0, V1, V2, V3, V4, V5, V6, V7, V8, V9, V10, V11, V12, V13, V14, V15, M0, M1, M2, M3, M4, M5, M6, M7, M8, M9, M10, M11, M12, M13, M14, M15, 0xD31⟩ = some s' ∧ s'.pc = 0xFF1 ∧
      #v[lane s'.z0 l, lane s'.z1 l, lane s'.z2 l, lane s'.z3 l, lane s'.z4 l, lane s'.z5 l, lane s'.z6 l, lane s'.z7 l, lane s'.z8 l, lane s'.z9 l, lane s'.z10 l, lane s'.z11 l, lane s'.z12 l, lane s'.z13 l, lane s'.z14 l, lane s'.z15 l] =
        rnd #v[lane V0 l, lane V1 l, lane V2 l, lane V3 l, lane V4 l, lane V5 l, lane V6 l, lane V7 l, lane V8 l, lane V9 l, lane V10 l, lane V11 l, lane V12 l, lane V13 l, lane V14 l, lane V15 l]
          #v[lane M10 l, lane M7 l, lane M12 l, lane M9 l, lane M14 l, lane M3 l, lane M13 l, lane M15 l, lane M4 l, lane M0 l, lane M11 l, lane M2 l, lane M5 l, lane M8 l, lane M1 l, lane M6 l] ∧
      s'.z16 = M0 ∧ s'.z17 = M1 ∧ s'.z18 = M2 ∧ s'.z19 = M3 ∧ s'.z20 = M4 ∧ s'.z21 = M5 ∧ s'.z22 = M6 ∧ s'.z23 = M7 ∧ s'.z24 = M8 ∧ s'.z25 = M9 ∧ s'.z26 = M10 ∧ s'.z27 = M11 ∧ s'.z28 = M12 ∧ s'.z29 = M13 ∧ s'.z30 = M14 ∧ s'.z31 = M15 := by
  simp (config := {maxSteps := 100000000, implicitDefEqProofs := false}) only [steps_mk, steps_zero, step, State.z, State.setz,
    Rounds.at_D31, Rounds.at_D37, Rounds.at_D3D, Rounds.at_D43, Rounds.at_D49, Rounds.at_D4F, Rounds.at_D55, Rounds.at_D5B, Rounds.at_D61, Rounds.at_D67, Rounds.at_D6D, Rounds.at_D73, Rounds.at_D79, Rounds.at_D80, Rounds.at_D87, Rounds.at_D8E, Rounds.at_D95, Rounds.at_D9B, Rounds.at_DA1, Rounds.at_DA7, Rounds.at_DAD, Rounds.at_DB3, Rounds.at_DB9, Rounds.at_DBF, Rounds.at_DC5, Rounds.at_DCC, Rounds.at_DD3, Rounds.at_DDA, Rounds.at_DE1, Rounds.at_DE7, Rounds.at_DED, Rounds.at_DF3, Rounds.at_DF9, Rounds.at_DFF, Rounds.at_E05, Rounds.at_E0B, Rounds.at_E11, Rounds.at_E17, Rounds.at_E1D, Rounds.at_E23, Rounds.at_E29, Rounds.at_E30, Rounds.at_E37, Rounds.at_E3E, Rounds.at_E45, Rounds.at_E4B, Rounds.at_E51, Rounds.at_E57, Rounds.at_E5D, Rounds.at_E63, Rounds.at_E69, Rounds.at_E6F, Rounds.at_E75, Rounds.at_E7C, Rounds.at_E83, Rounds.at_E8A, Rounds.at_E91, Rounds.at_E97, Rounds.at_E9D, Rounds.at_EA3, Rounds.at_EA9, Rounds.at_EAF, Rounds.at_EB5, Rounds.at_EBB, Rounds.at_EC1, Rounds.at_EC7, Rounds.at_ECD, Rounds.at_ED3, Rounds.at_ED9, Rounds.at_EE0, Rounds.at_EE7, Rounds.at_EEE, Rounds.at_EF5, Rounds.at_EFB, Rounds.at_F01, Rounds.at_F07, Rounds.at_F0D, Rounds.at_F13, Rounds.at_F19, Rounds.at_F1F, Rounds.at_F25, Rounds.at_F2C, Rounds.at_F33, Rounds.at_F3A, Rounds.at_F41, Rounds.at_F47, Rounds.at_F4D, Rounds.at_F53, Rounds.at_F59, Rounds.at_F5F, Rounds.at_F65, Rounds.at_F6B, Rounds.at_F71, Rounds.at_F77, Rounds.at_F7D, Rounds.at_F83, Rounds.at_F89, Rounds.at_F90, Rounds.at_F97, Rounds.at_F9E, Rounds.at_FA5, Rounds.at_FAB, Rounds.at_FB1, Rounds.at_FB7, Rounds.at_FBD, Rounds.at_FC3, Rounds.at_FC9, Rounds.at_FCF, Rounds.at_FD5, Rounds.at_FDC, Rounds.at_FE3, Rounds.at_FEA]
  refine ⟨_, rfl, rfl, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  simp only [lane_map2 _ _ _ l hl, lane_map1 _ _ l hl]
  simp (config := {maxSteps := 100000000, implicitDefEqProofs := false}) only [rnd, G, Id.run, pure, Rotr.rotr,
    fv0, fv1, fv2, fv3, fv4, fv5, fv6, fv7, fv8, fv9, fv10, fv11, fv12, fv13, fv14, fv15,
    Vector.set_mk, List.set_toArray, List.set_cons_succ, List.set_cons_zero, Fin.isValue, Fin.getElem_fin,
    Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero,
    Vector.mk.injEq, Array.mk.injEq, List.cons.injEq, and_true]
  bv_decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- Round 5: 112 instructions; message word `i` is in ZMM16+`[12, 13, 9, 11, 15, 10, 14, 8, 7, 2, 5, 3, 0, 1, 6, 4][i]`. -/
theorem round5 (V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12 V13 V14 V15 M0 M1 M2 M3 M4 M5 M6 M7 M8 M9 M10 M11 M12 M13 M14 M15 : Z) (l : Nat) (hl : l < 16) :
    ∃ s', steps Rounds.prog 112 ⟨V0, V1, V2, V3, V4, V5, V6, V7, V8, V9, V10, V11, V12, V13, V14, V15, M0, M1, M2, M3, M4, M5, M6, M7, M8, M9, M10, M11, M12, M13, M14, M15, 0xFF1⟩ = some s' ∧ s'.pc = 0x12B1 ∧
      #v[lane s'.z0 l, lane s'.z1 l, lane s'.z2 l, lane s'.z3 l, lane s'.z4 l, lane s'.z5 l, lane s'.z6 l, lane s'.z7 l, lane s'.z8 l, lane s'.z9 l, lane s'.z10 l, lane s'.z11 l, lane s'.z12 l, lane s'.z13 l, lane s'.z14 l, lane s'.z15 l] =
        rnd #v[lane V0 l, lane V1 l, lane V2 l, lane V3 l, lane V4 l, lane V5 l, lane V6 l, lane V7 l, lane V8 l, lane V9 l, lane V10 l, lane V11 l, lane V12 l, lane V13 l, lane V14 l, lane V15 l]
          #v[lane M12 l, lane M13 l, lane M9 l, lane M11 l, lane M15 l, lane M10 l, lane M14 l, lane M8 l, lane M7 l, lane M2 l, lane M5 l, lane M3 l, lane M0 l, lane M1 l, lane M6 l, lane M4 l] ∧
      s'.z16 = M0 ∧ s'.z17 = M1 ∧ s'.z18 = M2 ∧ s'.z19 = M3 ∧ s'.z20 = M4 ∧ s'.z21 = M5 ∧ s'.z22 = M6 ∧ s'.z23 = M7 ∧ s'.z24 = M8 ∧ s'.z25 = M9 ∧ s'.z26 = M10 ∧ s'.z27 = M11 ∧ s'.z28 = M12 ∧ s'.z29 = M13 ∧ s'.z30 = M14 ∧ s'.z31 = M15 := by
  simp (config := {maxSteps := 100000000, implicitDefEqProofs := false}) only [steps_mk, steps_zero, step, State.z, State.setz,
    Rounds.at_FF1, Rounds.at_FF7, Rounds.at_FFD, Rounds.at_1003, Rounds.at_1009, Rounds.at_100F, Rounds.at_1015, Rounds.at_101B, Rounds.at_1021, Rounds.at_1027, Rounds.at_102D, Rounds.at_1033, Rounds.at_1039, Rounds.at_1040, Rounds.at_1047, Rounds.at_104E, Rounds.at_1055, Rounds.at_105B, Rounds.at_1061, Rounds.at_1067, Rounds.at_106D, Rounds.at_1073, Rounds.at_1079, Rounds.at_107F, Rounds.at_1085, Rounds.at_108C, Rounds.at_1093, Rounds.at_109A, Rounds.at_10A1, Rounds.at_10A7, Rounds.at_10AD, Rounds.at_10B3, Rounds.at_10B9, Rounds.at_10BF, Rounds.at_10C5, Rounds.at_10CB, Rounds.at_10D1, Rounds.at_10D7, Rounds.at_10DD, Rounds.at_10E3, Rounds.at_10E9, Rounds.at_10F0, Rounds.at_10F7, Rounds.at_10FE, Rounds.at_1105, Rounds.at_110B, Rounds.at_1111, Rounds.at_1117, Rounds.at_111D, Rounds.at_1123, Rounds.at_1129, Rounds.at_112F, Rounds.at_1135, Rounds.at_113C, Rounds.at_1143, Rounds.at_114A, Rounds.at_1151, Rounds.at_1157, Rounds.at_115D, Rounds.at_1163, Rounds.at_1169, Rounds.at_116F, Rounds.at_1175, Rounds.at_117B, Rounds.at_1181, Rounds.at_1187, Rounds.at_118D, Rounds.at_1193, Rounds.at_1199, Rounds.at_11A0, Rounds.at_11A7, Rounds.at_11AE, Rounds.at_11B5, Rounds.at_11BB, Rounds.at_11C1, Rounds.at_11C7, Rounds.at_11CD, Rounds.at_11D3, Rounds.at_11D9, Rounds.at_11DF, Rounds.at_11E5, Rounds.at_11EC, Rounds.at_11F3, Rounds.at_11FA, Rounds.at_1201, Rounds.at_1207, Rounds.at_120D, Rounds.at_1213, Rounds.at_1219, Rounds.at_121F, Rounds.at_1225, Rounds.at_122B, Rounds.at_1231, Rounds.at_1237, Rounds.at_123D, Rounds.at_1243, Rounds.at_1249, Rounds.at_1250, Rounds.at_1257, Rounds.at_125E, Rounds.at_1265, Rounds.at_126B, Rounds.at_1271, Rounds.at_1277, Rounds.at_127D, Rounds.at_1283, Rounds.at_1289, Rounds.at_128F, Rounds.at_1295, Rounds.at_129C, Rounds.at_12A3, Rounds.at_12AA]
  refine ⟨_, rfl, rfl, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  simp only [lane_map2 _ _ _ l hl, lane_map1 _ _ l hl]
  simp (config := {maxSteps := 100000000, implicitDefEqProofs := false}) only [rnd, G, Id.run, pure, Rotr.rotr,
    fv0, fv1, fv2, fv3, fv4, fv5, fv6, fv7, fv8, fv9, fv10, fv11, fv12, fv13, fv14, fv15,
    Vector.set_mk, List.set_toArray, List.set_cons_succ, List.set_cons_zero, Fin.isValue, Fin.getElem_fin,
    Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero,
    Vector.mk.injEq, Array.mk.injEq, List.cons.injEq, and_true]
  bv_decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- Round 6: 112 instructions; message word `i` is in ZMM16+`[9, 14, 11, 5, 8, 12, 15, 1, 13, 3, 0, 10, 2, 6, 4, 7][i]`. -/
theorem round6 (V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12 V13 V14 V15 M0 M1 M2 M3 M4 M5 M6 M7 M8 M9 M10 M11 M12 M13 M14 M15 : Z) (l : Nat) (hl : l < 16) :
    ∃ s', steps Rounds.prog 112 ⟨V0, V1, V2, V3, V4, V5, V6, V7, V8, V9, V10, V11, V12, V13, V14, V15, M0, M1, M2, M3, M4, M5, M6, M7, M8, M9, M10, M11, M12, M13, M14, M15, 0x12B1⟩ = some s' ∧ s'.pc = 0x1571 ∧
      #v[lane s'.z0 l, lane s'.z1 l, lane s'.z2 l, lane s'.z3 l, lane s'.z4 l, lane s'.z5 l, lane s'.z6 l, lane s'.z7 l, lane s'.z8 l, lane s'.z9 l, lane s'.z10 l, lane s'.z11 l, lane s'.z12 l, lane s'.z13 l, lane s'.z14 l, lane s'.z15 l] =
        rnd #v[lane V0 l, lane V1 l, lane V2 l, lane V3 l, lane V4 l, lane V5 l, lane V6 l, lane V7 l, lane V8 l, lane V9 l, lane V10 l, lane V11 l, lane V12 l, lane V13 l, lane V14 l, lane V15 l]
          #v[lane M9 l, lane M14 l, lane M11 l, lane M5 l, lane M8 l, lane M12 l, lane M15 l, lane M1 l, lane M13 l, lane M3 l, lane M0 l, lane M10 l, lane M2 l, lane M6 l, lane M4 l, lane M7 l] ∧
      s'.z16 = M0 ∧ s'.z17 = M1 ∧ s'.z18 = M2 ∧ s'.z19 = M3 ∧ s'.z20 = M4 ∧ s'.z21 = M5 ∧ s'.z22 = M6 ∧ s'.z23 = M7 ∧ s'.z24 = M8 ∧ s'.z25 = M9 ∧ s'.z26 = M10 ∧ s'.z27 = M11 ∧ s'.z28 = M12 ∧ s'.z29 = M13 ∧ s'.z30 = M14 ∧ s'.z31 = M15 := by
  simp (config := {maxSteps := 100000000, implicitDefEqProofs := false}) only [steps_mk, steps_zero, step, State.z, State.setz,
    Rounds.at_12B1, Rounds.at_12B7, Rounds.at_12BD, Rounds.at_12C3, Rounds.at_12C9, Rounds.at_12CF, Rounds.at_12D5, Rounds.at_12DB, Rounds.at_12E1, Rounds.at_12E7, Rounds.at_12ED, Rounds.at_12F3, Rounds.at_12F9, Rounds.at_1300, Rounds.at_1307, Rounds.at_130E, Rounds.at_1315, Rounds.at_131B, Rounds.at_1321, Rounds.at_1327, Rounds.at_132D, Rounds.at_1333, Rounds.at_1339, Rounds.at_133F, Rounds.at_1345, Rounds.at_134C, Rounds.at_1353, Rounds.at_135A, Rounds.at_1361, Rounds.at_1367, Rounds.at_136D, Rounds.at_1373, Rounds.at_1379, Rounds.at_137F, Rounds.at_1385, Rounds.at_138B, Rounds.at_1391, Rounds.at_1397, Rounds.at_139D, Rounds.at_13A3, Rounds.at_13A9, Rounds.at_13B0, Rounds.at_13B7, Rounds.at_13BE, Rounds.at_13C5, Rounds.at_13CB, Rounds.at_13D1, Rounds.at_13D7, Rounds.at_13DD, Rounds.at_13E3, Rounds.at_13E9, Rounds.at_13EF, Rounds.at_13F5, Rounds.at_13FC, Rounds.at_1403, Rounds.at_140A, Rounds.at_1411, Rounds.at_1417, Rounds.at_141D, Rounds.at_1423, Rounds.at_1429, Rounds.at_142F, Rounds.at_1435, Rounds.at_143B, Rounds.at_1441, Rounds.at_1447, Rounds.at_144D, Rounds.at_1453, Rounds.at_1459, Rounds.at_1460, Rounds.at_1467, Rounds.at_146E, Rounds.at_1475, Rounds.at_147B, Rounds.at_1481, Rounds.at_1487, Rounds.at_148D, Rounds.at_1493, Rounds.at_1499, Rounds.at_149F, Rounds.at_14A5, Rounds.at_14AC, Rounds.at_14B3, Rounds.at_14BA, Rounds.at_14C1, Rounds.at_14C7, Rounds.at_14CD, Rounds.at_14D3, Rounds.at_14D9, Rounds.at_14DF, Rounds.at_14E5, Rounds.at_14EB, Rounds.at_14F1, Rounds.at_14F7, Rounds.at_14FD, Rounds.at_1503, Rounds.at_1509, Rounds.at_1510, Rounds.at_1517, Rounds.at_151E, Rounds.at_1525, Rounds.at_152B, Rounds.at_1531, Rounds.at_1537, Rounds.at_153D, Rounds.at_1543, Rounds.at_1549, Rounds.at_154F, Rounds.at_1555, Rounds.at_155C, Rounds.at_1563, Rounds.at_156A]
  refine ⟨_, rfl, rfl, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  simp only [lane_map2 _ _ _ l hl, lane_map1 _ _ l hl]
  simp (config := {maxSteps := 100000000, implicitDefEqProofs := false}) only [rnd, G, Id.run, pure, Rotr.rotr,
    fv0, fv1, fv2, fv3, fv4, fv5, fv6, fv7, fv8, fv9, fv10, fv11, fv12, fv13, fv14, fv15,
    Vector.set_mk, List.set_toArray, List.set_cons_succ, List.set_cons_zero, Fin.isValue, Fin.getElem_fin,
    Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero,
    Vector.mk.injEq, Array.mk.injEq, List.cons.injEq, and_true]
  bv_decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- Round 7: 112 instructions; message word `i` is in ZMM16+`[11, 15, 5, 0, 1, 9, 8, 6, 14, 10, 2, 12, 3, 4, 7, 13][i]`. -/
theorem round7 (V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12 V13 V14 V15 M0 M1 M2 M3 M4 M5 M6 M7 M8 M9 M10 M11 M12 M13 M14 M15 : Z) (l : Nat) (hl : l < 16) :
    ∃ s', steps Rounds.prog 112 ⟨V0, V1, V2, V3, V4, V5, V6, V7, V8, V9, V10, V11, V12, V13, V14, V15, M0, M1, M2, M3, M4, M5, M6, M7, M8, M9, M10, M11, M12, M13, M14, M15, 0x1571⟩ = some s' ∧ s'.pc = 0x1831 ∧
      #v[lane s'.z0 l, lane s'.z1 l, lane s'.z2 l, lane s'.z3 l, lane s'.z4 l, lane s'.z5 l, lane s'.z6 l, lane s'.z7 l, lane s'.z8 l, lane s'.z9 l, lane s'.z10 l, lane s'.z11 l, lane s'.z12 l, lane s'.z13 l, lane s'.z14 l, lane s'.z15 l] =
        rnd #v[lane V0 l, lane V1 l, lane V2 l, lane V3 l, lane V4 l, lane V5 l, lane V6 l, lane V7 l, lane V8 l, lane V9 l, lane V10 l, lane V11 l, lane V12 l, lane V13 l, lane V14 l, lane V15 l]
          #v[lane M11 l, lane M15 l, lane M5 l, lane M0 l, lane M1 l, lane M9 l, lane M8 l, lane M6 l, lane M14 l, lane M10 l, lane M2 l, lane M12 l, lane M3 l, lane M4 l, lane M7 l, lane M13 l] ∧
      s'.z16 = M0 ∧ s'.z17 = M1 ∧ s'.z18 = M2 ∧ s'.z19 = M3 ∧ s'.z20 = M4 ∧ s'.z21 = M5 ∧ s'.z22 = M6 ∧ s'.z23 = M7 ∧ s'.z24 = M8 ∧ s'.z25 = M9 ∧ s'.z26 = M10 ∧ s'.z27 = M11 ∧ s'.z28 = M12 ∧ s'.z29 = M13 ∧ s'.z30 = M14 ∧ s'.z31 = M15 := by
  simp (config := {maxSteps := 100000000, implicitDefEqProofs := false}) only [steps_mk, steps_zero, step, State.z, State.setz,
    Rounds.at_1571, Rounds.at_1577, Rounds.at_157D, Rounds.at_1583, Rounds.at_1589, Rounds.at_158F, Rounds.at_1595, Rounds.at_159B, Rounds.at_15A1, Rounds.at_15A7, Rounds.at_15AD, Rounds.at_15B3, Rounds.at_15B9, Rounds.at_15C0, Rounds.at_15C7, Rounds.at_15CE, Rounds.at_15D5, Rounds.at_15DB, Rounds.at_15E1, Rounds.at_15E7, Rounds.at_15ED, Rounds.at_15F3, Rounds.at_15F9, Rounds.at_15FF, Rounds.at_1605, Rounds.at_160C, Rounds.at_1613, Rounds.at_161A, Rounds.at_1621, Rounds.at_1627, Rounds.at_162D, Rounds.at_1633, Rounds.at_1639, Rounds.at_163F, Rounds.at_1645, Rounds.at_164B, Rounds.at_1651, Rounds.at_1657, Rounds.at_165D, Rounds.at_1663, Rounds.at_1669, Rounds.at_1670, Rounds.at_1677, Rounds.at_167E, Rounds.at_1685, Rounds.at_168B, Rounds.at_1691, Rounds.at_1697, Rounds.at_169D, Rounds.at_16A3, Rounds.at_16A9, Rounds.at_16AF, Rounds.at_16B5, Rounds.at_16BC, Rounds.at_16C3, Rounds.at_16CA, Rounds.at_16D1, Rounds.at_16D7, Rounds.at_16DD, Rounds.at_16E3, Rounds.at_16E9, Rounds.at_16EF, Rounds.at_16F5, Rounds.at_16FB, Rounds.at_1701, Rounds.at_1707, Rounds.at_170D, Rounds.at_1713, Rounds.at_1719, Rounds.at_1720, Rounds.at_1727, Rounds.at_172E, Rounds.at_1735, Rounds.at_173B, Rounds.at_1741, Rounds.at_1747, Rounds.at_174D, Rounds.at_1753, Rounds.at_1759, Rounds.at_175F, Rounds.at_1765, Rounds.at_176C, Rounds.at_1773, Rounds.at_177A, Rounds.at_1781, Rounds.at_1787, Rounds.at_178D, Rounds.at_1793, Rounds.at_1799, Rounds.at_179F, Rounds.at_17A5, Rounds.at_17AB, Rounds.at_17B1, Rounds.at_17B7, Rounds.at_17BD, Rounds.at_17C3, Rounds.at_17C9, Rounds.at_17D0, Rounds.at_17D7, Rounds.at_17DE, Rounds.at_17E5, Rounds.at_17EB, Rounds.at_17F1, Rounds.at_17F7, Rounds.at_17FD, Rounds.at_1803, Rounds.at_1809, Rounds.at_180F, Rounds.at_1815, Rounds.at_181C, Rounds.at_1823, Rounds.at_182A]
  refine ⟨_, rfl, rfl, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  simp only [lane_map2 _ _ _ l hl, lane_map1 _ _ l hl]
  simp (config := {maxSteps := 100000000, implicitDefEqProofs := false}) only [rnd, G, Id.run, pure, Rotr.rotr,
    fv0, fv1, fv2, fv3, fv4, fv5, fv6, fv7, fv8, fv9, fv10, fv11, fv12, fv13, fv14, fv15,
    Vector.set_mk, List.set_toArray, List.set_cons_succ, List.set_cons_zero, Fin.isValue, Fin.getElem_fin,
    Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero,
    Vector.mk.injEq, Array.mk.injEq, List.cons.injEq, and_true]
  bv_decide

