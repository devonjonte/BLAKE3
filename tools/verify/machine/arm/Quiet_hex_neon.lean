import Observer
open Arm64

/-! # `hex_neon` shows nothing of what memory holds or of the vector registers

Written by `gen_arm.py` from the assembled kernel's 27 instruction words. To be read: `hex_neon_words`
and the two theorems' statements; `Observer.lean` says what an observer sees. Axioms: Lean's three. -/

set_option maxRecDepth 100000

/-- The kernel's instruction words, as assembled. -/
def hex_neon_words : List (BitVec 32) := [0xad400420, 0xd2862609, 0xf2a66649, 0xf2c6a689, 0xf2e6e6c9, 0xd287270a, 0xf2ac4c2a, 0xf2cc8c6a, 0xf2ecccaa, 0x4e081d25, 0x4e181d45, 0x4f00e5e4, 0x6f0c0402, 0x4e241c00, 0x6f0c0423, 0x4e241c21, 0x4e003850, 0x4e007851, 0x4e013872, 0x4e017873, 0x4e1000b0, 0x4e1100b1, 0x4e1200b2, 0x4e1300b3, 0xad004410, 0xad014c12, 0xd65f03c0]

theorem hex_neon.d0 : decode 0xad400420#32 = some (Arm64.Instr.ldpSimd (Arm64.SimdMemSize.Q128) 0x00#5 0x01#5 (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x01#5) 0x0000000000000000#64)) := by decide +kernel
theorem hex_neon.d1 : decode 0xd2862609#32 = some (Arm64.Instr.moveWide (Arm64.RegWidth.W64) (Arm64.MoveWideOp.MOVZ) (Arm64.Reg.gpr 0x09#5) 0x3130#16 0) := by decide +kernel
theorem hex_neon.d2 : decode 0xf2a66649#32 = some (Arm64.Instr.moveWide (Arm64.RegWidth.W64) (Arm64.MoveWideOp.MOVK) (Arm64.Reg.gpr 0x09#5) 0x3332#16 16) := by decide +kernel
theorem hex_neon.d3 : decode 0xf2c6a689#32 = some (Arm64.Instr.moveWide (Arm64.RegWidth.W64) (Arm64.MoveWideOp.MOVK) (Arm64.Reg.gpr 0x09#5) 0x3534#16 32) := by decide +kernel
theorem hex_neon.d4 : decode 0xf2e6e6c9#32 = some (Arm64.Instr.moveWide (Arm64.RegWidth.W64) (Arm64.MoveWideOp.MOVK) (Arm64.Reg.gpr 0x09#5) 0x3736#16 48) := by decide +kernel
theorem hex_neon.d5 : decode 0xd287270a#32 = some (Arm64.Instr.moveWide (Arm64.RegWidth.W64) (Arm64.MoveWideOp.MOVZ) (Arm64.Reg.gpr 0x0a#5) 0x3938#16 0) := by decide +kernel
theorem hex_neon.d6 : decode 0xf2ac4c2a#32 = some (Arm64.Instr.moveWide (Arm64.RegWidth.W64) (Arm64.MoveWideOp.MOVK) (Arm64.Reg.gpr 0x0a#5) 0x6261#16 16) := by decide +kernel
theorem hex_neon.d7 : decode 0xf2cc8c6a#32 = some (Arm64.Instr.moveWide (Arm64.RegWidth.W64) (Arm64.MoveWideOp.MOVK) (Arm64.Reg.gpr 0x0a#5) 0x6463#16 32) := by decide +kernel
theorem hex_neon.d8 : decode 0xf2ecccaa#32 = some (Arm64.Instr.moveWide (Arm64.RegWidth.W64) (Arm64.MoveWideOp.MOVK) (Arm64.Reg.gpr 0x0a#5) 0x6665#16 48) := by decide +kernel
theorem hex_neon.d9 : decode 0x4e081d25#32 = some (Arm64.Instr.simdInsDup true false 0x08#5 0x3#4 0x09#5 0x05#5) := by decide +kernel
theorem hex_neon.p9 : RegOnly (Arm64.Instr.simdInsDup true false 0x08#5 0x3#4 0x09#5 0x05#5) := fun _ => ⟨rfl, rfl, rfl, rfl, rfl⟩
theorem hex_neon.d10 : decode 0x4e181d45#32 = some (Arm64.Instr.simdInsDup true false 0x18#5 0x3#4 0x0a#5 0x05#5) := by decide +kernel
theorem hex_neon.p10 : RegOnly (Arm64.Instr.simdInsDup true false 0x18#5 0x3#4 0x0a#5 0x05#5) := fun _ => ⟨rfl, rfl, rfl, rfl, rfl⟩
theorem hex_neon.d11 : decode 0x4f00e5e4#32 = some (Arm64.Instr.simdImmShift true false 0x0#4 0x0#3 0x1c#5 0x0f#5 0x04#5) := by decide +kernel
theorem hex_neon.p11 : RegOnly (Arm64.Instr.simdImmShift true false 0x0#4 0x0#3 0x1c#5 0x0f#5 0x04#5) := fun _ => ⟨rfl, rfl, rfl, rfl, rfl⟩
theorem hex_neon.d12 : decode 0x6f0c0402#32 = some (Arm64.Instr.simdImmShift true true 0x1#4 0x4#3 0x00#5 0x00#5 0x02#5) := by decide +kernel
theorem hex_neon.p12 : RegOnly (Arm64.Instr.simdImmShift true true 0x1#4 0x4#3 0x00#5 0x00#5 0x02#5) := fun _ => ⟨rfl, rfl, rfl, rfl, rfl⟩
theorem hex_neon.d13 : decode 0x4e241c00#32 = some (Arm64.Instr.simdThreeSame true false 0x0#2 0x04#5 0x03#5 0x00#5 0x00#5) := by decide +kernel
theorem hex_neon.p13 : RegOnly (Arm64.Instr.simdThreeSame true false 0x0#2 0x04#5 0x03#5 0x00#5 0x00#5) := fun _ => ⟨rfl, rfl, rfl, rfl, rfl⟩
theorem hex_neon.d14 : decode 0x6f0c0423#32 = some (Arm64.Instr.simdImmShift true true 0x1#4 0x4#3 0x00#5 0x01#5 0x03#5) := by decide +kernel
theorem hex_neon.p14 : RegOnly (Arm64.Instr.simdImmShift true true 0x1#4 0x4#3 0x00#5 0x01#5 0x03#5) := fun _ => ⟨rfl, rfl, rfl, rfl, rfl⟩
theorem hex_neon.d15 : decode 0x4e241c21#32 = some (Arm64.Instr.simdThreeSame true false 0x0#2 0x04#5 0x03#5 0x01#5 0x01#5) := by decide +kernel
theorem hex_neon.p15 : RegOnly (Arm64.Instr.simdThreeSame true false 0x0#2 0x04#5 0x03#5 0x01#5 0x01#5) := fun _ => ⟨rfl, rfl, rfl, rfl, rfl⟩
theorem hex_neon.d16 : decode 0x4e003850#32 = some (Arm64.Instr.simdPermute true 0x0#2 0x00#5 0x3#3 0x02#5 0x10#5) := by decide +kernel
theorem hex_neon.p16 : RegOnly (Arm64.Instr.simdPermute true 0x0#2 0x00#5 0x3#3 0x02#5 0x10#5) := fun _ => ⟨rfl, rfl, rfl, rfl, rfl⟩
theorem hex_neon.d17 : decode 0x4e007851#32 = some (Arm64.Instr.simdPermute true 0x0#2 0x00#5 0x7#3 0x02#5 0x11#5) := by decide +kernel
theorem hex_neon.p17 : RegOnly (Arm64.Instr.simdPermute true 0x0#2 0x00#5 0x7#3 0x02#5 0x11#5) := fun _ => ⟨rfl, rfl, rfl, rfl, rfl⟩
theorem hex_neon.d18 : decode 0x4e013872#32 = some (Arm64.Instr.simdPermute true 0x0#2 0x01#5 0x3#3 0x03#5 0x12#5) := by decide +kernel
theorem hex_neon.p18 : RegOnly (Arm64.Instr.simdPermute true 0x0#2 0x01#5 0x3#3 0x03#5 0x12#5) := fun _ => ⟨rfl, rfl, rfl, rfl, rfl⟩
theorem hex_neon.d19 : decode 0x4e017873#32 = some (Arm64.Instr.simdPermute true 0x0#2 0x01#5 0x7#3 0x03#5 0x13#5) := by decide +kernel
theorem hex_neon.p19 : RegOnly (Arm64.Instr.simdPermute true 0x0#2 0x01#5 0x7#3 0x03#5 0x13#5) := fun _ => ⟨rfl, rfl, rfl, rfl, rfl⟩
theorem hex_neon.d20 : decode 0x4e1000b0#32 = some (Arm64.Instr.simdTbl true 0x10#5 0x0#2 false 0x05#5 0x10#5) := by decide +kernel
theorem hex_neon.p20 : RegOnly (Arm64.Instr.simdTbl true 0x10#5 0x0#2 false 0x05#5 0x10#5) := fun _ => ⟨rfl, rfl, rfl, rfl, rfl⟩
theorem hex_neon.d21 : decode 0x4e1100b1#32 = some (Arm64.Instr.simdTbl true 0x11#5 0x0#2 false 0x05#5 0x11#5) := by decide +kernel
theorem hex_neon.p21 : RegOnly (Arm64.Instr.simdTbl true 0x11#5 0x0#2 false 0x05#5 0x11#5) := fun _ => ⟨rfl, rfl, rfl, rfl, rfl⟩
theorem hex_neon.d22 : decode 0x4e1200b2#32 = some (Arm64.Instr.simdTbl true 0x12#5 0x0#2 false 0x05#5 0x12#5) := by decide +kernel
theorem hex_neon.p22 : RegOnly (Arm64.Instr.simdTbl true 0x12#5 0x0#2 false 0x05#5 0x12#5) := fun _ => ⟨rfl, rfl, rfl, rfl, rfl⟩
theorem hex_neon.d23 : decode 0x4e1300b3#32 = some (Arm64.Instr.simdTbl true 0x13#5 0x0#2 false 0x05#5 0x13#5) := by decide +kernel
theorem hex_neon.p23 : RegOnly (Arm64.Instr.simdTbl true 0x13#5 0x0#2 false 0x05#5 0x13#5) := fun _ => ⟨rfl, rfl, rfl, rfl, rfl⟩
theorem hex_neon.d24 : decode 0xad004410#32 = some (Arm64.Instr.stpSimd (Arm64.SimdMemSize.Q128) 0x10#5 0x11#5 (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x0000000000000000#64)) := by decide +kernel
theorem hex_neon.d25 : decode 0xad014c12#32 = some (Arm64.Instr.stpSimd (Arm64.SimdMemSize.Q128) 0x12#5 0x13#5 (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x0000000000000020#64)) := by decide +kernel
theorem hex_neon.d26 : decode 0xd65f03c0#32 = some (Arm64.Instr.ret (Arm64.Reg.gpr 0x1e#5)) := by decide +kernel

/-- **While `hex_neon` runs, two machines that agree on everything but what memory holds and the vector
registers show the same.** -/
theorem hex_neon_quiet (s s' : State) (h : Agree s s') : runObs hex_neon_words s = runObs hex_neon_words s' := by
  unfold hex_neon_words
  refine cons_ldp hex_neon.d0 h ?_; intro s s' h
  refine cons_gpr hex_neon.d1 (moveWide_gprOnly _ _ _ _ _ (by decide)) (fun _ => rfl) h ?_; intro s s' h
  refine cons_gpr hex_neon.d2 (moveWide_gprOnly _ _ _ _ _ (by decide)) (fun _ => rfl) h ?_; intro s s' h
  refine cons_gpr hex_neon.d3 (moveWide_gprOnly _ _ _ _ _ (by decide)) (fun _ => rfl) h ?_; intro s s' h
  refine cons_gpr hex_neon.d4 (moveWide_gprOnly _ _ _ _ _ (by decide)) (fun _ => rfl) h ?_; intro s s' h
  refine cons_gpr hex_neon.d5 (moveWide_gprOnly _ _ _ _ _ (by decide)) (fun _ => rfl) h ?_; intro s s' h
  refine cons_gpr hex_neon.d6 (moveWide_gprOnly _ _ _ _ _ (by decide)) (fun _ => rfl) h ?_; intro s s' h
  refine cons_gpr hex_neon.d7 (moveWide_gprOnly _ _ _ _ _ (by decide)) (fun _ => rfl) h ?_; intro s s' h
  refine cons_gpr hex_neon.d8 (moveWide_gprOnly _ _ _ _ _ (by decide)) (fun _ => rfl) h ?_; intro s s' h
  refine cons_reg hex_neon.d9 hex_neon.p9 (fun _ => rfl) h ?_; intro s s' h
  refine cons_reg hex_neon.d10 hex_neon.p10 (fun _ => rfl) h ?_; intro s s' h
  refine cons_reg hex_neon.d11 hex_neon.p11 (fun _ => rfl) h ?_; intro s s' h
  refine cons_reg hex_neon.d12 hex_neon.p12 (fun _ => rfl) h ?_; intro s s' h
  refine cons_reg hex_neon.d13 hex_neon.p13 (fun _ => rfl) h ?_; intro s s' h
  refine cons_reg hex_neon.d14 hex_neon.p14 (fun _ => rfl) h ?_; intro s s' h
  refine cons_reg hex_neon.d15 hex_neon.p15 (fun _ => rfl) h ?_; intro s s' h
  refine cons_reg hex_neon.d16 hex_neon.p16 (fun _ => rfl) h ?_; intro s s' h
  refine cons_reg hex_neon.d17 hex_neon.p17 (fun _ => rfl) h ?_; intro s s' h
  refine cons_reg hex_neon.d18 hex_neon.p18 (fun _ => rfl) h ?_; intro s s' h
  refine cons_reg hex_neon.d19 hex_neon.p19 (fun _ => rfl) h ?_; intro s s' h
  refine cons_reg hex_neon.d20 hex_neon.p20 (fun _ => rfl) h ?_; intro s s' h
  refine cons_reg hex_neon.d21 hex_neon.p21 (fun _ => rfl) h ?_; intro s s' h
  refine cons_reg hex_neon.d22 hex_neon.p22 (fun _ => rfl) h ?_; intro s s' h
  refine cons_reg hex_neon.d23 hex_neon.p23 (fun _ => rfl) h ?_; intro s s' h
  refine cons_stp hex_neon.d24 h ?_; intro s s' h
  refine cons_stp hex_neon.d25 h ?_; intro s s' h
  exact cons_ret hex_neon.d26 h

/-- **The observer has an account of every one of its instructions**: something is always seen, so the
theorem above is not about two runs both unobserved. -/
theorem hex_neon_observed : ∀ s : State, (runObs hex_neon_words s).isSome := by
  unfold hex_neon_words
  refine seen_cons hex_neon.d0 (fun _ => rfl) ?_
  refine seen_cons hex_neon.d1 (fun _ => rfl) ?_
  refine seen_cons hex_neon.d2 (fun _ => rfl) ?_
  refine seen_cons hex_neon.d3 (fun _ => rfl) ?_
  refine seen_cons hex_neon.d4 (fun _ => rfl) ?_
  refine seen_cons hex_neon.d5 (fun _ => rfl) ?_
  refine seen_cons hex_neon.d6 (fun _ => rfl) ?_
  refine seen_cons hex_neon.d7 (fun _ => rfl) ?_
  refine seen_cons hex_neon.d8 (fun _ => rfl) ?_
  refine seen_cons hex_neon.d9 (fun _ => rfl) ?_
  refine seen_cons hex_neon.d10 (fun _ => rfl) ?_
  refine seen_cons hex_neon.d11 (fun _ => rfl) ?_
  refine seen_cons hex_neon.d12 (fun _ => rfl) ?_
  refine seen_cons hex_neon.d13 (fun _ => rfl) ?_
  refine seen_cons hex_neon.d14 (fun _ => rfl) ?_
  refine seen_cons hex_neon.d15 (fun _ => rfl) ?_
  refine seen_cons hex_neon.d16 (fun _ => rfl) ?_
  refine seen_cons hex_neon.d17 (fun _ => rfl) ?_
  refine seen_cons hex_neon.d18 (fun _ => rfl) ?_
  refine seen_cons hex_neon.d19 (fun _ => rfl) ?_
  refine seen_cons hex_neon.d20 (fun _ => rfl) ?_
  refine seen_cons hex_neon.d21 (fun _ => rfl) ?_
  refine seen_cons hex_neon.d22 (fun _ => rfl) ?_
  refine seen_cons hex_neon.d23 (fun _ => rfl) ?_
  refine seen_cons hex_neon.d24 (fun _ => rfl) ?_
  refine seen_cons hex_neon.d25 (fun _ => rfl) ?_
  refine seen_cons hex_neon.d26 (fun _ => rfl) ?_
  exact fun _ => rfl

#print axioms hex_neon_quiet
#print axioms hex_neon_observed
