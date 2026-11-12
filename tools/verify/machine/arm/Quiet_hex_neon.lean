import Observer
open Arm64

/-! # `hex_neon` shows nothing of what memory holds or of the vector registers

Written by `gen_arm.py` from the assembled kernel's 32 instruction words. To be read: `hex_neon_words`
and the two theorems' statements; `Observer.lean` says what an observer sees. Axioms: Lean's three. -/

set_option maxRecDepth 100000

/-- The kernel's instruction words, as assembled. -/
def hex_neon_words : List (BitVec 32) := [0xad400420, 0x4f00e5e4, 0x4f00e525, 0x4f01e4e6, 0x4f01e607, 0x6f0c0402, 0x4e241c00, 0x6f0c0423, 0x4e241c21, 0x4e003850, 0x4e007851, 0x4e013872, 0x4e017873, 0x6e253600, 0x6e253621, 0x6e253642, 0x6e253663, 0x4e261c00, 0x4e261c21, 0x4e261c42, 0x4e261c63, 0x4e278610, 0x4e278631, 0x4e278652, 0x4e278673, 0x4e208610, 0x4e218631, 0x4e228652, 0x4e238673, 0xad004410, 0xad014c12, 0xd65f03c0]

theorem hex_neon.d0 : decode 0xad400420#32 = some (Arm64.Instr.ldpSimd (Arm64.SimdMemSize.Q128) 0x00#5 0x01#5 (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x01#5) 0x0000000000000000#64)) := by decide +kernel
theorem hex_neon.d1 : decode 0x4f00e5e4#32 = some (Arm64.Instr.simdImmShift true false 0x0#4 0x0#3 0x1c#5 0x0f#5 0x04#5) := by decide +kernel
theorem hex_neon.p1 : RegOnly (Arm64.Instr.simdImmShift true false 0x0#4 0x0#3 0x1c#5 0x0f#5 0x04#5) := fun _ => ⟨rfl, rfl, rfl, rfl, rfl⟩
theorem hex_neon.d2 : decode 0x4f00e525#32 = some (Arm64.Instr.simdImmShift true false 0x0#4 0x0#3 0x1c#5 0x09#5 0x05#5) := by decide +kernel
theorem hex_neon.p2 : RegOnly (Arm64.Instr.simdImmShift true false 0x0#4 0x0#3 0x1c#5 0x09#5 0x05#5) := fun _ => ⟨rfl, rfl, rfl, rfl, rfl⟩
theorem hex_neon.d3 : decode 0x4f01e4e6#32 = some (Arm64.Instr.simdImmShift true false 0x0#4 0x1#3 0x1c#5 0x07#5 0x06#5) := by decide +kernel
theorem hex_neon.p3 : RegOnly (Arm64.Instr.simdImmShift true false 0x0#4 0x1#3 0x1c#5 0x07#5 0x06#5) := fun _ => ⟨rfl, rfl, rfl, rfl, rfl⟩
theorem hex_neon.d4 : decode 0x4f01e607#32 = some (Arm64.Instr.simdImmShift true false 0x0#4 0x1#3 0x1c#5 0x10#5 0x07#5) := by decide +kernel
theorem hex_neon.p4 : RegOnly (Arm64.Instr.simdImmShift true false 0x0#4 0x1#3 0x1c#5 0x10#5 0x07#5) := fun _ => ⟨rfl, rfl, rfl, rfl, rfl⟩
theorem hex_neon.d5 : decode 0x6f0c0402#32 = some (Arm64.Instr.simdImmShift true true 0x1#4 0x4#3 0x00#5 0x00#5 0x02#5) := by decide +kernel
theorem hex_neon.p5 : RegOnly (Arm64.Instr.simdImmShift true true 0x1#4 0x4#3 0x00#5 0x00#5 0x02#5) := fun _ => ⟨rfl, rfl, rfl, rfl, rfl⟩
theorem hex_neon.d6 : decode 0x4e241c00#32 = some (Arm64.Instr.simdThreeSame true false 0x0#2 0x04#5 0x03#5 0x00#5 0x00#5) := by decide +kernel
theorem hex_neon.p6 : RegOnly (Arm64.Instr.simdThreeSame true false 0x0#2 0x04#5 0x03#5 0x00#5 0x00#5) := fun _ => ⟨rfl, rfl, rfl, rfl, rfl⟩
theorem hex_neon.d7 : decode 0x6f0c0423#32 = some (Arm64.Instr.simdImmShift true true 0x1#4 0x4#3 0x00#5 0x01#5 0x03#5) := by decide +kernel
theorem hex_neon.p7 : RegOnly (Arm64.Instr.simdImmShift true true 0x1#4 0x4#3 0x00#5 0x01#5 0x03#5) := fun _ => ⟨rfl, rfl, rfl, rfl, rfl⟩
theorem hex_neon.d8 : decode 0x4e241c21#32 = some (Arm64.Instr.simdThreeSame true false 0x0#2 0x04#5 0x03#5 0x01#5 0x01#5) := by decide +kernel
theorem hex_neon.p8 : RegOnly (Arm64.Instr.simdThreeSame true false 0x0#2 0x04#5 0x03#5 0x01#5 0x01#5) := fun _ => ⟨rfl, rfl, rfl, rfl, rfl⟩
theorem hex_neon.d9 : decode 0x4e003850#32 = some (Arm64.Instr.simdPermute true 0x0#2 0x00#5 0x3#3 0x02#5 0x10#5) := by decide +kernel
theorem hex_neon.p9 : RegOnly (Arm64.Instr.simdPermute true 0x0#2 0x00#5 0x3#3 0x02#5 0x10#5) := fun _ => ⟨rfl, rfl, rfl, rfl, rfl⟩
theorem hex_neon.d10 : decode 0x4e007851#32 = some (Arm64.Instr.simdPermute true 0x0#2 0x00#5 0x7#3 0x02#5 0x11#5) := by decide +kernel
theorem hex_neon.p10 : RegOnly (Arm64.Instr.simdPermute true 0x0#2 0x00#5 0x7#3 0x02#5 0x11#5) := fun _ => ⟨rfl, rfl, rfl, rfl, rfl⟩
theorem hex_neon.d11 : decode 0x4e013872#32 = some (Arm64.Instr.simdPermute true 0x0#2 0x01#5 0x3#3 0x03#5 0x12#5) := by decide +kernel
theorem hex_neon.p11 : RegOnly (Arm64.Instr.simdPermute true 0x0#2 0x01#5 0x3#3 0x03#5 0x12#5) := fun _ => ⟨rfl, rfl, rfl, rfl, rfl⟩
theorem hex_neon.d12 : decode 0x4e017873#32 = some (Arm64.Instr.simdPermute true 0x0#2 0x01#5 0x7#3 0x03#5 0x13#5) := by decide +kernel
theorem hex_neon.p12 : RegOnly (Arm64.Instr.simdPermute true 0x0#2 0x01#5 0x7#3 0x03#5 0x13#5) := fun _ => ⟨rfl, rfl, rfl, rfl, rfl⟩
theorem hex_neon.d13 : decode 0x6e253600#32 = some (Arm64.Instr.simdThreeSame true true 0x0#2 0x05#5 0x06#5 0x10#5 0x00#5) := by decide +kernel
theorem hex_neon.p13 : RegOnly (Arm64.Instr.simdThreeSame true true 0x0#2 0x05#5 0x06#5 0x10#5 0x00#5) := fun _ => ⟨rfl, rfl, rfl, rfl, rfl⟩
theorem hex_neon.d14 : decode 0x6e253621#32 = some (Arm64.Instr.simdThreeSame true true 0x0#2 0x05#5 0x06#5 0x11#5 0x01#5) := by decide +kernel
theorem hex_neon.p14 : RegOnly (Arm64.Instr.simdThreeSame true true 0x0#2 0x05#5 0x06#5 0x11#5 0x01#5) := fun _ => ⟨rfl, rfl, rfl, rfl, rfl⟩
theorem hex_neon.d15 : decode 0x6e253642#32 = some (Arm64.Instr.simdThreeSame true true 0x0#2 0x05#5 0x06#5 0x12#5 0x02#5) := by decide +kernel
theorem hex_neon.p15 : RegOnly (Arm64.Instr.simdThreeSame true true 0x0#2 0x05#5 0x06#5 0x12#5 0x02#5) := fun _ => ⟨rfl, rfl, rfl, rfl, rfl⟩
theorem hex_neon.d16 : decode 0x6e253663#32 = some (Arm64.Instr.simdThreeSame true true 0x0#2 0x05#5 0x06#5 0x13#5 0x03#5) := by decide +kernel
theorem hex_neon.p16 : RegOnly (Arm64.Instr.simdThreeSame true true 0x0#2 0x05#5 0x06#5 0x13#5 0x03#5) := fun _ => ⟨rfl, rfl, rfl, rfl, rfl⟩
theorem hex_neon.d17 : decode 0x4e261c00#32 = some (Arm64.Instr.simdThreeSame true false 0x0#2 0x06#5 0x03#5 0x00#5 0x00#5) := by decide +kernel
theorem hex_neon.p17 : RegOnly (Arm64.Instr.simdThreeSame true false 0x0#2 0x06#5 0x03#5 0x00#5 0x00#5) := fun _ => ⟨rfl, rfl, rfl, rfl, rfl⟩
theorem hex_neon.d18 : decode 0x4e261c21#32 = some (Arm64.Instr.simdThreeSame true false 0x0#2 0x06#5 0x03#5 0x01#5 0x01#5) := by decide +kernel
theorem hex_neon.p18 : RegOnly (Arm64.Instr.simdThreeSame true false 0x0#2 0x06#5 0x03#5 0x01#5 0x01#5) := fun _ => ⟨rfl, rfl, rfl, rfl, rfl⟩
theorem hex_neon.d19 : decode 0x4e261c42#32 = some (Arm64.Instr.simdThreeSame true false 0x0#2 0x06#5 0x03#5 0x02#5 0x02#5) := by decide +kernel
theorem hex_neon.p19 : RegOnly (Arm64.Instr.simdThreeSame true false 0x0#2 0x06#5 0x03#5 0x02#5 0x02#5) := fun _ => ⟨rfl, rfl, rfl, rfl, rfl⟩
theorem hex_neon.d20 : decode 0x4e261c63#32 = some (Arm64.Instr.simdThreeSame true false 0x0#2 0x06#5 0x03#5 0x03#5 0x03#5) := by decide +kernel
theorem hex_neon.p20 : RegOnly (Arm64.Instr.simdThreeSame true false 0x0#2 0x06#5 0x03#5 0x03#5 0x03#5) := fun _ => ⟨rfl, rfl, rfl, rfl, rfl⟩
theorem hex_neon.d21 : decode 0x4e278610#32 = some (Arm64.Instr.simdThreeSame true false 0x0#2 0x07#5 0x10#5 0x10#5 0x10#5) := by decide +kernel
theorem hex_neon.p21 : RegOnly (Arm64.Instr.simdThreeSame true false 0x0#2 0x07#5 0x10#5 0x10#5 0x10#5) := fun _ => ⟨rfl, rfl, rfl, rfl, rfl⟩
theorem hex_neon.d22 : decode 0x4e278631#32 = some (Arm64.Instr.simdThreeSame true false 0x0#2 0x07#5 0x10#5 0x11#5 0x11#5) := by decide +kernel
theorem hex_neon.p22 : RegOnly (Arm64.Instr.simdThreeSame true false 0x0#2 0x07#5 0x10#5 0x11#5 0x11#5) := fun _ => ⟨rfl, rfl, rfl, rfl, rfl⟩
theorem hex_neon.d23 : decode 0x4e278652#32 = some (Arm64.Instr.simdThreeSame true false 0x0#2 0x07#5 0x10#5 0x12#5 0x12#5) := by decide +kernel
theorem hex_neon.p23 : RegOnly (Arm64.Instr.simdThreeSame true false 0x0#2 0x07#5 0x10#5 0x12#5 0x12#5) := fun _ => ⟨rfl, rfl, rfl, rfl, rfl⟩
theorem hex_neon.d24 : decode 0x4e278673#32 = some (Arm64.Instr.simdThreeSame true false 0x0#2 0x07#5 0x10#5 0x13#5 0x13#5) := by decide +kernel
theorem hex_neon.p24 : RegOnly (Arm64.Instr.simdThreeSame true false 0x0#2 0x07#5 0x10#5 0x13#5 0x13#5) := fun _ => ⟨rfl, rfl, rfl, rfl, rfl⟩
theorem hex_neon.d25 : decode 0x4e208610#32 = some (Arm64.Instr.simdThreeSame true false 0x0#2 0x00#5 0x10#5 0x10#5 0x10#5) := by decide +kernel
theorem hex_neon.p25 : RegOnly (Arm64.Instr.simdThreeSame true false 0x0#2 0x00#5 0x10#5 0x10#5 0x10#5) := fun _ => ⟨rfl, rfl, rfl, rfl, rfl⟩
theorem hex_neon.d26 : decode 0x4e218631#32 = some (Arm64.Instr.simdThreeSame true false 0x0#2 0x01#5 0x10#5 0x11#5 0x11#5) := by decide +kernel
theorem hex_neon.p26 : RegOnly (Arm64.Instr.simdThreeSame true false 0x0#2 0x01#5 0x10#5 0x11#5 0x11#5) := fun _ => ⟨rfl, rfl, rfl, rfl, rfl⟩
theorem hex_neon.d27 : decode 0x4e228652#32 = some (Arm64.Instr.simdThreeSame true false 0x0#2 0x02#5 0x10#5 0x12#5 0x12#5) := by decide +kernel
theorem hex_neon.p27 : RegOnly (Arm64.Instr.simdThreeSame true false 0x0#2 0x02#5 0x10#5 0x12#5 0x12#5) := fun _ => ⟨rfl, rfl, rfl, rfl, rfl⟩
theorem hex_neon.d28 : decode 0x4e238673#32 = some (Arm64.Instr.simdThreeSame true false 0x0#2 0x03#5 0x10#5 0x13#5 0x13#5) := by decide +kernel
theorem hex_neon.p28 : RegOnly (Arm64.Instr.simdThreeSame true false 0x0#2 0x03#5 0x10#5 0x13#5 0x13#5) := fun _ => ⟨rfl, rfl, rfl, rfl, rfl⟩
theorem hex_neon.d29 : decode 0xad004410#32 = some (Arm64.Instr.stpSimd (Arm64.SimdMemSize.Q128) 0x10#5 0x11#5 (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x0000000000000000#64)) := by decide +kernel
theorem hex_neon.d30 : decode 0xad014c12#32 = some (Arm64.Instr.stpSimd (Arm64.SimdMemSize.Q128) 0x12#5 0x13#5 (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x0000000000000020#64)) := by decide +kernel
theorem hex_neon.d31 : decode 0xd65f03c0#32 = some (Arm64.Instr.ret (Arm64.Reg.gpr 0x1e#5)) := by decide +kernel

/-- **While `hex_neon` runs, two machines that agree on everything but what memory holds and the vector
registers show the same.** -/
theorem hex_neon_quiet (s s' : State) (h : Agree s s') : runObs hex_neon_words s = runObs hex_neon_words s' := by
  unfold hex_neon_words
  refine cons_ldp hex_neon.d0 h ?_; intro s s' h
  refine cons_reg hex_neon.d1 hex_neon.p1 (fun _ => rfl) h ?_; intro s s' h
  refine cons_reg hex_neon.d2 hex_neon.p2 (fun _ => rfl) h ?_; intro s s' h
  refine cons_reg hex_neon.d3 hex_neon.p3 (fun _ => rfl) h ?_; intro s s' h
  refine cons_reg hex_neon.d4 hex_neon.p4 (fun _ => rfl) h ?_; intro s s' h
  refine cons_reg hex_neon.d5 hex_neon.p5 (fun _ => rfl) h ?_; intro s s' h
  refine cons_reg hex_neon.d6 hex_neon.p6 (fun _ => rfl) h ?_; intro s s' h
  refine cons_reg hex_neon.d7 hex_neon.p7 (fun _ => rfl) h ?_; intro s s' h
  refine cons_reg hex_neon.d8 hex_neon.p8 (fun _ => rfl) h ?_; intro s s' h
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
  refine cons_reg hex_neon.d24 hex_neon.p24 (fun _ => rfl) h ?_; intro s s' h
  refine cons_reg hex_neon.d25 hex_neon.p25 (fun _ => rfl) h ?_; intro s s' h
  refine cons_reg hex_neon.d26 hex_neon.p26 (fun _ => rfl) h ?_; intro s s' h
  refine cons_reg hex_neon.d27 hex_neon.p27 (fun _ => rfl) h ?_; intro s s' h
  refine cons_reg hex_neon.d28 hex_neon.p28 (fun _ => rfl) h ?_; intro s s' h
  refine cons_stp hex_neon.d29 h ?_; intro s s' h
  refine cons_stp hex_neon.d30 h ?_; intro s s' h
  exact cons_ret hex_neon.d31 h

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
  refine seen_cons hex_neon.d27 (fun _ => rfl) ?_
  refine seen_cons hex_neon.d28 (fun _ => rfl) ?_
  refine seen_cons hex_neon.d29 (fun _ => rfl) ?_
  refine seen_cons hex_neon.d30 (fun _ => rfl) ?_
  refine seen_cons hex_neon.d31 (fun _ => rfl) ?_
  exact fun _ => rfl

#print axioms hex_neon_quiet
#print axioms hex_neon_observed
