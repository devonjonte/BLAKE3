import Round
open Simd Flat Blake3Generic

theorem add16_ne (a : BitVec 64) : (a + 16 = a + 0) = False := eq_false (by bv_decide)
theorem add0_ne (a : BitVec 64) : (a + 0 = a + 16) = False := eq_false (by bv_decide)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- **Between rounds.** The 16 instructions after a round that is not the last count it and
permute the message words as the specification does. -/
theorem perm (m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 : BitVec 32) (s : State) (hpc : s.pc = 0x381A)
    (hm : Msgs s #v[m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15]) (hal : (s.rax.setWidth 8 - 1 == 0) = false) :
    ∃ s', steps Code.prog 16 s = some s' ∧ s'.pc = 0x3764 ∧ Msgs s' (PERMUTE #v[m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15]) ∧
      (s'.x0 = s.x0 ∧ s'.x1 = s.x1 ∧ s'.x2 = s.x2 ∧ s'.x3 = s.x3) ∧ Kept s s' ∧
      s'.rax.setWidth 8 = s.rax.setWidth 8 - 1 := by
  obtain ⟨rax, rcx, rdx, rsi, rdi, r8, rsp, zf, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, mem, ra, pc⟩ := s
  obtain ⟨hm0, hm1, hm2, hm3⟩ := hm
  simp only at hpc hm0 hm1 hm2 hm3 hal
  subst hpc hm0 hm1 hm2 hm3
  run_kernel_with [hal]
  refine ⟨_, rfl, rfl, ⟨?_, ?_, ?_, ?_⟩, ⟨rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  · eval_spec; open_ops; bv_decide
  · eval_spec; open_ops; bv_decide
  · eval_spec; open_ops; bv_decide
  · eval_spec; open_ops; bv_decide
  · simp only []; bv_decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- **After the last round.** Seven instructions: the two halves are xored, stored where the
chaining value was, and the kernel returns. -/
theorem finish (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : BitVec 32) (s : State) (hpc : s.pc = 0x381A)
    (hv : Rows s #v[v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15]) (hal : (s.rax.setWidth 8 - 1 == 0) = true)
    (h0 : (s.mem (s.rdi + 0)).isSome) (h1 : (s.mem (s.rdi + 16)).isSome) :
    ∃ s', steps Code.prog 7 s = some s' ∧ s'.pc = s.ra ∧ s'.rsp = s.rsp + 8 ∧
      s'.mem (s.rdi + 0) = some (mk4 (v0 ^^^ v8) (v1 ^^^ v9) (v2 ^^^ v10) (v3 ^^^ v11)) ∧
      s'.mem (s.rdi + 16) = some (mk4 (v4 ^^^ v12) (v5 ^^^ v13) (v6 ^^^ v14) (v7 ^^^ v15)) ∧
      ∀ a, a ≠ s.rdi + 0 → a ≠ s.rdi + 16 → s'.mem a = s.mem a := by
  obtain ⟨rax, rcx, rdx, rsi, rdi, r8, rsp, zf, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, mem, ra, pc⟩ := s
  obtain ⟨hv0, hv1, hv2, hv3⟩ := hv
  simp only at hpc hv0 hv1 hv2 hv3 hal h0 h1
  subst hpc hv0 hv1 hv2 hv3
  run_kernel_with [hal, h0, h1, add16_ne]
  refine ⟨_, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · simp only [add0_ne, ↓reduceIte, Option.some.injEq]; eval_spec; open_ops; bv_decide
  · simp only [↓reduceIte, Option.some.injEq]; eval_spec; open_ops; bv_decide
  · intro a ha0 ha1
    simp only [ha0, ha1, ↓reduceIte]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- **Before the first round.** Twenty-one instructions load the chaining value, the IV, the
counter, the length and the flags into the rows, and the block's words where the rounds take them. -/
theorem start (cv0 cv1 b0 b1 b2 b3 : V) (s : State) (hpc : s.pc = 0x3700)
    (hc0 : s.mem (s.rdi + 0) = some cv0) (hc1 : s.mem (s.rdi + 16) = some cv1)
    (hb0 : s.mem (s.rsi + 0) = some b0) (hb1 : s.mem (s.rsi + 16) = some b1)
    (hb2 : s.mem (s.rsi + 32) = some b2) (hb3 : s.mem (s.rsi + 48) = some b3) :
    ∃ s', steps Code.prog 21 s = some s' ∧ s'.pc = 0x3764 ∧
      Rows s' #v[dw cv0 0, dw cv0 1, dw cv0 2, dw cv0 3, dw cv1 0, dw cv1 1, dw cv1 2, dw cv1 3,
        0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, s.rcx.setWidth 32, (s.rcx >>> 32).setWidth 32, (s.rdx.setWidth 8).setWidth 32, (s.r8.setWidth 8).setWidth 32] ∧
      Msgs s' #v[dw b0 0, dw b0 1, dw b0 2, dw b0 3, dw b1 0, dw b1 1, dw b1 2, dw b1 3,
        dw b2 0, dw b2 1, dw b2 2, dw b2 3, dw b3 0, dw b3 1, dw b3 2, dw b3 3] ∧
      s'.rax.setWidth 8 = 7 ∧
      s'.rdi = s.rdi ∧ s'.rsp = s.rsp ∧ s'.mem = s.mem ∧ s'.ra = s.ra := by
  obtain ⟨rax, rcx, rdx, rsi, rdi, r8, rsp, zf, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, mem, ra, pc⟩ := s
  simp only at hpc hc0 hc1 hb0 hb1 hb2 hb3
  subst hpc
  run_kernel_with [hc0, hc1, hb0, hb1, hb2, hb3]
  refine ⟨_, rfl, rfl, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ?_, rfl, rfl, rfl, rfl⟩
  all_goals (try eval_spec)
  all_goals (try open_ops)
  all_goals bv_decide
