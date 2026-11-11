import Proof
open Equihash.Verifier

/-- **The arithmetic side.** On two `u32`s the machine's condition is the transcription's, which is
written over the natural numbers: nothing wraps, since `k < n` keeps `k + 1` below `2^32`. -/
theorem accepts_iff (n k : BitVec 32) :
    accepts n k = true ↔
      (n.toNat % 8 = 0 ∧ k.toNat ≥ 3 ∧ k.toNat < n.toNat ∧ n.toNat % (k.toNat + 1) = 0 ∧ n.toNat ≤ 512 ∧
        8 ≤ n.toNat / (k.toNat + 1) ∧ n.toNat / (k.toNat + 1) ≤ 24) := by
  have hn := n.isLt
  have hk := k.isLt
  have e8 : (n % 8 == 0) = decide (n.toNat % 8 = 0) := by
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_eq, ← BitVec.toNat_inj, BitVec.toNat_umod]; rfl
  by_cases hkn : k.toNat < n.toNat
  · have h1 : (k + 1).toNat = k.toNat + 1 := by
      rw [BitVec.toNat_add]; show (k.toNat + 1) % 2 ^ 32 = _; omega
    have em : (n % (k + 1) == 0) = decide (n.toNat % (k.toNat + 1) = 0) := by
      rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_eq, ← BitVec.toNat_inj, BitVec.toNat_umod, h1]; rfl
    have ed : (n / (k + 1)).toNat = n.toNat / (k.toNat + 1) := by rw [BitVec.toNat_udiv, h1]
    simp only [accepts, e8, em, Bool.and_eq_true, decide_eq_true_eq, BitVec.ule, BitVec.ult, ed,
      show (3 : BitVec 32).toNat = 3 from rfl, show (512 : BitVec 32).toNat = 512 from rfl,
      show (8 : BitVec 32).toNat = 8 from rfl, show (24 : BitVec 32).toNat = 24 from rfl]
    exact ⟨fun ⟨⟨⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩, f⟩, g⟩ => ⟨a, b, c, d, e, f, g⟩,
      fun ⟨a, b, c, d, e, f, g⟩ => ⟨⟨⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩, f⟩, g⟩⟩
  · constructor
    · intro h
      simp only [accepts, Bool.and_eq_true, BitVec.ult, decide_eq_true_eq] at h
      exact absurd h.1.1.1.1.2 hkn
    · intro h
      exact absurd h.2.2.1 hkn

/-- The transcription's `Params.new?` on the two `u32`s: the parameters when the machine accepts. -/
theorem new?_eq (n k : BitVec 32) :
    Params.new? n.toNat k.toNat = if accepts n k then some ⟨n.toNat, k.toNat⟩ else none := by
  unfold Params.new?
  by_cases h : accepts n k = true
  · rw [if_pos ((accepts_iff n k).mp h), if_pos h]
  · rw [if_neg (fun h' => h ((accepts_iff n k).mpr h')), if_neg h]

#print axioms new?_eq

set_option maxRecDepth 100000 in
/-- **The compiled `Params::new` is the transcription's `Params.new?`.** For every pair of `u32`s:
the thirty instructions return without a fault and leave at `out` the tag 1, `n` and `k` exactly
when `Params.new? n k` is `some`, and the tag 0 (the other two words unwritten) when it is `none`. -/
theorem params_new_is_new? (cpu : X86.Cpu) (rax rcx rdx rbx rsp rbp rsi out r8 : BitVec 64)
    (hsep : ∀ c d : BitVec 64, (c + 8).ult 16 = true → d.ult 12 = true → (rsp + c == out + d) = false) :
    (X86.run Code.prog cpu 40 (entry rax rcx rdx rbx rsp rbp rsi out r8)).map (seen out) =
      some (out, rsp + 8, rbx, rbp,
        some (if (Params.new? (rsi.setWidth 32).toNat (rdx.setWidth 32).toNat).isSome then 1 else 0),
        if (Params.new? (rsi.setWidth 32).toNat (rdx.setWidth 32).toNat).isSome then some (rsi &&& 0xFFFFFFFF) else none,
        if (Params.new? (rsi.setWidth 32).toNat (rdx.setWidth 32).toNat).isSome then some (rdx &&& 0xFFFFFFFF) else none) := by
  rw [params_new_code cpu rax rcx rdx rbx rsp rbp rsi out r8 hsep, new?_eq]
  cases accepts (rsi.setWidth 32) (rdx.setWidth 32) <;> rfl

#print axioms params_new_is_new?
