import Run
import Flat
open X86

/-! # `hasher::parent_output`, as rustc compiled it in the core crate

Twenty-three instructions: the two children's chaining values, the key, the block length 64,
the counter 0, the flags with PARENT and the platform's byte are written into an `Output`
(and the children's values once more into the red zone below the stack pointer, which nothing
reads). Written by a script from the list of the code's memory writes. -/

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- **`parent_output` fills the node.** Called with the node's address in RDI (a multiple of
16), the left and right children's chaining values at RSI and RDX, the key at RCX, the mode's
flags in R8B and the platform in R9B, it returns to its caller with RAX the node's address and
the node holding: the left value at +0, the right at +0x20, the key at +0x40, the byte 64 at
+0x60, the quadword 0 at +0x68, the flags with PARENT (4) at +0x70 and the platform at +0x71.
It changes no byte outside the node's 0x72 and the 64 below the stack pointer's red zone it uses. -/
theorem parent_output_fills (l0 l1 r0 r1 k0 k1 : V) (ra : BitVec 64) (rax rcx rdx rbx rsp rbp rsi rdi r8 r9 r12 r13 r14 r15 : BitVec 64) (zf cf : Option Bool)
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : V) (mem : Mem)
    (hL0 : Vec mem (rsi + 0x0) l0) (hL1 : Vec mem (rsi + 0x10) l1) (hR0 : Vec mem (rdx + 0x0) r0) (hR1 : Vec mem (rdx + 0x10) r1)
    (hK0 : Vec mem (rcx + 0x0) k0) (hK1 : Vec mem (rcx + 0x10) k1)
    (oS0 : Owned16 mem (rsp + 0xFFFFFFFFFFFFFFB8)) (oS1 : Owned16 mem (rsp + 0xFFFFFFFFFFFFFFC8)) (oS2 : Owned16 mem (rsp + 0xFFFFFFFFFFFFFFD8)) (oS3 : Owned16 mem (rsp + 0xFFFFFFFFFFFFFFE8))
    (oO0 : Owned16 mem (rdi + 0x0)) (oO1 : Owned16 mem (rdi + 0x10)) (oO2 : Owned16 mem (rdi + 0x20)) (oO3 : Owned16 mem (rdi + 0x30))
    (oO4 : Owned16 mem (rdi + 0x40)) (oO5 : Owned16 mem (rdi + 0x50))
    (oB60 : (mem (rdi + 0x60)).isSome) (oQ68 : Owned8 mem (rdi + 0x68)) (oB70 : (mem (rdi + 0x70)).isSome) (oB71 : (mem (rdi + 0x71)).isSome)
    (hsp : rsp &&& 15 = 8) (hdi : rdi &&& 15 = 0) (hret : mem.read rsp 64 = some ra)
    (aRS : ∀ x, (x - rdx).toNat < 32 → 0x40 ≤ (x - (rsp - 0x48)).toNat)
    (aKS : ∀ x, (x - rcx).toNat < 32 → 0x40 ≤ (x - (rsp - 0x48)).toNat)
    (aKO : ∀ x, (x - rcx).toNat < 32 → 0x78 ≤ (x - rdi).toNat)
    (aTO : ∀ x, (x - rsp).toNat < 8 → 0x78 ≤ (x - rdi).toNat) :
    ∃ s', steps Code.prog 23 ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r12, r13, r14, r15, zf, cf, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, mem, 0x10000⟩ = some s' ∧ s'.pc = ra.toNat ∧ s'.rsp = rsp + 8 ∧ s'.rax = rdi ∧
      (s'.rbx = rbx ∧ s'.rbp = rbp ∧ s'.r12 = r12 ∧ s'.r13 = r13 ∧ s'.r14 = r14 ∧ s'.r15 = r15) ∧
      Vec s'.mem (rdi + 0x0) l0 ∧ Vec s'.mem (rdi + 0x10) l1 ∧ Vec s'.mem (rdi + 0x20) r0 ∧ Vec s'.mem (rdi + 0x30) r1 ∧
      Vec s'.mem (rdi + 0x40) k0 ∧ Vec s'.mem (rdi + 0x50) k1 ∧
      s'.mem (rdi + 0x60) = some 0x40 ∧ Quad s'.mem (rdi + 0x68) 0 ∧
      s'.mem (rdi + 0x70) = some (r8.setWidth 8 ||| 4) ∧ s'.mem (rdi + 0x71) = some (r9.setWidth 8) ∧
      (∀ x, 0x78 ≤ (x - rdi).toNat → 0x40 ≤ (x - (rsp - 0x48)).toNat → s'.mem x = mem x) ∧
      (∀ x, (mem x).isSome → (s'.mem x).isSome) := by
  have rR0 : ∀ (v0 : V) (v1 : V), ((mem.put128 (rsp + 0xFFFFFFFFFFFFFFC8) v0).put128 (rsp + 0xFFFFFFFFFFFFFFB8) v1).read128 (rdx + 0x0) = some r0 := fun v0 v1 => by
    rw [read128_congr (m := mem) _ (fun x hx => by
      have hs := aRS x (by bv_omega)
      rw [put128_other _ _ _ x (by bv_omega), put128_other _ _ _ x (by bv_omega)])]
    exact read_vec hR0
  have rR1 : ∀ (v0 : V) (v1 : V), ((mem.put128 (rsp + 0xFFFFFFFFFFFFFFC8) v0).put128 (rsp + 0xFFFFFFFFFFFFFFB8) v1).read128 (rdx + 0x10) = some r1 := fun v0 v1 => by
    rw [read128_congr (m := mem) _ (fun x hx => by
      have hs := aRS x (by bv_omega)
      rw [put128_other _ _ _ x (by bv_omega), put128_other _ _ _ x (by bv_omega)])]
    exact read_vec hR1
  have rK0 : ∀ (v0 : V) (v1 : V) (v2 : V) (v3 : V) (v4 : V) (v5 : V) (v6 : V) (v7 : V), ((((((((mem.put128 (rsp + 0xFFFFFFFFFFFFFFC8) v0).put128 (rsp + 0xFFFFFFFFFFFFFFB8) v1).put128 (rsp + 0xFFFFFFFFFFFFFFD8) v2).put128 (rsp + 0xFFFFFFFFFFFFFFE8) v3).put128 (rdi + 0x30) v4).put128 (rdi + 0x20) v5).put128 (rdi + 0x10) v6).put128 (rdi + 0x0) v7).read128 (rcx + 0x0) = some k0 := fun v0 v1 v2 v3 v4 v5 v6 v7 => by
    rw [read128_congr (m := mem) _ (fun x hx => by
      have hs := aKS x (by bv_omega)
      have ho := aKO x (by bv_omega)
      rw [put128_other _ _ _ x (by bv_omega), put128_other _ _ _ x (by bv_omega), put128_other _ _ _ x (by bv_omega), put128_other _ _ _ x (by bv_omega), put128_other _ _ _ x (by bv_omega), put128_other _ _ _ x (by bv_omega), put128_other _ _ _ x (by bv_omega), put128_other _ _ _ x (by bv_omega)])]
    exact read_vec hK0
  have rK1 : ∀ (v0 : V) (v1 : V) (v2 : V) (v3 : V) (v4 : V) (v5 : V) (v6 : V) (v7 : V), ((((((((mem.put128 (rsp + 0xFFFFFFFFFFFFFFC8) v0).put128 (rsp + 0xFFFFFFFFFFFFFFB8) v1).put128 (rsp + 0xFFFFFFFFFFFFFFD8) v2).put128 (rsp + 0xFFFFFFFFFFFFFFE8) v3).put128 (rdi + 0x30) v4).put128 (rdi + 0x20) v5).put128 (rdi + 0x10) v6).put128 (rdi + 0x0) v7).read128 (rcx + 0x10) = some k1 := fun v0 v1 v2 v3 v4 v5 v6 v7 => by
    rw [read128_congr (m := mem) _ (fun x hx => by
      have hs := aKS x (by bv_omega)
      have ho := aKO x (by bv_omega)
      rw [put128_other _ _ _ x (by bv_omega), put128_other _ _ _ x (by bv_omega), put128_other _ _ _ x (by bv_omega), put128_other _ _ _ x (by bv_omega), put128_other _ _ _ x (by bv_omega), put128_other _ _ _ x (by bv_omega), put128_other _ _ _ x (by bv_omega), put128_other _ _ _ x (by bv_omega)])]
    exact read_vec hK1
  have rRet : ∀ (v0 : V) (v1 : V) (v2 : V) (v3 : V) (v4 : V) (v5 : V) (v6 : V) (v7 : V) (v8 : V) (v9 : V) (v10 : BitVec 8) (v11 : BitVec 64) (v12 : BitVec 8) (v13 : BitVec 8), ((((((((((((((mem.put128 (rsp + 0xFFFFFFFFFFFFFFC8) v0).put128 (rsp + 0xFFFFFFFFFFFFFFB8) v1).put128 (rsp + 0xFFFFFFFFFFFFFFD8) v2).put128 (rsp + 0xFFFFFFFFFFFFFFE8) v3).put128 (rdi + 0x30) v4).put128 (rdi + 0x20) v5).put128 (rdi + 0x10) v6).put128 (rdi + 0x0) v7).put128 (rdi + 0x40) v8).put128 (rdi + 0x50) v9).put8 (rdi + 0x60) v10).put64 (rdi + 0x68) v11).put8 (rdi + 0x70) v12).put8 (rdi + 0x71) v13).read (rsp) 64 = some ra := fun v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 => by
    rw [read_congr (m := mem) _ (fun x hx => by
      have ho := aTO x (by bv_omega)
      rw [put8_far _ _ _ x (by bv_omega), put8_far _ _ _ x (by bv_omega), put64_other _ _ _ x (by bv_omega), put8_far _ _ _ x (by bv_omega), put128_other _ _ _ x (by bv_omega), put128_other _ _ _ x (by bv_omega), put128_other _ _ _ x (by bv_omega), put128_other _ _ _ x (by bv_omega), put128_other _ _ _ x (by bv_omega), put128_other _ _ _ x (by bv_omega), put128_other _ _ _ x (by bv_omega), put128_other _ _ _ x (by bv_omega), put128_other _ _ _ x (by bv_omega), put128_other _ _ _ x (by bv_omega)])]
    exact hret
  have aS1 : aligned16 (rsp + 0xFFFFFFFFFFFFFFC8) = true := by simp only [aligned16]; bv_decide
  have aS0 : aligned16 (rsp + 0xFFFFFFFFFFFFFFB8) = true := by simp only [aligned16]; bv_decide
  have aS2 : aligned16 (rsp + 0xFFFFFFFFFFFFFFD8) = true := by simp only [aligned16]; bv_decide
  have aS3 : aligned16 (rsp + 0xFFFFFFFFFFFFFFE8) = true := by simp only [aligned16]; bv_decide
  have aO3 : aligned16 (rdi + 0x30) = true := by simp only [aligned16]; bv_decide
  have aO2 : aligned16 (rdi + 0x20) = true := by simp only [aligned16]; bv_decide
  have aO1 : aligned16 (rdi + 0x10) = true := by simp only [aligned16]; bv_decide
  have aO0 : aligned16 (rdi + 0x0) = true := by simp only [aligned16]; bv_decide
  have aO4 : aligned16 (rdi + 0x40) = true := by simp only [aligned16]; bv_decide
  have aO5 : aligned16 (rdi + 0x50) = true := by simp only [aligned16]; bv_decide
  have w0 : ∀ (w : V), mem.write128 (rsp + 0xFFFFFFFFFFFFFFC8) w = some (mem.put128 (rsp + 0xFFFFFFFFFFFFFFC8) w) :=
    fun  w => write_vec oS1 w
  have w1 : ∀ (v0 : V) (w : V), (mem.put128 (rsp + 0xFFFFFFFFFFFFFFC8) v0).write128 (rsp + 0xFFFFFFFFFFFFFFB8) w = some ((mem.put128 (rsp + 0xFFFFFFFFFFFFFFC8) v0).put128 (rsp + 0xFFFFFFFFFFFFFFB8) w) :=
    fun v0 w => write_vec (owned16_put128 _ _ _ _ oS0) w
  have w2 : ∀ (v0 : V) (v1 : V) (w : V), ((mem.put128 (rsp + 0xFFFFFFFFFFFFFFC8) v0).put128 (rsp + 0xFFFFFFFFFFFFFFB8) v1).write128 (rsp + 0xFFFFFFFFFFFFFFD8) w = some (((mem.put128 (rsp + 0xFFFFFFFFFFFFFFC8) v0).put128 (rsp + 0xFFFFFFFFFFFFFFB8) v1).put128 (rsp + 0xFFFFFFFFFFFFFFD8) w) :=
    fun v0 v1 w => write_vec (owned16_put128 _ _ _ _ (owned16_put128 _ _ _ _ oS2)) w
  have w3 : ∀ (v0 : V) (v1 : V) (v2 : V) (w : V), (((mem.put128 (rsp + 0xFFFFFFFFFFFFFFC8) v0).put128 (rsp + 0xFFFFFFFFFFFFFFB8) v1).put128 (rsp + 0xFFFFFFFFFFFFFFD8) v2).write128 (rsp + 0xFFFFFFFFFFFFFFE8) w = some ((((mem.put128 (rsp + 0xFFFFFFFFFFFFFFC8) v0).put128 (rsp + 0xFFFFFFFFFFFFFFB8) v1).put128 (rsp + 0xFFFFFFFFFFFFFFD8) v2).put128 (rsp + 0xFFFFFFFFFFFFFFE8) w) :=
    fun v0 v1 v2 w => write_vec (owned16_put128 _ _ _ _ (owned16_put128 _ _ _ _ (owned16_put128 _ _ _ _ oS3))) w
  have w4 : ∀ (v0 : V) (v1 : V) (v2 : V) (v3 : V) (w : V), ((((mem.put128 (rsp + 0xFFFFFFFFFFFFFFC8) v0).put128 (rsp + 0xFFFFFFFFFFFFFFB8) v1).put128 (rsp + 0xFFFFFFFFFFFFFFD8) v2).put128 (rsp + 0xFFFFFFFFFFFFFFE8) v3).write128 (rdi + 0x30) w = some (((((mem.put128 (rsp + 0xFFFFFFFFFFFFFFC8) v0).put128 (rsp + 0xFFFFFFFFFFFFFFB8) v1).put128 (rsp + 0xFFFFFFFFFFFFFFD8) v2).put128 (rsp + 0xFFFFFFFFFFFFFFE8) v3).put128 (rdi + 0x30) w) :=
    fun v0 v1 v2 v3 w => write_vec (owned16_put128 _ _ _ _ (owned16_put128 _ _ _ _ (owned16_put128 _ _ _ _ (owned16_put128 _ _ _ _ oO3)))) w
  have w5 : ∀ (v0 : V) (v1 : V) (v2 : V) (v3 : V) (v4 : V) (w : V), (((((mem.put128 (rsp + 0xFFFFFFFFFFFFFFC8) v0).put128 (rsp + 0xFFFFFFFFFFFFFFB8) v1).put128 (rsp + 0xFFFFFFFFFFFFFFD8) v2).put128 (rsp + 0xFFFFFFFFFFFFFFE8) v3).put128 (rdi + 0x30) v4).write128 (rdi + 0x20) w = some ((((((mem.put128 (rsp + 0xFFFFFFFFFFFFFFC8) v0).put128 (rsp + 0xFFFFFFFFFFFFFFB8) v1).put128 (rsp + 0xFFFFFFFFFFFFFFD8) v2).put128 (rsp + 0xFFFFFFFFFFFFFFE8) v3).put128 (rdi + 0x30) v4).put128 (rdi + 0x20) w) :=
    fun v0 v1 v2 v3 v4 w => write_vec (owned16_put128 _ _ _ _ (owned16_put128 _ _ _ _ (owned16_put128 _ _ _ _ (owned16_put128 _ _ _ _ (owned16_put128 _ _ _ _ oO2))))) w
  have w6 : ∀ (v0 : V) (v1 : V) (v2 : V) (v3 : V) (v4 : V) (v5 : V) (w : V), ((((((mem.put128 (rsp + 0xFFFFFFFFFFFFFFC8) v0).put128 (rsp + 0xFFFFFFFFFFFFFFB8) v1).put128 (rsp + 0xFFFFFFFFFFFFFFD8) v2).put128 (rsp + 0xFFFFFFFFFFFFFFE8) v3).put128 (rdi + 0x30) v4).put128 (rdi + 0x20) v5).write128 (rdi + 0x10) w = some (((((((mem.put128 (rsp + 0xFFFFFFFFFFFFFFC8) v0).put128 (rsp + 0xFFFFFFFFFFFFFFB8) v1).put128 (rsp + 0xFFFFFFFFFFFFFFD8) v2).put128 (rsp + 0xFFFFFFFFFFFFFFE8) v3).put128 (rdi + 0x30) v4).put128 (rdi + 0x20) v5).put128 (rdi + 0x10) w) :=
    fun v0 v1 v2 v3 v4 v5 w => write_vec (owned16_put128 _ _ _ _ (owned16_put128 _ _ _ _ (owned16_put128 _ _ _ _ (owned16_put128 _ _ _ _ (owned16_put128 _ _ _ _ (owned16_put128 _ _ _ _ oO1)))))) w
  have w7 : ∀ (v0 : V) (v1 : V) (v2 : V) (v3 : V) (v4 : V) (v5 : V) (v6 : V) (w : V), (((((((mem.put128 (rsp + 0xFFFFFFFFFFFFFFC8) v0).put128 (rsp + 0xFFFFFFFFFFFFFFB8) v1).put128 (rsp + 0xFFFFFFFFFFFFFFD8) v2).put128 (rsp + 0xFFFFFFFFFFFFFFE8) v3).put128 (rdi + 0x30) v4).put128 (rdi + 0x20) v5).put128 (rdi + 0x10) v6).write128 (rdi + 0x0) w = some ((((((((mem.put128 (rsp + 0xFFFFFFFFFFFFFFC8) v0).put128 (rsp + 0xFFFFFFFFFFFFFFB8) v1).put128 (rsp + 0xFFFFFFFFFFFFFFD8) v2).put128 (rsp + 0xFFFFFFFFFFFFFFE8) v3).put128 (rdi + 0x30) v4).put128 (rdi + 0x20) v5).put128 (rdi + 0x10) v6).put128 (rdi + 0x0) w) :=
    fun v0 v1 v2 v3 v4 v5 v6 w => write_vec (owned16_put128 _ _ _ _ (owned16_put128 _ _ _ _ (owned16_put128 _ _ _ _ (owned16_put128 _ _ _ _ (owned16_put128 _ _ _ _ (owned16_put128 _ _ _ _ (owned16_put128 _ _ _ _ oO0))))))) w
  have w8 : ∀ (v0 : V) (v1 : V) (v2 : V) (v3 : V) (v4 : V) (v5 : V) (v6 : V) (v7 : V) (w : V), ((((((((mem.put128 (rsp + 0xFFFFFFFFFFFFFFC8) v0).put128 (rsp + 0xFFFFFFFFFFFFFFB8) v1).put128 (rsp + 0xFFFFFFFFFFFFFFD8) v2).put128 (rsp + 0xFFFFFFFFFFFFFFE8) v3).put128 (rdi + 0x30) v4).put128 (rdi + 0x20) v5).put128 (rdi + 0x10) v6).put128 (rdi + 0x0) v7).write128 (rdi + 0x40) w = some (((((((((mem.put128 (rsp + 0xFFFFFFFFFFFFFFC8) v0).put128 (rsp + 0xFFFFFFFFFFFFFFB8) v1).put128 (rsp + 0xFFFFFFFFFFFFFFD8) v2).put128 (rsp + 0xFFFFFFFFFFFFFFE8) v3).put128 (rdi + 0x30) v4).put128 (rdi + 0x20) v5).put128 (rdi + 0x10) v6).put128 (rdi + 0x0) v7).put128 (rdi + 0x40) w) :=
    fun v0 v1 v2 v3 v4 v5 v6 v7 w => write_vec (owned16_put128 _ _ _ _ (owned16_put128 _ _ _ _ (owned16_put128 _ _ _ _ (owned16_put128 _ _ _ _ (owned16_put128 _ _ _ _ (owned16_put128 _ _ _ _ (owned16_put128 _ _ _ _ (owned16_put128 _ _ _ _ oO4)))))))) w
  have w9 : ∀ (v0 : V) (v1 : V) (v2 : V) (v3 : V) (v4 : V) (v5 : V) (v6 : V) (v7 : V) (v8 : V) (w : V), (((((((((mem.put128 (rsp + 0xFFFFFFFFFFFFFFC8) v0).put128 (rsp + 0xFFFFFFFFFFFFFFB8) v1).put128 (rsp + 0xFFFFFFFFFFFFFFD8) v2).put128 (rsp + 0xFFFFFFFFFFFFFFE8) v3).put128 (rdi + 0x30) v4).put128 (rdi + 0x20) v5).put128 (rdi + 0x10) v6).put128 (rdi + 0x0) v7).put128 (rdi + 0x40) v8).write128 (rdi + 0x50) w = some ((((((((((mem.put128 (rsp + 0xFFFFFFFFFFFFFFC8) v0).put128 (rsp + 0xFFFFFFFFFFFFFFB8) v1).put128 (rsp + 0xFFFFFFFFFFFFFFD8) v2).put128 (rsp + 0xFFFFFFFFFFFFFFE8) v3).put128 (rdi + 0x30) v4).put128 (rdi + 0x20) v5).put128 (rdi + 0x10) v6).put128 (rdi + 0x0) v7).put128 (rdi + 0x40) v8).put128 (rdi + 0x50) w) :=
    fun v0 v1 v2 v3 v4 v5 v6 v7 v8 w => write_vec (owned16_put128 _ _ _ _ (owned16_put128 _ _ _ _ (owned16_put128 _ _ _ _ (owned16_put128 _ _ _ _ (owned16_put128 _ _ _ _ (owned16_put128 _ _ _ _ (owned16_put128 _ _ _ _ (owned16_put128 _ _ _ _ (owned16_put128 _ _ _ _ oO5))))))))) w
  have w10 : ∀ (v0 : V) (v1 : V) (v2 : V) (v3 : V) (v4 : V) (v5 : V) (v6 : V) (v7 : V) (v8 : V) (v9 : V) (w : BitVec 64), ((((((((((mem.put128 (rsp + 0xFFFFFFFFFFFFFFC8) v0).put128 (rsp + 0xFFFFFFFFFFFFFFB8) v1).put128 (rsp + 0xFFFFFFFFFFFFFFD8) v2).put128 (rsp + 0xFFFFFFFFFFFFFFE8) v3).put128 (rdi + 0x30) v4).put128 (rdi + 0x20) v5).put128 (rdi + 0x10) v6).put128 (rdi + 0x0) v7).put128 (rdi + 0x40) v8).put128 (rdi + 0x50) v9).write (rdi + 0x60) w 8 = some (((((((((((mem.put128 (rsp + 0xFFFFFFFFFFFFFFC8) v0).put128 (rsp + 0xFFFFFFFFFFFFFFB8) v1).put128 (rsp + 0xFFFFFFFFFFFFFFD8) v2).put128 (rsp + 0xFFFFFFFFFFFFFFE8) v3).put128 (rdi + 0x30) v4).put128 (rdi + 0x20) v5).put128 (rdi + 0x10) v6).put128 (rdi + 0x0) v7).put128 (rdi + 0x40) v8).put128 (rdi + 0x50) v9).put8 (rdi + 0x60) (byte w 0)) :=
    fun v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 w => write_byte (put128_isSome _ _ _ _ (put128_isSome _ _ _ _ (put128_isSome _ _ _ _ (put128_isSome _ _ _ _ (put128_isSome _ _ _ _ (put128_isSome _ _ _ _ (put128_isSome _ _ _ _ (put128_isSome _ _ _ _ (put128_isSome _ _ _ _ (put128_isSome _ _ _ _ oB60)))))))))) w
  have w11 : ∀ (v0 : V) (v1 : V) (v2 : V) (v3 : V) (v4 : V) (v5 : V) (v6 : V) (v7 : V) (v8 : V) (v9 : V) (v10 : BitVec 8) (w : BitVec 64), (((((((((((mem.put128 (rsp + 0xFFFFFFFFFFFFFFC8) v0).put128 (rsp + 0xFFFFFFFFFFFFFFB8) v1).put128 (rsp + 0xFFFFFFFFFFFFFFD8) v2).put128 (rsp + 0xFFFFFFFFFFFFFFE8) v3).put128 (rdi + 0x30) v4).put128 (rdi + 0x20) v5).put128 (rdi + 0x10) v6).put128 (rdi + 0x0) v7).put128 (rdi + 0x40) v8).put128 (rdi + 0x50) v9).put8 (rdi + 0x60) v10).write (rdi + 0x68) w 64 = some ((((((((((((mem.put128 (rsp + 0xFFFFFFFFFFFFFFC8) v0).put128 (rsp + 0xFFFFFFFFFFFFFFB8) v1).put128 (rsp + 0xFFFFFFFFFFFFFFD8) v2).put128 (rsp + 0xFFFFFFFFFFFFFFE8) v3).put128 (rdi + 0x30) v4).put128 (rdi + 0x20) v5).put128 (rdi + 0x10) v6).put128 (rdi + 0x0) v7).put128 (rdi + 0x40) v8).put128 (rdi + 0x50) v9).put8 (rdi + 0x60) v10).put64 (rdi + 0x68) w) :=
    fun v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 w => write_quad (owned8_put8 _ _ _ _ (owned8_put128 _ _ _ _ (owned8_put128 _ _ _ _ (owned8_put128 _ _ _ _ (owned8_put128 _ _ _ _ (owned8_put128 _ _ _ _ (owned8_put128 _ _ _ _ (owned8_put128 _ _ _ _ (owned8_put128 _ _ _ _ (owned8_put128 _ _ _ _ (owned8_put128 _ _ _ _ oQ68))))))))))) w
  have w12 : ∀ (v0 : V) (v1 : V) (v2 : V) (v3 : V) (v4 : V) (v5 : V) (v6 : V) (v7 : V) (v8 : V) (v9 : V) (v10 : BitVec 8) (v11 : BitVec 64) (w : BitVec 64), ((((((((((((mem.put128 (rsp + 0xFFFFFFFFFFFFFFC8) v0).put128 (rsp + 0xFFFFFFFFFFFFFFB8) v1).put128 (rsp + 0xFFFFFFFFFFFFFFD8) v2).put128 (rsp + 0xFFFFFFFFFFFFFFE8) v3).put128 (rdi + 0x30) v4).put128 (rdi + 0x20) v5).put128 (rdi + 0x10) v6).put128 (rdi + 0x0) v7).put128 (rdi + 0x40) v8).put128 (rdi + 0x50) v9).put8 (rdi + 0x60) v10).put64 (rdi + 0x68) v11).write (rdi + 0x70) w 8 = some (((((((((((((mem.put128 (rsp + 0xFFFFFFFFFFFFFFC8) v0).put128 (rsp + 0xFFFFFFFFFFFFFFB8) v1).put128 (rsp + 0xFFFFFFFFFFFFFFD8) v2).put128 (rsp + 0xFFFFFFFFFFFFFFE8) v3).put128 (rdi + 0x30) v4).put128 (rdi + 0x20) v5).put128 (rdi + 0x10) v6).put128 (rdi + 0x0) v7).put128 (rdi + 0x40) v8).put128 (rdi + 0x50) v9).put8 (rdi + 0x60) v10).put64 (rdi + 0x68) v11).put8 (rdi + 0x70) (byte w 0)) :=
    fun v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 w => write_byte (put64_isSome _ _ _ _ (put8_isSome _ _ _ _ (put128_isSome _ _ _ _ (put128_isSome _ _ _ _ (put128_isSome _ _ _ _ (put128_isSome _ _ _ _ (put128_isSome _ _ _ _ (put128_isSome _ _ _ _ (put128_isSome _ _ _ _ (put128_isSome _ _ _ _ (put128_isSome _ _ _ _ (put128_isSome _ _ _ _ oB70)))))))))))) w
  have w13 : ∀ (v0 : V) (v1 : V) (v2 : V) (v3 : V) (v4 : V) (v5 : V) (v6 : V) (v7 : V) (v8 : V) (v9 : V) (v10 : BitVec 8) (v11 : BitVec 64) (v12 : BitVec 8) (w : BitVec 64), (((((((((((((mem.put128 (rsp + 0xFFFFFFFFFFFFFFC8) v0).put128 (rsp + 0xFFFFFFFFFFFFFFB8) v1).put128 (rsp + 0xFFFFFFFFFFFFFFD8) v2).put128 (rsp + 0xFFFFFFFFFFFFFFE8) v3).put128 (rdi + 0x30) v4).put128 (rdi + 0x20) v5).put128 (rdi + 0x10) v6).put128 (rdi + 0x0) v7).put128 (rdi + 0x40) v8).put128 (rdi + 0x50) v9).put8 (rdi + 0x60) v10).put64 (rdi + 0x68) v11).put8 (rdi + 0x70) v12).write (rdi + 0x71) w 8 = some ((((((((((((((mem.put128 (rsp + 0xFFFFFFFFFFFFFFC8) v0).put128 (rsp + 0xFFFFFFFFFFFFFFB8) v1).put128 (rsp + 0xFFFFFFFFFFFFFFD8) v2).put128 (rsp + 0xFFFFFFFFFFFFFFE8) v3).put128 (rdi + 0x30) v4).put128 (rdi + 0x20) v5).put128 (rdi + 0x10) v6).put128 (rdi + 0x0) v7).put128 (rdi + 0x40) v8).put128 (rdi + 0x50) v9).put8 (rdi + 0x60) v10).put64 (rdi + 0x68) v11).put8 (rdi + 0x70) v12).put8 (rdi + 0x71) (byte w 0)) :=
    fun v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 w => write_byte (put8_isSome _ _ _ _ (put64_isSome _ _ _ _ (put8_isSome _ _ _ _ (put128_isSome _ _ _ _ (put128_isSome _ _ _ _ (put128_isSome _ _ _ _ (put128_isSome _ _ _ _ (put128_isSome _ _ _ _ (put128_isSome _ _ _ _ (put128_isSome _ _ _ _ (put128_isSome _ _ _ _ (put128_isSome _ _ _ _ (put128_isSome _ _ _ _ oB71))))))))))))) w
  run_code [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, rR0, rR1, rK0, rK1, rRet, read_vec hL0, read_vec hL1, aS1, aS0, aS2, aS3, aO3, aO2, aO1, aO0, aO4, aO5]
  clear w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 rR0 rR1 rK0 rK1 rRet aS1 aS0 aS2 aS3 aO3 aO2 aO1 aO0 aO4 aO5
  refine ⟨_, rfl, rfl, rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals dsimp only
  · exact vec_congr (fun x hx => by rw [put8_far _ _ _ x (by bv_omega), put8_far _ _ _ x (by bv_omega), put64_other _ _ _ x (by bv_omega), put8_far _ _ _ x (by bv_omega), put128_other _ _ _ x (by bv_omega), put128_other _ _ _ x (by bv_omega)]) (vec_put128 _ _ _)
  · exact vec_congr (fun x hx => by rw [put8_far _ _ _ x (by bv_omega), put8_far _ _ _ x (by bv_omega), put64_other _ _ _ x (by bv_omega), put8_far _ _ _ x (by bv_omega), put128_other _ _ _ x (by bv_omega), put128_other _ _ _ x (by bv_omega), put128_other _ _ _ x (by bv_omega)]) (vec_put128 _ _ _)
  · exact vec_congr (fun x hx => by rw [put8_far _ _ _ x (by bv_omega), put8_far _ _ _ x (by bv_omega), put64_other _ _ _ x (by bv_omega), put8_far _ _ _ x (by bv_omega), put128_other _ _ _ x (by bv_omega), put128_other _ _ _ x (by bv_omega), put128_other _ _ _ x (by bv_omega), put128_other _ _ _ x (by bv_omega)]) (vec_put128 _ _ _)
  · exact vec_congr (fun x hx => by rw [put8_far _ _ _ x (by bv_omega), put8_far _ _ _ x (by bv_omega), put64_other _ _ _ x (by bv_omega), put8_far _ _ _ x (by bv_omega), put128_other _ _ _ x (by bv_omega), put128_other _ _ _ x (by bv_omega), put128_other _ _ _ x (by bv_omega), put128_other _ _ _ x (by bv_omega), put128_other _ _ _ x (by bv_omega)]) (vec_put128 _ _ _)
  · exact vec_congr (fun x hx => by rw [put8_far _ _ _ x (by bv_omega), put8_far _ _ _ x (by bv_omega), put64_other _ _ _ x (by bv_omega), put8_far _ _ _ x (by bv_omega), put128_other _ _ _ x (by bv_omega)]) (vec_put128 _ _ _)
  · exact vec_congr (fun x hx => by rw [put8_far _ _ _ x (by bv_omega), put8_far _ _ _ x (by bv_omega), put64_other _ _ _ x (by bv_omega), put8_far _ _ _ x (by bv_omega)]) (vec_put128 _ _ _)
  · rw [put8_far _ _ _ _ (by bv_omega), put8_far _ _ _ _ (by bv_omega), put64_other _ _ _ _ (by bv_omega), put8_same]
    simp only [byte, Option.some.injEq]; bv_decide
  · exact quad_congr (fun x hx => by rw [put8_far _ _ _ x (by bv_omega), put8_far _ _ _ x (by bv_omega)]) (quad_put64 _ _ _)
  · rw [put8_far _ _ _ _ (by bv_omega), put8_same]
    simp only [byte, Option.some.injEq]; bv_decide
  · rw [put8_same]
    simp only [byte, Option.some.injEq]; bv_decide
  · intro x hx hs
    rw [put8_far _ _ _ x (by bv_omega), put8_far _ _ _ x (by bv_omega), put64_other _ _ _ x (by bv_omega), put8_far _ _ _ x (by bv_omega), put128_other _ _ _ x (by bv_omega), put128_other _ _ _ x (by bv_omega), put128_other _ _ _ x (by bv_omega), put128_other _ _ _ x (by bv_omega), put128_other _ _ _ x (by bv_omega), put128_other _ _ _ x (by bv_omega), put128_other _ _ _ x (by bv_omega), put128_other _ _ _ x (by bv_omega), put128_other _ _ _ x (by bv_omega), put128_other _ _ _ x (by bv_omega)]
  · intro x h
    exact (put8_isSome _ _ _ _ (put8_isSome _ _ _ _ (put64_isSome _ _ _ _ (put8_isSome _ _ _ _ (put128_isSome _ _ _ _ (put128_isSome _ _ _ _ (put128_isSome _ _ _ _ (put128_isSome _ _ _ _ (put128_isSome _ _ _ _ (put128_isSome _ _ _ _ (put128_isSome _ _ _ _ (put128_isSome _ _ _ _ (put128_isSome _ _ _ _ (put128_isSome _ _ _ _ h))))))))))))))

#print axioms parent_output_fills
