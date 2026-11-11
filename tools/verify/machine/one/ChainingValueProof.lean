import ChainingValueProofBase
open X86

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- **`Output::chaining_value` returns the node's chaining value.** Called with the address for
the result in RDI and the node's in RSI (a multiple of 16; the node as `parent_output` and its
like leave it: block at +0, key at +0x40, length at +0x60, counter at +0x68, flags at +0x70,
platform at +0x71), with 48 bytes of stack below the return address and both the node and the
result's 32 bytes apart from them, it returns with RAX the result's address and, at it, the
first eight words of the specification's `BLAKE3_COMPRESS` of the node's key, block, counter,
length and flags: whichever kernel the platform's byte chose. RBX, RBP and R12 to R15 are as
they were, and no byte is changed but the result's 32 and the 48 of its own stack frame. -/
theorem chaining_value_is_the_cv (k0 k1 b0 b1 b2 b3 : V) (len8 fl8 pl8 : BitVec 8) (ctr ra : BitVec 64) (rax rcx rdx rbx rsp rbp rsi rdi r8 r9 r12 r13 r14 r15 : BitVec 64) (zf cf : Option Bool)
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : V) (mem : Mem)
    (hK0 : Vec mem (rsi + 0x40) k0) (hK1 : Vec mem (rsi + 0x50) k1)
    (hB0 : Vec mem (rsi + 0) b0) (hB1 : Vec mem (rsi + 16) b1) (hB2 : Vec mem (rsi + 32) b2) (hB3 : Vec mem (rsi + 48) b3)
    (hLen : mem (rsi + 0x60) = some len8) (hCtr : Quad mem (rsi + 0x68) ctr) (hFl : mem (rsi + 0x70) = some fl8)
    (hPl : mem (rsi + 0x71) = some pl8)
    (oPush : Owned8 mem (rsp - 8)) (oC1 : Owned16 mem (rsp - 8 - 32 + 0x10)) (oC0 : Owned16 mem (rsp - 8 - 32 + 0x0))
    (oCall : Owned8 mem (rsp - 8 - 32 - 8))
    (hsp : rsp &&& 15 = 8) (hsi : rsi &&& 15 = 0)
    (aOS : ∀ x, (x - rsi).toNat < 0x72 → 0x30 ≤ (x - (rsp - 0x30)).toNat)
    (oU0 : Owned16 mem (rdi + 0x0)) (oU1 : Owned16 mem (rdi + 0x10)) (hret : mem.read rsp 64 = some ra)
    (aUS : ∀ x, (x - rdi).toNat < 32 → 0x38 ≤ (x - (rsp - 0x30)).toNat) :
    ∃ k s', steps Code.prog k ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r12, r13, r14, r15, zf, cf, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, mem, 0x11000⟩ = some s' ∧ s'.pc = ra.toNat ∧ s'.rsp = rsp + 8 ∧ s'.rax = rdi ∧ s'.rbx = rbx ∧
      (s'.rbp = rbp ∧ s'.r12 = r12 ∧ s'.r13 = r13 ∧ s'.r14 = r14 ∧ s'.r15 = r15) ∧
      Vec s'.mem (rdi + 0x0) (mk4 (specCv (cvWords k0 k1) (blockWords b0 b1 b2 b3) ctr (BitVec.setWidth 32 len8) (BitVec.setWidth 32 fl8))[0] (specCv (cvWords k0 k1) (blockWords b0 b1 b2 b3) ctr (BitVec.setWidth 32 len8) (BitVec.setWidth 32 fl8))[1]
        (specCv (cvWords k0 k1) (blockWords b0 b1 b2 b3) ctr (BitVec.setWidth 32 len8) (BitVec.setWidth 32 fl8))[2] (specCv (cvWords k0 k1) (blockWords b0 b1 b2 b3) ctr (BitVec.setWidth 32 len8) (BitVec.setWidth 32 fl8))[3]) ∧
      Vec s'.mem (rdi + 0x10) (mk4 (specCv (cvWords k0 k1) (blockWords b0 b1 b2 b3) ctr (BitVec.setWidth 32 len8) (BitVec.setWidth 32 fl8))[4] (specCv (cvWords k0 k1) (blockWords b0 b1 b2 b3) ctr (BitVec.setWidth 32 len8) (BitVec.setWidth 32 fl8))[5]
        (specCv (cvWords k0 k1) (blockWords b0 b1 b2 b3) ctr (BitVec.setWidth 32 len8) (BitVec.setWidth 32 fl8))[6] (specCv (cvWords k0 k1) (blockWords b0 b1 b2 b3) ctr (BitVec.setWidth 32 len8) (BitVec.setWidth 32 fl8))[7]) ∧
      (∀ x, 32 ≤ (x - rdi).toNat → 0x30 ≤ (x - (rsp - 0x30)).toNat → s'.mem x = mem x) := by
  by_cases hp : pl8 = 5
  · -- the AVX-512 kernel
    obtain ⟨s1, e1, pc1, di1, si1, dx1, cx1, r81, sp1, bx1, ⟨bp1, a12, a13, a14, a15⟩, mem1⟩ := pre_avx k0 k1 b0 b1 b2 b3 len8 fl8 pl8 ctr ra rax rcx rdx rbx rsp rbp rsi rdi r8 r9 r12 r13 r14 r15 zf cf x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 mem hK0 hK1 hB0 hB1 hB2 hB3 hLen hCtr hFl hPl oPush oC1 oC0 oCall hsp hsi aOS hp
    have n0 : rsp - 0x28 + 0 = rsp - 0x28 := by bv_decide
    have n16 : rsp - 0x28 + 16 = rsp - 0x18 := by bv_decide
    have hc0 : Vec s1.mem (s1.rdi + 0) k0 := by
      rw [mem1, di1, n0]; exact vec_congr (fun x hx => by rw [put64_other _ _ _ x (by bv_omega)]) (vec_put128 _ _ _)
    have hc1 : Vec s1.mem (s1.rdi + 16) k1 := by
      rw [mem1, di1, n16]
      exact vec_congr (fun x hx => by rw [put64_other _ _ _ x (by bv_omega), put128_other _ _ _ x (by bv_omega)]) (vec_put128 _ _ _)
    have hb0 : Vec s1.mem (s1.rsi + 0) b0 := by
      rw [mem1, si1]; exact vec_congr (fun x hx => by have h := aOS x (by bv_omega); rw [put64_other _ _ _ x (by bv_omega), put128_other _ _ _ x (by bv_omega), put128_other _ _ _ x (by bv_omega), put64_other _ _ _ x (by bv_omega)]) hB0
    have hb1 : Vec s1.mem (s1.rsi + 16) b1 := by
      rw [mem1, si1]; exact vec_congr (fun x hx => by have h := aOS x (by bv_omega); rw [put64_other _ _ _ x (by bv_omega), put128_other _ _ _ x (by bv_omega), put128_other _ _ _ x (by bv_omega), put64_other _ _ _ x (by bv_omega)]) hB1
    have hb2 : Vec s1.mem (s1.rsi + 32) b2 := by
      rw [mem1, si1]; exact vec_congr (fun x hx => by have h := aOS x (by bv_omega); rw [put64_other _ _ _ x (by bv_omega), put128_other _ _ _ x (by bv_omega), put128_other _ _ _ x (by bv_omega), put64_other _ _ _ x (by bv_omega)]) hB2
    have hb3 : Vec s1.mem (s1.rsi + 48) b3 := by
      rw [mem1, si1]; exact vec_congr (fun x hx => by have h := aOS x (by bv_omega); rw [put64_other _ _ _ x (by bv_omega), put128_other _ _ _ x (by bv_omega), put128_other _ _ _ x (by bv_omega), put64_other _ _ _ x (by bv_omega)]) hB3
    have hret1 : s1.mem.read s1.rsp 64 = some (BitVec.ofNat 64 0x1103B) := by
      rw [mem1, sp1]; exact read_quad (quad_put64 _ _ _)
    have hapart1 : ∀ x, (x - s1.rsp).toNat < 8 → 32 ≤ (x - s1.rdi).toNat := by
      rw [sp1, di1]; intro x hx; bv_omega
    obtain ⟨s2, e2, pc2, sp2, mem2, bx2, bp2, c12, c13, c14, c15⟩ :=
      Avx.contract k0 k1 b0 b1 b2 b3 (BitVec.ofNat 64 0x1103B) s1 pc1 hc0 hc1 hb0 hb1 hb2 hb3 hret1 hapart1
    have pc2 : s2.pc = 0x1103B := pc2
    have sp2 : s2.rsp = rsp - 0x28 := by rw [sp2, sp1]; bv_decide
    rw [cx1, dx1, r81, len_of, len_of, di1, mem1, n0, n16] at mem2
    rw [bx1] at bx2
    clear hc0 hc1 hb0 hb1 hb2 hb3 hret1 hapart1 pc1 di1 si1 dx1 cx1 r81 sp1 mem1
    obtain ⟨s3, e3, pc3, sp3, ax3, bx3, ⟨bp3, d12, d13, d14, d15⟩, mem3⟩ := suf_avx _ _ rbx ra s2 pc2
      (by rw [mem2, sp2, show rsp - 0x28 + 0x0 = rsp - 0x28 by bv_decide]
          exact vec_congr (fun x hx => by rw [put128_other _ _ _ x (by bv_omega)]) (vec_put128 _ _ _))
      (by rw [mem2, sp2, show rsp - 0x28 + 0x10 = rsp - 0x18 by bv_decide]; exact vec_put128 _ _ _)
      (by rw [sp2]; simp only [aligned16]; bv_decide) (by rw [sp2]; simp only [aligned16]; bv_decide)
      (by rw [mem2, bx2]; exact owned16_put128 _ _ _ _ (owned16_put128 _ _ _ _ (owned16_put64 _ _ _ _ (owned16_put128 _ _ _ _ (owned16_put128 _ _ _ _ (owned16_put64 _ _ _ _ oU1))))))
      (by rw [mem2, bx2]; exact owned16_put128 _ _ _ _ (owned16_put128 _ _ _ _ (owned16_put64 _ _ _ _ (owned16_put128 _ _ _ _ (owned16_put128 _ _ _ _ (owned16_put64 _ _ _ _ oU0))))))
      (by rw [mem2, sp2, show rsp - 0x28 + 32 = rsp - 8 by bv_decide,
            read_congr (m := mem.put64 (rsp - 8) rbx) _ (fun x hx => by
              rw [put128_other _ _ _ x (by bv_omega), put128_other _ _ _ x (by bv_omega), put64_other _ _ _ x (by bv_omega),
                put128_other _ _ _ x (by bv_omega), put128_other _ _ _ x (by bv_omega)])]
          exact read_quad (quad_put64 _ _ _))
      (by rw [mem2, sp2, show rsp - 0x28 + 32 + 8 = rsp by bv_decide,
            read_congr (m := mem) _ (fun x hx => by
              rw [put128_other _ _ _ x (by bv_omega), put128_other _ _ _ x (by bv_omega), put64_other _ _ _ x (by bv_omega),
                put128_other _ _ _ x (by bv_omega), put128_other _ _ _ x (by bv_omega), put64_other _ _ _ x (by bv_omega)])]
          exact hret)
      (by rw [sp2, bx2, show rsp - 0x28 + 32 = rsp - 8 by bv_decide]
          exact fun x hx => Nat.le_of_not_lt (fun h => by have := aUS x h; bv_omega))
    rw [bx2] at ax3 mem3
    refine ⟨16 + (362 + 9), s3, ?_, pc3, ?_, ax3, bx3, ⟨by rw [bp3, bp2, bp1], by rw [d12, c12, a12], by rw [d13, c13, a13],
      by rw [d14, c14, a14], by rw [d15, c15, a15]⟩, ?_, ?_, ?_⟩
    · rw [steps_add, e1, Option.bind_some, steps_add, e2, Option.bind_some, e3]
    · rw [sp3, sp2]; bv_decide
    · rw [mem3]; exact vec_put128 _ _ _
    · rw [mem3]; exact vec_congr (fun x hx => by rw [put128_other _ _ _ x (by bv_omega)]) (vec_put128 _ _ _)
    · intro x hx hs
      rw [mem3, put128_other _ _ _ x (by bv_omega), put128_other _ _ _ x (by bv_omega), mem2,
        put128_other _ _ _ x (by bv_omega), put128_other _ _ _ x (by bv_omega), put64_other _ _ _ x (by bv_omega), put128_other _ _ _ x (by bv_omega), put128_other _ _ _ x (by bv_omega), put64_other _ _ _ x (by bv_omega)]
  · -- the SSE4.1 kernel
    obtain ⟨s1, e1, pc1, di1, si1, dx1, cx1, r81, sp1, bx1, ⟨bp1, a12, a13, a14, a15⟩, mem1⟩ := pre_sse k0 k1 b0 b1 b2 b3 len8 fl8 pl8 ctr ra rax rcx rdx rbx rsp rbp rsi rdi r8 r9 r12 r13 r14 r15 zf cf x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 mem hK0 hK1 hB0 hB1 hB2 hB3 hLen hCtr hFl hPl oPush oC1 oC0 oCall hsp hsi aOS hp
    have n0 : rsp - 0x28 + 0 = rsp - 0x28 := by bv_decide
    have n16 : rsp - 0x28 + 16 = rsp - 0x18 := by bv_decide
    have hc0 : Vec s1.mem (s1.rdi + 0) k0 := by
      rw [mem1, di1, n0]; exact vec_congr (fun x hx => by rw [put64_other _ _ _ x (by bv_omega)]) (vec_put128 _ _ _)
    have hc1 : Vec s1.mem (s1.rdi + 16) k1 := by
      rw [mem1, di1, n16]
      exact vec_congr (fun x hx => by rw [put64_other _ _ _ x (by bv_omega), put128_other _ _ _ x (by bv_omega)]) (vec_put128 _ _ _)
    have hb0 : Vec s1.mem (s1.rsi + 0) b0 := by
      rw [mem1, si1]; exact vec_congr (fun x hx => by have h := aOS x (by bv_omega); rw [put64_other _ _ _ x (by bv_omega), put128_other _ _ _ x (by bv_omega), put128_other _ _ _ x (by bv_omega), put64_other _ _ _ x (by bv_omega)]) hB0
    have hb1 : Vec s1.mem (s1.rsi + 16) b1 := by
      rw [mem1, si1]; exact vec_congr (fun x hx => by have h := aOS x (by bv_omega); rw [put64_other _ _ _ x (by bv_omega), put128_other _ _ _ x (by bv_omega), put128_other _ _ _ x (by bv_omega), put64_other _ _ _ x (by bv_omega)]) hB1
    have hb2 : Vec s1.mem (s1.rsi + 32) b2 := by
      rw [mem1, si1]; exact vec_congr (fun x hx => by have h := aOS x (by bv_omega); rw [put64_other _ _ _ x (by bv_omega), put128_other _ _ _ x (by bv_omega), put128_other _ _ _ x (by bv_omega), put64_other _ _ _ x (by bv_omega)]) hB2
    have hb3 : Vec s1.mem (s1.rsi + 48) b3 := by
      rw [mem1, si1]; exact vec_congr (fun x hx => by have h := aOS x (by bv_omega); rw [put64_other _ _ _ x (by bv_omega), put128_other _ _ _ x (by bv_omega), put128_other _ _ _ x (by bv_omega), put64_other _ _ _ x (by bv_omega)]) hB3
    have hret1 : s1.mem.read s1.rsp 64 = some (BitVec.ofNat 64 0x1104D) := by
      rw [mem1, sp1]; exact read_quad (quad_put64 _ _ _)
    have hapart1 : ∀ x, (x - s1.rsp).toNat < 8 → 32 ≤ (x - s1.rdi).toNat := by
      rw [sp1, di1]; intro x hx; bv_omega
    obtain ⟨s2, e2, pc2, sp2, mem2, bx2, bp2, c12, c13, c14, c15⟩ :=
      Sse.contract k0 k1 b0 b1 b2 b3 (BitVec.setWidth 32 len8) (BitVec.ofNat 64 0x1104D) s1 pc1 hc0 hc1 hb0 hb1 hb2 hb3 (by rw [dx1, len_of']) hret1 hapart1
    have pc2 : s2.pc = 0x1104D := pc2
    have sp2 : s2.rsp = rsp - 0x28 := by rw [sp2, sp1]; bv_decide
    rw [cx1, r81, flags_of, di1, mem1, n0, n16] at mem2
    rw [bx1] at bx2
    clear hc0 hc1 hb0 hb1 hb2 hb3 hret1 hapart1 pc1 di1 si1 dx1 cx1 r81 sp1 mem1
    obtain ⟨s3, e3, pc3, sp3, ax3, bx3, ⟨bp3, d12, d13, d14, d15⟩, mem3⟩ := suf_sse _ _ rbx ra s2 pc2
      (by rw [mem2, sp2, show rsp - 0x28 + 0x0 = rsp - 0x28 by bv_decide]
          exact vec_congr (fun x hx => by rw [put128_other _ _ _ x (by bv_omega)]) (vec_put128 _ _ _))
      (by rw [mem2, sp2, show rsp - 0x28 + 0x10 = rsp - 0x18 by bv_decide]; exact vec_put128 _ _ _)
      (by rw [sp2]; simp only [aligned16]; bv_decide) (by rw [sp2]; simp only [aligned16]; bv_decide)
      (by rw [mem2, bx2]; exact owned16_put128 _ _ _ _ (owned16_put128 _ _ _ _ (owned16_put64 _ _ _ _ (owned16_put128 _ _ _ _ (owned16_put128 _ _ _ _ (owned16_put64 _ _ _ _ oU1))))))
      (by rw [mem2, bx2]; exact owned16_put128 _ _ _ _ (owned16_put128 _ _ _ _ (owned16_put64 _ _ _ _ (owned16_put128 _ _ _ _ (owned16_put128 _ _ _ _ (owned16_put64 _ _ _ _ oU0))))))
      (by rw [mem2, sp2, show rsp - 0x28 + 32 = rsp - 8 by bv_decide,
            read_congr (m := mem.put64 (rsp - 8) rbx) _ (fun x hx => by
              rw [put128_other _ _ _ x (by bv_omega), put128_other _ _ _ x (by bv_omega), put64_other _ _ _ x (by bv_omega),
                put128_other _ _ _ x (by bv_omega), put128_other _ _ _ x (by bv_omega)])]
          exact read_quad (quad_put64 _ _ _))
      (by rw [mem2, sp2, show rsp - 0x28 + 32 + 8 = rsp by bv_decide,
            read_congr (m := mem) _ (fun x hx => by
              rw [put128_other _ _ _ x (by bv_omega), put128_other _ _ _ x (by bv_omega), put64_other _ _ _ x (by bv_omega),
                put128_other _ _ _ x (by bv_omega), put128_other _ _ _ x (by bv_omega), put64_other _ _ _ x (by bv_omega)])]
          exact hret)
      (by rw [sp2, bx2, show rsp - 0x28 + 32 = rsp - 8 by bv_decide]
          exact fun x hx => Nat.le_of_not_lt (fun h => by have := aUS x h; bv_omega))
    rw [bx2] at ax3 mem3
    refine ⟨16 + (467 + 8), s3, ?_, pc3, ?_, ax3, bx3, ⟨by rw [bp3, bp2, bp1], by rw [d12, c12, a12], by rw [d13, c13, a13],
      by rw [d14, c14, a14], by rw [d15, c15, a15]⟩, ?_, ?_, ?_⟩
    · rw [steps_add, e1, Option.bind_some, steps_add, e2, Option.bind_some, e3]
    · rw [sp3, sp2]; bv_decide
    · rw [mem3]; exact vec_put128 _ _ _
    · rw [mem3]; exact vec_congr (fun x hx => by rw [put128_other _ _ _ x (by bv_omega)]) (vec_put128 _ _ _)
    · intro x hx hs
      rw [mem3, put128_other _ _ _ x (by bv_omega), put128_other _ _ _ x (by bv_omega), mem2,
        put128_other _ _ _ x (by bv_omega), put128_other _ _ _ x (by bv_omega), put64_other _ _ _ x (by bv_omega), put128_other _ _ _ x (by bv_omega), put128_other _ _ _ x (by bv_omega), put64_other _ _ _ x (by bv_omega)]

#print axioms chaining_value_is_the_cv
