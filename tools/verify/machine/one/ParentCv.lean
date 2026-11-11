import ParentOutputProof
import ChainingValueProof
open X86

/-! # A parent node's chaining value, by the core crate's own compiled code

`hasher::parent_output` then `Output::chaining_value`, the two functions the crate's Rust calls
to turn two children's chaining values into their parent's, are proved here to leave the
specification's parent chaining value: for every pair of children, every key, every mode's
flags, and on either compression kernel. The second function's kernel call is taken from the
kernel's contract. -/

theorem flags_parent (b : BitVec 8) : BitVec.setWidth 32 (b ||| 4) = BitVec.setWidth 32 b ||| 4 := by bv_decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- **The two functions compute the specification's parent chaining value.**

First call: `parent_output(node, left, right, key, flags, platform)` with a return address `ra`.
It returns (to `ra`, with the node's address in RAX).

Second call, from the same stack depth with return address `ra2` (the caller's CALL writes it
where `ra` was): `chaining_value(out, node)`, any values in the other registers.
It returns to `ra2` with `out` in RAX, and the 32 bytes at `out` are the eight words of
`parentCv key left right flags`: the specification's `BLAKE3_COMPRESS` of the key, the block
`left ‖ right`, counter 0, length 64 and the flags with PARENT, first eight words.

What is assumed: the three inputs and the node and `out` are owned memory where stated; the node
is 16-aligned and the stack pointer is as the ABI has it at a call (8 modulo 16); 0x48 bytes
below the stack pointer are owned; and the regions that must not overlap do not (each `a…`). -/
theorem parent_cv_by_the_crates_code (l0 l1 r0 r1 k0 k1 : V) (ra ra2 out : BitVec 64)
    (rax rcx rdx rbx rsp rbp rsi rdi r8 r9 r12 r13 r14 r15 : BitVec 64) (zf cf : Option Bool) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : V) (mem : Mem)
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
    (aTO : ∀ x, (x - rsp).toNat < 8 → 0x78 ≤ (x - rdi).toNat)
    -- for the second call
    (oT : Owned8 mem (rsp + 0)) (oPush : Owned8 mem (rsp - 8)) (oC1 : Owned16 mem (rsp - 8 - 32 + 0x10))
    (oC0 : Owned16 mem (rsp - 8 - 32 + 0x0)) (oCall : Owned8 mem (rsp - 8 - 32 - 8))
    (oU0 : Owned16 mem (out + 0x0)) (oU1 : Owned16 mem (out + 0x10))
    (aOS : ∀ x, (x - rdi).toNat < 0x72 → 0x38 ≤ (x - (rsp - 0x30)).toNat)
    (aUS : ∀ x, (x - out).toNat < 32 → 0x38 ≤ (x - (rsp - 0x30)).toNat) :
    ∃ n1 s1, steps Code.prog n1 ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r12, r13, r14, r15, zf, cf, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, mem, 0x10000⟩ = some s1 ∧ s1.pc = ra.toNat ∧ s1.rax = rdi ∧
      ∀ (rax' rcx' rdx' rbx' rsp' rbp' rsi' rdi' r8' r9' r12' r13' r14' r15' : BitVec 64) (zf' cf' : Option Bool) (x0' x1' x2' x3' x4' x5' x6' x7' x8' x9' x10' x11' x12' x13' x14' x15' : V),
        rdi' = out → rsi' = s1.rax → rsp' = rsp →
        ∃ n2 s2, steps Code.prog n2 ⟨rax', rcx', rdx', rbx', rsp', rbp', rsi', rdi', r8', r9', r12', r13', r14', r15', zf', cf', x0', x1', x2', x3', x4', x5', x6', x7', x8', x9', x10', x11', x12', x13', x14', x15', s1.mem.put64 (rsp + 0) ra2, 0x11000⟩ = some s2 ∧
          s2.pc = ra2.toNat ∧ s2.rax = out ∧ s2.rsp = rsp + 8 ∧
          Vec s2.mem (out + 0x0) (mk4 (parentCv (cvWords k0 k1) l0 l1 r0 r1 (BitVec.setWidth 32 (BitVec.setWidth 8 r8)))[0] (parentCv (cvWords k0 k1) l0 l1 r0 r1 (BitVec.setWidth 32 (BitVec.setWidth 8 r8)))[1]
            (parentCv (cvWords k0 k1) l0 l1 r0 r1 (BitVec.setWidth 32 (BitVec.setWidth 8 r8)))[2] (parentCv (cvWords k0 k1) l0 l1 r0 r1 (BitVec.setWidth 32 (BitVec.setWidth 8 r8)))[3]) ∧
          Vec s2.mem (out + 0x10) (mk4 (parentCv (cvWords k0 k1) l0 l1 r0 r1 (BitVec.setWidth 32 (BitVec.setWidth 8 r8)))[4] (parentCv (cvWords k0 k1) l0 l1 r0 r1 (BitVec.setWidth 32 (BitVec.setWidth 8 r8)))[5]
            (parentCv (cvWords k0 k1) l0 l1 r0 r1 (BitVec.setWidth 32 (BitVec.setWidth 8 r8)))[6] (parentCv (cvWords k0 k1) l0 l1 r0 r1 (BitVec.setWidth 32 (BitVec.setWidth 8 r8)))[7]) := by
  obtain ⟨s1, e1, pc1, sp1, ax1, _, v0, v1, v2, v3, v4, v5, b60, q68, b70, b71, fr1, own1⟩ :=
    parent_output_fills l0 l1 r0 r1 k0 k1 ra rax rcx rdx rbx rsp rbp rsi rdi r8 r9 r12 r13 r14 r15 zf cf x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 mem hL0 hL1 hR0 hR1 hK0 hK1 oS0 oS1 oS2 oS3
      oO0 oO1 oO2 oO3 oO4 oO5 oB60 oQ68 oB70 oB71 hsp hdi hret aRS aKS aKO aTO
  refine ⟨23, s1, e1, pc1, ax1, ?_⟩
  intro rax' rcx' rdx' rbx' rsp' rbp' rsi' rdi' r8' r9' r12' r13' r14' r15' zf' cf' x0' x1' x2' x3' x4' x5' x6' x7' x8' x9' x10' x11' x12' x13' x14' x15' hdi' hsi' hsp'
  subst rdi' rsp'
  rw [ax1] at hsi'
  subst rsi'
  -- the node, as the second call finds it: the return address's eight bytes are not in it
  have keep : ∀ x, (x - rdi).toNat < 0x72 → (s1.mem.put64 (rsp + 0) ra2) x = s1.mem x := fun x hx => by
    have h := aOS x hx
    rw [put64_other _ _ _ x (by bv_omega)]
  have e0 : rdi + 0 = rdi + 0x0 := rfl
  obtain ⟨n2, s2, e2, pc2, sp2, ax2, _, _, o0, o1, _⟩ :=
    chaining_value_is_the_cv k0 k1 l0 l1 r0 r1 0x40 (BitVec.setWidth 8 r8 ||| 4) (BitVec.setWidth 8 r9) 0 ra2
      rax' rcx' rdx' rbx' rsp rbp' rdi out r8' r9' r12' r13' r14' r15' zf' cf' x0' x1' x2' x3' x4' x5' x6' x7' x8' x9' x10' x11' x12' x13' x14' x15' (s1.mem.put64 (rsp + 0) ra2)
      (vec_congr (fun x hx => keep x (by bv_omega)) v4) (vec_congr (fun x hx => keep x (by bv_omega)) v5)
      (vec_congr (fun x hx => keep x (by bv_omega)) v0) (vec_congr (fun x hx => keep x (by bv_omega)) v1)
      (vec_congr (fun x hx => keep x (by bv_omega)) v2) (vec_congr (fun x hx => keep x (by bv_omega)) v3)
      (by rw [keep _ (by bv_omega)]; exact b60) (quad_congr (fun x hx => keep x (by bv_omega)) q68)
      (by rw [keep _ (by bv_omega)]; exact b70) (by rw [keep _ (by bv_omega)]; exact b71)
      (owned8_put64 _ _ _ _ (owned8_mono own1 oPush)) (owned16_put64 _ _ _ _ (owned16_mono own1 oC1))
      (owned16_put64 _ _ _ _ (owned16_mono own1 oC0)) (owned8_put64 _ _ _ _ (owned8_mono own1 oCall))
      hsp hdi (fun x hx => by have h := aOS x hx; bv_omega)
      (owned16_put64 _ _ _ _ (owned16_mono own1 oU0)) (owned16_put64 _ _ _ _ (owned16_mono own1 oU1))
      (by have h := read_quad (quad_put64 s1.mem (rsp + 0) ra2)
          have e : rsp + 0 = rsp := by bv_decide
          rw [e] at h ⊢; exact h) aUS
  refine ⟨n2, s2, e2, pc2, ax2, sp2, ?_, ?_⟩
  · have e : BitVec.setWidth 32 (0x40 : BitVec 8) = 64 := by decide
    rw [e, flags_parent] at o0
    exact o0
  · have e : BitVec.setWidth 32 (0x40 : BitVec 8) = 64 := by decide
    rw [e, flags_parent] at o1
    exact o1

#print axioms parent_cv_by_the_crates_code
