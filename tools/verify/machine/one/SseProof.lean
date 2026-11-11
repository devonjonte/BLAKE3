import Run
import Flat
open X86 Blake3Generic

/-! # `blake3_servil_compress_in_place_sse41` is the specification's compression function

Written by gen_kernel.py. The theorem at the end is the kernel's contract: what a caller may
take from a call of it. -/

namespace Sse

def ROT8 : V := 0x0C0F0E0D080B0A090407060500030201#128
def ROT16 : V := 0x0D0C0F0E09080B0A0504070601000302#128

/-- The state's four rows are the sixteen words of `v`. -/
def Rows (s : State) (v : Vector (BitVec 32) 16) : Prop :=
  s.x0 = mk4 v[0] v[1] v[2] v[3] ∧ s.x1 = mk4 v[4] v[5] v[6] v[7] ∧ s.x2 = mk4 v[8] v[9] v[10] v[11] ∧ s.x3 = mk4 v[12] v[13] v[14] v[15]

/-- The message words where the round's instructions expect them. -/
def Msgs (s : State) (m : Vector (BitVec 32) 16) : Prop :=
  s.x4 = mk4 m[0] m[2] m[4] m[6] ∧ s.x5 = mk4 m[1] m[3] m[5] m[7] ∧ s.x6 = mk4 m[14] m[8] m[10] m[12] ∧ s.x7 = mk4 m[15] m[9] m[11] m[13]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- **A round.** The 46 instructions from the loop's head are the specification's round on the rows. -/
theorem body (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 : BitVec 32) (s : State) (hpc : s.pc = 0x2006D)
    (hv : Rows s #v[v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15]) (hm : Msgs s #v[m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15]) (h14 : s.x14 = ROT8) (h15 : s.x15 = ROT16) :
    ∃ s', steps Code.prog 46 s = some s' ∧ s'.pc = 0x20147 ∧ Rows s' (rnd #v[v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15] #v[m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15]) ∧
      Msgs s' #v[m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15] ∧ Same s s' ∧ s'.x14 = s.x14 ∧ s'.x15 = s.x15 ∧ s'.rax = s.rax := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r12, r13, r14, r15, zf, cf, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, mem, pc⟩ := s
  obtain ⟨hv0, hv1, hv2, hv3⟩ := hv
  obtain ⟨hm0, hm1, hm2, hm3⟩ := hm
  simp only at hpc hv0 hv1 hv2 hv3 hm0 hm1 hm2 hm3 h14 h15
  subst hpc hv0 hv1 hv2 hv3 hm0 hm1 hm2 hm3 h14 h15
  run_code []
  refine ⟨_, rfl, rfl, ⟨?_, ?_, ?_, ?_⟩, ⟨rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl⟩
  all_goals (eval_spec; simp only [ROT8, ROT16]; open_ops; bv_decide (config := { timeout := 900 }))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- **Between rounds.** The 19 instructions after a round that is not the last count it and
permute the message words as the specification does. -/
theorem perm (m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 : BitVec 32) (s : State) (hpc : s.pc = 0x20147)
    (hm : Msgs s #v[m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15]) (hal : (s.rax.setWidth 8 - 1 == 0) = false) :
    ∃ s', steps Code.prog 19 s = some s' ∧ s'.pc = 0x2006D ∧ Msgs s' (PERMUTE #v[m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15]) ∧
      (s'.x0 = s.x0 ∧ s'.x1 = s.x1 ∧ s'.x2 = s.x2 ∧ s'.x3 = s.x3) ∧ Same s s' ∧ s'.x14 = s.x14 ∧ s'.x15 = s.x15 ∧
      s'.rax.setWidth 8 = s.rax.setWidth 8 - 1 := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r12, r13, r14, r15, zf, cf, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, mem, pc⟩ := s
  obtain ⟨hm0, hm1, hm2, hm3⟩ := hm
  simp only at hpc hm0 hm1 hm2 hm3 hal
  subst hpc hm0 hm1 hm2 hm3
  run_code [hal]
  refine ⟨_, rfl, rfl, ⟨?_, ?_, ?_, ?_⟩, ⟨rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, ?_⟩
  · eval_spec; open_ops; bv_decide (config := { timeout := 900 })
  · eval_spec; open_ops; bv_decide (config := { timeout := 900 })
  · eval_spec; open_ops; bv_decide (config := { timeout := 900 })
  · eval_spec; open_ops; bv_decide (config := { timeout := 900 })
  · simp only []; bv_decide (config := { timeout := 900 })

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- **After the last round.** Seven instructions: the two halves are xored, stored where the
chaining value was, and the kernel returns to the address on the stack. -/
theorem finish (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : BitVec 32) (ra : BitVec 64) (s : State) (hpc : s.pc = 0x20147)
    (hv : Rows s #v[v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15]) (hal : (s.rax.setWidth 8 - 1 == 0) = true)
    (o0 : Owned16 s.mem (s.rdi + 0)) (o1 : Owned16 s.mem (s.rdi + 16))
    (hret : s.mem.read s.rsp 64 = some ra) (hapart : ∀ x, (x - s.rsp).toNat < 8 → 32 ≤ (x - s.rdi).toNat) :
    ∃ s', steps Code.prog 7 s = some s' ∧ s'.pc = ra.toNat ∧ s'.rsp = s.rsp + 8 ∧
      s'.mem = (s.mem.put128 (s.rdi + 0) (mk4 (v0 ^^^ v8) (v1 ^^^ v9) (v2 ^^^ v10) (v3 ^^^ v11))).put128 (s.rdi + 16)
        (mk4 (v4 ^^^ v12) (v5 ^^^ v13) (v6 ^^^ v14) (v7 ^^^ v15)) ∧
      s'.rbx = s.rbx ∧ s'.rbp = s.rbp ∧ s'.r12 = s.r12 ∧ s'.r13 = s.r13 ∧ s'.r14 = s.r14 ∧ s'.r15 = s.r15 := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r12, r13, r14, r15, zf, cf, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, mem, pc⟩ := s
  obtain ⟨hv0, hv1, hv2, hv3⟩ := hv
  simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero] at hpc hv0 hv1 hv2 hv3 hal o0 o1 hret hapart
  subst hpc hv0 hv1 hv2 hv3
  have w1 : ∀ (a b : V), (mem.put128 (rdi + 0) a).write128 (rdi + 16) b = some ((mem.put128 (rdi + 0) a).put128 (rdi + 16) b) :=
    fun a b => write_vec (owned16_put128 _ _ _ _ o1) b
  have r1 : ∀ (a b : V), ((mem.put128 (rdi + 0) a).put128 (rdi + 16) b).read rsp 64 = some ra := fun a b => by
    rw [read_congr (m := mem) _ (fun x hx => by
      have := hapart x hx
      rw [put128_other _ _ _ x (by bv_omega), put128_other _ _ _ x (by bv_omega)])]
    exact hret
  have e0 : mk4 v0 v1 v2 v3 ^^^ mk4 v8 v9 v10 v11 = mk4 (v0 ^^^ v8) (v1 ^^^ v9) (v2 ^^^ v10) (v3 ^^^ v11) := by
    open_ops; bv_decide (config := { timeout := 900 })
  have e1 : mk4 v4 v5 v6 v7 ^^^ mk4 v12 v13 v14 v15 = mk4 (v4 ^^^ v12) (v5 ^^^ v13) (v6 ^^^ v14) (v7 ^^^ v15) := by
    open_ops; bv_decide (config := { timeout := 900 })
  run_code [hal, write_vec o0, w1, r1, e0, e1]
  exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- **Before the first round.** 24 instructions load the chaining value, the IV, the counter,
the length and the flags into the rows, and the block's words where the rounds take them. -/
theorem start (cv0 cv1 b0 b1 b2 b3 : V) (len : BitVec 32) (s : State) (hpc : s.pc = 0x20000)
    (hc0 : Vec s.mem (s.rdi + 0) cv0) (hc1 : Vec s.mem (s.rdi + 16) cv1)
    (hb0 : Vec s.mem (s.rsi + 0) b0) (hb1 : Vec s.mem (s.rsi + 16) b1)
    (hb2 : Vec s.mem (s.rsi + 32) b2) (hb3 : Vec s.mem (s.rsi + 48) b3) (hlen : s.rdx = len.setWidth 64) :
    ∃ s', steps Code.prog 24 s = some s' ∧ s'.pc = 0x2006D ∧
      Rows s' #v[dw cv0 0, dw cv0 1, dw cv0 2, dw cv0 3, dw cv1 0, dw cv1 1, dw cv1 2, dw cv1 3,
        0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, s.rcx.setWidth 32, (s.rcx >>> 32).setWidth 32, len, s.r8.setWidth 32] ∧
      Msgs s' #v[dw b0 0, dw b0 1, dw b0 2, dw b0 3, dw b1 0, dw b1 1, dw b1 2, dw b1 3,
        dw b2 0, dw b2 1, dw b2 2, dw b2 3, dw b3 0, dw b3 1, dw b3 2, dw b3 3] ∧
      s'.x14 = ROT8 ∧ s'.x15 = ROT16 ∧ s'.rax.setWidth 8 = 7 ∧ Same s s' := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r12, r13, r14, r15, zf, cf, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, mem, pc⟩ := s
  simp only at hpc hc0 hc1 hb0 hb1 hb2 hb3 hlen
  subst hpc hlen
  run_code [read_vec hc0, read_vec hc1, read_vec hb0, read_vec hb1, read_vec hb2, read_vec hb3]
  refine ⟨_, rfl, rfl, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, rfl, rfl, ?_, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
  all_goals (try eval_spec)
  all_goals (try open_ops)
  all_goals bv_decide (config := { timeout := 900 })

theorem body' (v m : Vector (BitVec 32) 16) (s : State) (hpc : s.pc = 0x2006D)
    (hv : Rows s v) (hm : Msgs s m) (h14 : s.x14 = ROT8) (h15 : s.x15 = ROT16) :
    ∃ s', steps Code.prog 46 s = some s' ∧ s'.pc = 0x20147 ∧ Rows s' (rnd v m) ∧ Msgs s' m ∧ Same s s' ∧
      s'.x14 = s.x14 ∧ s'.x15 = s.x15 ∧ s'.rax = s.rax := by
  have h := body v[0] v[1] v[2] v[3] v[4] v[5] v[6] v[7] v[8] v[9] v[10] v[11] v[12] v[13] v[14] v[15] m[0] m[1] m[2] m[3] m[4] m[5] m[6] m[7] m[8] m[9] m[10] m[11] m[12] m[13] m[14] m[15] s hpc (by rw [eta16]; exact hv) (by rw [eta16]; exact hm) h14 h15
  rwa [eta16 v, eta16 m] at h

theorem perm' (m : Vector (BitVec 32) 16) (s : State) (hpc : s.pc = 0x20147)
    (hm : Msgs s m) (hal : (s.rax.setWidth 8 - 1 == 0) = false) :
    ∃ s', steps Code.prog 19 s = some s' ∧ s'.pc = 0x2006D ∧ Msgs s' (PERMUTE m) ∧
      (s'.x0 = s.x0 ∧ s'.x1 = s.x1 ∧ s'.x2 = s.x2 ∧ s'.x3 = s.x3) ∧ Same s s' ∧ s'.x14 = s.x14 ∧ s'.x15 = s.x15 ∧
      s'.rax.setWidth 8 = s.rax.setWidth 8 - 1 := by
  have h := perm m[0] m[1] m[2] m[3] m[4] m[5] m[6] m[7] m[8] m[9] m[10] m[11] m[12] m[13] m[14] m[15] s hpc (by rw [eta16]; exact hm) hal
  rwa [eta16 m] at h

theorem finish' (w : Vector (BitVec 32) 16) (ra : BitVec 64) (s : State) (hpc : s.pc = 0x20147)
    (hv : Rows s w) (hal : (s.rax.setWidth 8 - 1 == 0) = true)
    (o0 : Owned16 s.mem (s.rdi + 0)) (o1 : Owned16 s.mem (s.rdi + 16))
    (hret : s.mem.read s.rsp 64 = some ra) (hapart : ∀ x, (x - s.rsp).toNat < 8 → 32 ≤ (x - s.rdi).toNat) :
    ∃ s', steps Code.prog 7 s = some s' ∧ s'.pc = ra.toNat ∧ s'.rsp = s.rsp + 8 ∧
      s'.mem = (s.mem.put128 (s.rdi + 0) (mk4 (w[0] ^^^ w[8]) (w[1] ^^^ w[9]) (w[2] ^^^ w[10]) (w[3] ^^^ w[11]))).put128
        (s.rdi + 16) (mk4 (w[4] ^^^ w[12]) (w[5] ^^^ w[13]) (w[6] ^^^ w[14]) (w[7] ^^^ w[15])) ∧
      s'.rbx = s.rbx ∧ s'.rbp = s.rbp ∧ s'.r12 = s.r12 ∧ s'.r13 = s.r13 ∧ s'.r14 = s.r14 ∧ s'.r15 = s.r15 :=
  finish w[0] w[1] w[2] w[3] w[4] w[5] w[6] w[7] w[8] w[9] w[10] w[11] w[12] w[13] w[14] w[15] ra s hpc (by rw [eta16]; exact hv) hal o0 o1 hret hapart

/-- What holds at the loop's head: the rows, the message, the rounds left in AL, the two masks. -/
structure Head (s : State) (v m : Vector (BitVec 32) 16) (k : BitVec 8) : Prop where
  pc : s.pc = 0x2006D
  rows : Rows s v
  msgs : Msgs s m
  al : s.rax.setWidth 8 = k
  x14 : s.x14 = ROT8
  x15 : s.x15 = ROT16

/-- A round that is not the last, and the permutation after it: 65 instructions. -/
theorem iter (v m : Vector (BitVec 32) 16) (k : BitVec 8) (s : State) (h : Head s v m k) (hk : (k - 1 == 0) = false) :
    ∃ s', steps Code.prog 65 s = some s' ∧ Head s' (rnd v m) (PERMUTE m) (k - 1) ∧ Same s s' := by
  obtain ⟨s1, e1, pc1, r1, m1, S1, a14, a15, ax1⟩ := body' v m s h.pc h.rows h.msgs h.x14 h.x15
  obtain ⟨s2, e2, pc2, m2, ⟨q0, q1, q2, q3⟩, S2, b14, b15, ax2⟩ := perm' m s1 pc1 m1 (by rw [ax1, h.al]; exact hk)
  obtain ⟨c0, c1, c2, c3⟩ := r1
  refine ⟨s2, ?_, ⟨pc2, ⟨by rw [q0, c0], by rw [q1, c1], by rw [q2, c2], by rw [q3, c3]⟩, m2, by rw [ax2, ax1, h.al], by rw [b14, a14, h.x14], by rw [b15, a15, h.x15]⟩, S1.trans S2⟩
  rw [show 65 = 46 + 19 from rfl, steps_add, e1, Option.bind_some, e2]

/-- The last round and the return: 53 instructions. -/
theorem last (v m : Vector (BitVec 32) 16) (ra : BitVec 64) (s : State) (h : Head s v m 1)
    (o0 : Owned16 s.mem (s.rdi + 0)) (o1 : Owned16 s.mem (s.rdi + 16))
    (hret : s.mem.read s.rsp 64 = some ra) (hapart : ∀ x, (x - s.rsp).toNat < 8 → 32 ≤ (x - s.rdi).toNat) :
    ∃ s', steps Code.prog 53 s = some s' ∧ s'.pc = ra.toNat ∧ s'.rsp = s.rsp + 8 ∧
      s'.mem = (s.mem.put128 (s.rdi + 0) (mk4 ((rnd v m)[0] ^^^ (rnd v m)[8]) ((rnd v m)[1] ^^^ (rnd v m)[9])
        ((rnd v m)[2] ^^^ (rnd v m)[10]) ((rnd v m)[3] ^^^ (rnd v m)[11]))).put128 (s.rdi + 16)
        (mk4 ((rnd v m)[4] ^^^ (rnd v m)[12]) ((rnd v m)[5] ^^^ (rnd v m)[13]) ((rnd v m)[6] ^^^ (rnd v m)[14])
          ((rnd v m)[7] ^^^ (rnd v m)[15])) ∧
      s'.rbx = s.rbx ∧ s'.rbp = s.rbp ∧ s'.r12 = s.r12 ∧ s'.r13 = s.r13 ∧ s'.r14 = s.r14 ∧ s'.r15 = s.r15 := by
  obtain ⟨s1, e1, pc1, r1, m1, ⟨kbx, ksp, kbp, kdi, k12, k13, k14, k15, kmem⟩, _, _, ax1⟩ :=
    body' v m s h.pc h.rows h.msgs h.x14 h.x15
  obtain ⟨s2, e2, pc2, sp2, mem2, bx2, bp2, c12, c13, c14, c15⟩ := finish' (rnd v m) ra s1 pc1 r1 (by rw [ax1, h.al]; rfl)
    (by rw [kmem, kdi]; exact o0) (by rw [kmem, kdi]; exact o1) (by rw [kmem, ksp]; exact hret) (by rw [ksp, kdi]; exact hapart)
  refine ⟨s2, ?_, pc2, by rw [sp2, ksp], by rw [mem2, kmem, kdi], by rw [bx2, kbx], by rw [bp2, kbp], by rw [c12, k12],
    by rw [c13, k13], by rw [c14, k14], by rw [c15, k15]⟩
  rw [show 53 = 46 + 7 from rfl, steps_add, e1, Option.bind_some, e2]

set_option maxRecDepth 1000000 in
/-- **The contract of `blake3_servil_compress_in_place_sse41`.** Called with a chaining value at RDI, a block at RSI,
the block's length in RDX (its upper half clear), the counter in RCX and the flags in R8's low half, and a return address on the stack that is not in the
chaining value's 32 bytes: its 467 instructions run to that address with the stack pointer
popped, and memory is what it was but for the 32 bytes at RDI, which hold the first eight words
of the specification's `BLAKE3_COMPRESS` (sections 2.2 to 3.3 of C2SP's BLAKE3, `Generic.lean`,
at 32-bit words). RBX, RBP and R12 to R15 are as they were. -/
theorem contract (cv0 cv1 b0 b1 b2 b3 : V) (len : BitVec 32) (ra : BitVec 64) (s : State) (hpc : s.pc = 0x20000)
    (hc0 : Vec s.mem (s.rdi + 0) cv0) (hc1 : Vec s.mem (s.rdi + 16) cv1)
    (hb0 : Vec s.mem (s.rsi + 0) b0) (hb1 : Vec s.mem (s.rsi + 16) b1)
    (hb2 : Vec s.mem (s.rsi + 32) b2) (hb3 : Vec s.mem (s.rsi + 48) b3) (hlen : s.rdx = len.setWidth 64)
    (hret : s.mem.read s.rsp 64 = some ra) (hapart : ∀ x, (x - s.rsp).toNat < 8 → 32 ≤ (x - s.rdi).toNat) :
    ∃ s', steps Code.prog 467 s = some s' ∧ s'.pc = ra.toNat ∧ s'.rsp = s.rsp + 8 ∧
      s'.mem = (s.mem.put128 (s.rdi + 0) (mk4 (specCv (cvWords cv0 cv1) (blockWords b0 b1 b2 b3) s.rcx (len) (s.r8.setWidth 32))[0] (specCv (cvWords cv0 cv1) (blockWords b0 b1 b2 b3) s.rcx (len) (s.r8.setWidth 32))[1]
          (specCv (cvWords cv0 cv1) (blockWords b0 b1 b2 b3) s.rcx (len) (s.r8.setWidth 32))[2] (specCv (cvWords cv0 cv1) (blockWords b0 b1 b2 b3) s.rcx (len) (s.r8.setWidth 32))[3])).put128 (s.rdi + 16)
        (mk4 (specCv (cvWords cv0 cv1) (blockWords b0 b1 b2 b3) s.rcx (len) (s.r8.setWidth 32))[4] (specCv (cvWords cv0 cv1) (blockWords b0 b1 b2 b3) s.rcx (len) (s.r8.setWidth 32))[5]
          (specCv (cvWords cv0 cv1) (blockWords b0 b1 b2 b3) s.rcx (len) (s.r8.setWidth 32))[6] (specCv (cvWords cv0 cv1) (blockWords b0 b1 b2 b3) s.rcx (len) (s.r8.setWidth 32))[7]) ∧
      s'.rbx = s.rbx ∧ s'.rbp = s.rbp ∧ s'.r12 = s.r12 ∧ s'.r13 = s.r13 ∧ s'.r14 = s.r14 ∧ s'.r15 = s.r15 := by
  obtain ⟨s1, e1, pc1, r1, m1, x14, x15, al1, S1⟩ := start cv0 cv1 b0 b1 b2 b3 len s hpc hc0 hc1 hb0 hb1 hb2 hb3 hlen
  have H1 : Head s1 _ _ 7 := ⟨pc1, r1, m1, al1, x14, x15⟩
  obtain ⟨s2, e2, H2, S2⟩ := iter _ _ 7 s1 H1 (by decide)
  have H2 : Head s2 _ _ 6 := H2
  have S2 := S1.trans S2
  obtain ⟨s3, e3, H3, S3⟩ := iter _ _ 6 s2 H2 (by decide)
  have H3 : Head s3 _ _ 5 := H3
  have S3 := S2.trans S3
  obtain ⟨s4, e4, H4, S4⟩ := iter _ _ 5 s3 H3 (by decide)
  have H4 : Head s4 _ _ 4 := H4
  have S4 := S3.trans S4
  obtain ⟨s5, e5, H5, S5⟩ := iter _ _ 4 s4 H4 (by decide)
  have H5 : Head s5 _ _ 3 := H5
  have S5 := S4.trans S5
  obtain ⟨s6, e6, H6, S6⟩ := iter _ _ 3 s5 H5 (by decide)
  have H6 : Head s6 _ _ 2 := H6
  have S6 := S5.trans S6
  obtain ⟨s7, e7, H7, S7⟩ := iter _ _ 2 s6 H6 (by decide)
  have H7 : Head s7 _ _ 1 := H7
  have S7 := S6.trans S7
  obtain ⟨kbx, ksp, kbp, kdi, k12, k13, k14, k15, kmem⟩ := S7
  obtain ⟨s8, e8, pc8, sp8, mem8, bx8, bp8, c12, c13, c14, c15⟩ := last _ _ ra s7 H7
    (by rw [kmem, kdi]; exact vec_owned hc0) (by rw [kmem, kdi]; exact vec_owned hc1) (by rw [kmem, ksp]; exact hret)
    (by rw [ksp, kdi]; exact hapart)
  refine ⟨s8, ?_, pc8, by rw [sp8, ksp], ?_, by rw [bx8, kbx], by rw [bp8, kbp], by rw [c12, k12], by rw [c13, k13],
    by rw [c14, k14], by rw [c15, k15]⟩
  · rw [show 467 = 24 + (65 + (65 + (65 + (65 + (65 + (65 + 53)))))) from rfl, steps_add, e1, Option.bind_some, steps_add, e2, Option.bind_some, steps_add, e3, Option.bind_some, steps_add, e4, Option.bind_some, steps_add, e5, Option.bind_some, steps_add, e6, Option.bind_some, steps_add, e7, Option.bind_some, e8]
  · rw [mem8, kmem, kdi, spec_eq, low8_0, low8_1, low8_2, low8_3, low8_4, low8_5, low8_6, low8_7]
    rfl

end Sse
