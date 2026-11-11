import MergeLoop
open X86

namespace MergeCode

/-! # `CvStack::merge`, whole: the way in, the loop, the way out -/

/-- The 48 bytes `merge` pushes and the return address above them. -/
def inP (d : BitVec 64) : Bool := (d + 48#64).ult 56#64

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- **The way in.** From `merge`'s first instruction to its loop's head, when the stack is longer than
`target`: six registers are saved, the frame is made and aligned, and the platform and the flags (with
PARENT) are put in it. -/
theorem prologue (self p keyp rsp0 fp len target : BitVec 64) (flags plat : BitVec 8) (m : Mem)
    (rax rcx rbx rbp r8 r9 r12 r13 r14 r15 : BitVec 64) (zf cf : Option Bool) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : V)
    (hfp : ((rsp0 + 18446744073709551568#64) &&& 18446744073709551552#64) - 384#64 = fp)
    (hsp : 1024#64 ≤ rsp0) (hsp2 : rsp0 ≤ 18446744073709551600#64)
    (hlt : target < len)
    (hLen : Quad m (self + 0#64) len) (hKeyp : Quad m (p + 0#64) keyp)
    (hFlags : m (p + 40#64) = some flags) (hPlat : m (p + 41#64) = some plat)
    (hOwnP : ∀ d : BitVec 64, inP d = true → (m (rsp0 + d)).isSome = true)
    (hOwnF : ∀ d : BitVec 64, inF d = true → (m (fp + d)).isSome = true)
    -- the `CvStack`'s length and the kernels' structure are in neither the frame nor the pushed bytes
    (gLen : ∀ x : BitVec 64, (x - (self + 0#64)).toNat < 8 → inF (x - fp) = false ∧ inP (x - rsp0) = false)
    (gP : ∀ x : BitVec 64, (x - p).toNat < 42 → inF (x - fp) = false ∧ inP (x - rsp0) = false)
    (ra : BitVec 64) (hRa : m.read (rsp0 + 0#64) 64 = some ra) :
    ∃ s', steps Code.prog 24 ⟨rax, rcx, target, rbx, rsp0, rbp, p, self, r8, r9, r12, r13, r14, r15, zf, cf, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, m, 0x40000⟩ = some s' ∧ s'.pc = 0x40094 ∧
      s'.rax = len ∧ s'.rbx = self ∧ s'.rsp = fp ∧ s'.rbp = rsp0 + 18446744073709551608#64 ∧ s'.r12 = self + 9#64 ∧ s'.r14 = keyp ∧
      s'.r15 = len - target ∧
      s'.mem.read (rsp0 + 18446744073709551568#64) 64 = some rbx ∧
      s'.mem.read (rsp0 + 18446744073709551576#64) 64 = some r12 ∧
      s'.mem.read (rsp0 + 18446744073709551584#64) 64 = some r13 ∧
      s'.mem.read (rsp0 + 18446744073709551592#64) 64 = some r14 ∧
      s'.mem.read (rsp0 + 18446744073709551600#64) 64 = some r15 ∧
      s'.mem.read (rsp0 + 18446744073709551608#64) 64 = some rbp ∧
      s'.mem.read (rsp0 + 0#64) 64 = some ra ∧
      (∀ d : BitVec 64, inF d = true → (s'.mem (fp + d)).isSome = true) ∧
      s'.mem (fp + 58#64) = some plat ∧ s'.mem (fp + 59#64) = some (flags ||| 4#8) ∧ s'.mem (fp + 60#64) = some (flags ||| 4#8) ∧
      s'.mem (fp + 61#64) = some 0#8 ∧ s'.mem (fp + 62#64) = some 0#8 ∧ s'.mem (fp + 63#64) = some 0#8 ∧
      (∀ x : BitVec 64, inF (x - fp) = false → inP (x - rsp0) = false → s'.mem x = m x) := by
  let mm (fP fF : Written) : Mem := over (over m rsp0 inP fP) fp inF fF
  have hm : m = mm none' none' := by simp only [mm, over_none]
  have pNotF : ∀ d : BitVec 64, inP d = true → inF (rsp0 + d - fp) = false := by
    intro d hd; simp only [inP, inF] at hd ⊢; bv_decide
  have fNotP : ∀ d : BitVec 64, inF d = true → inP (fp + d - rsp0) = false := by
    intro d hd; simp only [inP, inF] at hd ⊢; bv_decide
  have wP : ∀ (fP fF : Written) (d : BitVec 64) (v : BitVec 8), inP d = true → (mm fP fF).put8 (rsp0 + d) v = mm (upd fP d v) fF := by
    intro fP fF d v hd; simp only [mm]; rw [put8_over_out _ _ _ _ _ _ (pNotF d hd), put8_over_in _ _ _ _ _ _ hd]
  have rP : ∀ (fP fF : Written) (d : BitVec 64), inP d = true → mm fP fF (rsp0 + d) = (fP d).or (m (rsp0 + d)) := by
    intro fP fF d hd; simp only [mm]; rw [over_out _ _ _ _ _ (pNotF d hd), over_in _ _ _ _ _ hd]
  have wF : ∀ (fP fF : Written) (d : BitVec 64) (v : BitVec 8), inF d = true → (mm fP fF).put8 (fp + d) v = mm fP (upd fF d v) := by
    intro fP fF d v hd; simp only [mm]; rw [put8_over_in _ _ _ _ _ _ hd]
  have rF : ∀ (fP fF : Written) (d : BitVec 64), inF d = true → mm fP fF (fp + d) = (fF d).or (m (fp + d)) := by
    intro fP fF d hd; simp only [mm]; rw [over_in _ _ _ _ _ hd, over_out _ _ _ _ _ (fNotP d hd)]
  have r_sub : ∀ c : BitVec 64, rsp0 - c = rsp0 + (-c) := by intro c; bv_decide
  have r_add : ∀ c d : BitVec 64, rsp0 + c + d = rsp0 + (c + d) := by intro c d; bv_decide
  have r_sub2 : ∀ c d : BitVec 64, rsp0 + c - d = rsp0 + (c - d) := by intro c d; bv_decide
  have fp_add : ∀ c d : BitVec 64, fp + c + d = fp + (c + d) := by intro c d; bv_decide
  have wrP64 : ∀ (fP fF : Written) (c v : BitVec 64), (mm fP fF).write (rsp0 + c) v 64 = (do
      let m ← (mm fP fF).write8 (rsp0 + c) (byte v 0); let m ← m.write8 (rsp0 + c + 1) (byte v 1)
      let m ← m.write8 (rsp0 + c + 2) (byte v 2); let m ← m.write8 (rsp0 + c + 3) (byte v 3)
      let m ← m.write8 (rsp0 + c + 4) (byte v 4); let m ← m.write8 (rsp0 + c + 5) (byte v 5)
      let m ← m.write8 (rsp0 + c + 6) (byte v 6); m.write8 (rsp0 + c + 7) (byte v 7)) := fun _ _ _ _ => rfl
  have rdP64 : ∀ (fP fF : Written) (c : BitVec 64), (mm fP fF).read (rsp0 + c) 64 = (do
      let b0 ← (mm fP fF).read8 (rsp0 + c); let b1 ← (mm fP fF).read8 (rsp0 + c + 1); let b2 ← (mm fP fF).read8 (rsp0 + c + 2); let b3 ← (mm fP fF).read8 (rsp0 + c + 3)
      let b4 ← (mm fP fF).read8 (rsp0 + c + 4); let b5 ← (mm fP fF).read8 (rsp0 + c + 5); let b6 ← (mm fP fF).read8 (rsp0 + c + 6); let b7 ← (mm fP fF).read8 (rsp0 + c + 7)
      pure (b0 ||| (b1 <<< 8) ||| (b2 <<< 16) ||| (b3 <<< 24) ||| (b4 <<< 32) ||| (b5 <<< 40) ||| (b6 <<< 48) ||| (b7 <<< 56))) := fun _ _ _ => rfl
  have wrF8 : ∀ (fP fF : Written) (c v : BitVec 64), (mm fP fF).write (fp + c) v 8 = (mm fP fF).write8 (fp + c) (byte v 0) := fun _ _ _ _ => rfl
  have wrF32 : ∀ (fP fF : Written) (c v : BitVec 64), (mm fP fF).write (fp + c) v 32 = (do
      let m ← (mm fP fF).write8 (fp + c) (byte v 0); let m ← m.write8 (fp + c + 1) (byte v 1)
      let m ← m.write8 (fp + c + 2) (byte v 2); m.write8 (fp + c + 3) (byte v 3)) := fun _ _ _ _ => rfl
  have rdLen : ∀ (fP fF : Written), (mm fP fF).read (self + 0#64) 64 = some len := by
    intro fP fF; simp only [mm]
    rw [over_read64 _ _ _ _ _ (fun x hx => (gLen x hx).1), over_read64 _ _ _ _ _ (fun x hx => (gLen x hx).2), read_quad hLen]
  have rdKeyp : ∀ (fP fF : Written), (mm fP fF).read (p + 0#64) 64 = some keyp := by
    intro fP fF; simp only [mm]
    rw [over_read64 _ _ _ _ _ (fun x hx => (gP x (by bv_omega)).1), over_read64 _ _ _ _ _ (fun x hx => (gP x (by bv_omega)).2), read_quad hKeyp]
  have rdFlags : ∀ (fP fF : Written), (mm fP fF).read (p + 40#64) 8 = some (flags.setWidth 64) := by
    intro fP fF; simp only [mm]
    rw [over_read8 _ _ _ _ _ (gP _ (by bv_omega)).1, over_read8 _ _ _ _ _ (gP _ (by bv_omega)).2]; simp [Mem.read, Mem.read8, hFlags]
  have rdPlat : ∀ (fP fF : Written), (mm fP fF).read (p + 41#64) 8 = some (plat.setWidth 64) := by
    intro fP fF; simp only [mm]
    rw [over_read8 _ _ _ _ _ (gP _ (by bv_omega)).1, over_read8 _ _ _ _ _ (gP _ (by bv_omega)).2]; simp [Mem.read, Mem.read8, hPlat]
  have hc : len.ult target = false := by bv_decide
  have hz : (len - target == 0#64) = false := by bv_decide
  rw [hm]
  run_merge [wP, rP, wF, rF, r_sub, r_sub2, r_add, fp_add, wrP64, wrF8, wrF32, rdLen, rdKeyp, rdFlags, rdPlat, hOwnP, hOwnF, hfp, hc, hz]
  have hRa' := hRa
  simp only [Mem.read, Mem.read8, r_add, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] at hRa'
  refine ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (intro x hx hp; simp only [mm, over_none]; rw [over_out _ _ _ _ _ hx, over_out _ _ _ _ _ hp]; done)
    | (intro d hd; simp (disch := assumption) only [rF, Option.isSome_or, hOwnF, Bool.or_true]; done)
    | (simp (config := {maxSteps := 10000000}) (disch := decide) only [rdP64, Mem.read8, r_add, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat, rP, rF,
        upd_apply, none_apply, BitVec.reduceEq, ↓reduceIte, Option.some_or, Option.none_or, unbyte64,
        Option.map_some, Option.bind_eq_bind, Option.bind_some, Option.pure_def]; done)
    | (simp (config := {maxSteps := 10000000}) (disch := decide) only [rdP64, Mem.read8, r_add, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat, rP,
        upd_apply, none_apply, BitVec.reduceEq, ↓reduceIte, Option.none_or]; exact hRa')
    | (simp (config := {maxSteps := 10000000}) (disch := decide) only [rF, upd_apply, none_apply, BitVec.reduceEq, ↓reduceIte, Option.some_or,
        Option.some.injEq, byte, Nat.reduceMul]; bv_decide)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- **The way out.** From the loop's exit: the stack pointer goes back to the saved registers, they are
restored, and `merge` returns. -/
theorem epilogue (rsp0 : BitVec 64) (b : Mem) (v0 v12 v13 v14 v15 vbp ra : BitVec 64)
    (rax rcx rdx rbx rsp rsi rdi r8 r9 r12 r13 r14 r15 : BitVec 64) (zf cf : Option Bool) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : V)
    (h48 : b.read (rsp0 + 18446744073709551568#64) 64 = some v0) (h40 : b.read (rsp0 + 18446744073709551576#64) 64 = some v12)
    (h32 : b.read (rsp0 + 18446744073709551584#64) 64 = some v13) (h24 : b.read (rsp0 + 18446744073709551592#64) 64 = some v14)
    (h16 : b.read (rsp0 + 18446744073709551600#64) 64 = some v15) (h8 : b.read (rsp0 + 18446744073709551608#64) 64 = some vbp)
    (hra : b.read (rsp0 + 0#64) 64 = some ra) :
    ∃ s', steps Code.prog 8 ⟨rax, rcx, rdx, rbx, rsp, rsp0 + 18446744073709551608#64, rsi, rdi, r8, r9, r12, r13, r14, r15, zf, cf, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, b, 0x401AB⟩ = some s' ∧
      s'.pc = ra.toNat ∧ s'.rsp = rsp0 + 8#64 ∧ s'.rbx = v0 ∧ s'.rbp = vbp ∧ s'.r12 = v12 ∧ s'.r13 = v13 ∧ s'.r14 = v14 ∧
      s'.r15 = v15 ∧ s'.mem = b := by
  have r_add : ∀ c d : BitVec 64, rsp0 + c + d = rsp0 + (c + d) := by intro c d; bv_decide
  run_merge [r_add, h48, h40, h32, h24, h16, h8, hra]
  exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- **The compiled `CvStack::merge` runs `mergeN`.** Called with the `CvStack` at RDI (its tag `Some`, its
length `len ≤ 55`, its values `es`, top first, in its array), the kernels' structure at RSI (the key's
address, the flags, the platform) and `target` in RDX, `1 ≤ target < len`; with its stack owned (56 bytes
at the stack pointer, and the aligned frame of 392 below) and apart from the `CvStack`, the key and that
structure: it returns to its caller with the stack pointer popped and RBX, RBP and R12 to R15 as they were;
the length is `target`; the array holds `mergeN (len - target) es`, each merge the parent chaining value
by a one-block kernel (AVX-512 when the platform byte is 5, else SSE4.1); the tag stays; and no byte
outside `merge`'s stack, the array and the length is changed. None of its three panic sites is reached. -/
theorem merge_is_mergeN (self p keyp rsp0 fp len target : BitVec 64) (k0 k1 : V) (flags plat : BitVec 8) (es : List (V × V)) (m : Mem)
    (rax rcx rbx rbp r8 r9 r12 r13 r14 r15 ra : BitVec 64) (zf cf : Option Bool) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : V)
    (hfp : ((rsp0 + 18446744073709551568#64) &&& 18446744073709551552#64) - 384#64 = fp) (hsp : 1024#64 ≤ rsp0) (hsp2 : rsp0 ≤ 18446744073709551600#64)
    (hlt : target < len) (h1 : 1#64 ≤ target) (hlen : len.toNat = es.length) (hmax : es.length ≤ 55)
    (hTag : m (self + 8#64) = some 1#8) (hLen : Quad m (self + 0#64) len)
    (hE : Entries m (self + 9#64 + (len + 18446744073709551615#64) <<< 5) es)
    (hKeyp : Quad m (p + 0#64) keyp) (hFlags : m (p + 40#64) = some flags) (hPlat : m (p + 41#64) = some plat)
    (hK0 : Vec m (keyp + 0#64) k0) (hK1 : Vec m (keyp + 16#64) k1)
    (hRa : m.read (rsp0 + 0#64) 64 = some ra)
    (hOwnP : ∀ d : BitVec 64, inP d = true → (m (rsp0 + d)).isSome = true)
    (hOwnF : ∀ d : BitVec 64, inF d = true → (m (fp + d)).isSome = true)
    (gSelf : ∀ x : BitVec 64, (x - self).toNat < 9 → inF (x - fp) = false ∧ inP (x - rsp0) = false)
    (gArr : ∀ x : BitVec 64, (x - (self + 9#64)).toNat < 1760 → inF (x - fp) = false ∧ inP (x - rsp0) = false)
    (gKey : ∀ x : BitVec 64, (x - keyp).toNat < 32 → inF (x - fp) = false ∧ inP (x - rsp0) = false)
    (gP : ∀ x : BitVec 64, (x - p).toNat < 42 → inF (x - fp) = false ∧ inP (x - rsp0) = false)
    (gKeyArr : ∀ x : BitVec 64, (x - keyp).toNat < 32 → 1760 ≤ (x - (self + 9#64)).toNat)
    (gKeySelf : ∀ x : BitVec 64, (x - keyp).toNat < 32 → 9 ≤ (x - self).toNat)
    (hW : self ≤ 18446744073709549846#64) :
    ∃ K s', steps Code.prog K ⟨rax, rcx, target, rbx, rsp0, rbp, p, self, r8, r9, r12, r13, r14, r15, zf, cf, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, m, 0x40000⟩ = some s' ∧
      s'.pc = ra.toNat ∧ s'.rsp = rsp0 + 8#64 ∧ s'.rbx = rbx ∧ s'.rbp = rbp ∧ s'.r12 = r12 ∧ s'.r13 = r13 ∧ s'.r14 = r14 ∧
      s'.r15 = r15 ∧
      Quad s'.mem (self + 0#64) target ∧
      Entries s'.mem (self + 9#64 + (target + 18446744073709551615#64) <<< 5) (mergeN k0 k1 (flags ||| 4#8) (len - target).toNat es) ∧
      s'.mem (self + 8#64) = some 1#8 ∧
      (∀ x : BitVec 64, inF (x - fp) = false → inP (x - rsp0) = false → 1760 ≤ (x - (self + 9#64)).toNat → 9 ≤ (x - self).toNat →
        s'.mem x = m x) := by
  have hfpA : fp &&& 63#64 = 0#64 := by rw [← hfp]; bv_decide
  have pNotF : ∀ x : BitVec 64, inP (x - rsp0) = true → inF (x - fp) = false := by
    intro x hx; simp only [inP, inF] at hx ⊢; bv_decide
  -- the way in
  obtain ⟨s1, e1, pc1, ax1, bx1, sp1, bp1, c12, c14, c15, s48, s40, s32, s24, s16, s8, sra, own1, f58, f59, f60, f61, f62, f63, out1⟩ :=
    prologue self p keyp rsp0 fp len target flags plat m rax rcx rbx rbp r8 r9 r12 r13 r14 r15 zf cf x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15
      hfp hsp hsp2 hlt hLen hKeyp hFlags hPlat hOwnP hOwnF (fun x hx => gSelf x (by bv_omega)) gP ra hRa
  -- what holds at the loop's head
  have P : Places self (self + 9#64) keyp fp := ⟨rfl, hfpA, hW, fun x hx => (gArr x hx).1, fun x hx => (gKey x hx).1,
    fun x hx => (gSelf x hx).1, gKeyArr, gKeySelf⟩
  have H1 : Head self (self + 9#64) keyp fp k0 k1 (flags ||| 4#8) plat s1.mem len es := by
    refine ⟨?_, ?_, ?_, ?_, ?_, own1, f58, f59, f60, f61, f62, f63⟩
    · rw [out1 _ (gSelf _ (by bv_omega)).1 (gSelf _ (by bv_omega)).2]; exact hTag
    · exact quad_congr (fun x hx => out1 x (gSelf x (by bv_omega)).1 (gSelf x (by bv_omega)).2) hLen
    · refine entries_congr es _ (fun x hx => ?_) hE
      have hx' : (x - (self + 9#64)).toNat < 1760 := by rw [shl5] at hx; bv_omega
      exact out1 x (gArr x hx').1 (gArr x hx').2
    · exact vec_congr (fun x hx => out1 x (gKey x (by bv_omega)).1 (gKey x (by bv_omega)).2) hK0
    · exact vec_congr (fun x hx => out1 x (gKey x (by bv_omega)).1 (gKey x (by bv_omega)).2) hK1
  obtain ⟨a1, b1, d1, bx1v, sp1v, bp1v, si1, di1, r81, r91, r121, r131, r141, r151, zf1, cf1, y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, m1, pcv⟩ := s1
  simp only at pc1 ax1 bx1 sp1 bp1 c12 c14 c15 s48 s40 s32 s24 s16 s8 sra own1 out1 H1
  subst pcv a1 bx1v sp1v bp1v r121 r141 r151
  -- the loop
  obtain ⟨K2, s2, e2, pc2, bx2, sp2, bp2, d12, d14, q2, E2, tag2, out2⟩ :=
    loop self (self + 9#64) keyp fp k0 k1 (flags ||| 4#8) plat P (len - target).toNat es len (len - target) m1
      b1 d1 (rsp0 + 18446744073709551608#64) si1 di1 r81 r91 r131 zf1 cf1 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15
      (by bv_omega) (by bv_omega) hlen hmax rfl H1
  -- the way out: the saved registers and the return address are where they were put
  have keep : ∀ x : BitVec 64, inP (x - rsp0) = true → s2.mem x = m1 x := by
    intro x hx
    refine out2 x (pNotF x hx) (Nat.le_of_not_lt (fun h => ?_)) (Nat.le_of_not_lt (fun h => ?_))
    · have := (gArr x h).2; rw [hx] at this; exact absurd this (by decide)
    · have := (gSelf x h).2; rw [hx] at this; exact absurd this (by decide)
  have rd : ∀ (c v : BitVec 64), (c + 48#64).ult 49#64 = true → m1.read (rsp0 + c) 64 = some v → s2.mem.read (rsp0 + c) 64 = some v := by
    intro c v hc hv
    rw [read_congr (m := m1) _ (fun x hx => keep x (by
      have h8 : x - (rsp0 + c) < 8#64 := BitVec.lt_def.mpr (by simpa using hx)
      simp only [inP]; bv_decide))]
    exact hv
  obtain ⟨s3, e3, pc3, sp3, bx3, bp3, f12, f13, f14, f15, mem3⟩ :=
    epilogue rsp0 s2.mem rbx r12 r13 r14 r15 rbp ra s2.rax s2.rcx s2.rdx s2.rbx s2.rsp s2.rsi s2.rdi s2.r8 s2.r9 s2.r12 s2.r13 s2.r14 s2.r15
      s2.zf s2.cf s2.x0 s2.x1 s2.x2 s2.x3 s2.x4 s2.x5 s2.x6 s2.x7 s2.x8 s2.x9 s2.x10 s2.x11 s2.x12 s2.x13 s2.x14 s2.x15
      (rd _ _ (by decide) s48) (rd _ _ (by decide) s40) (rd _ _ (by decide) s32) (rd _ _ (by decide) s24) (rd _ _ (by decide) s16)
      (rd _ _ (by decide) s8) (rd _ _ (by decide) sra)
  have es2 : s2 = ⟨s2.rax, s2.rcx, s2.rdx, s2.rbx, s2.rsp, rsp0 + 18446744073709551608#64, s2.rsi, s2.rdi, s2.r8, s2.r9, s2.r12, s2.r13, s2.r14, s2.r15,
      s2.zf, s2.cf, s2.x0, s2.x1, s2.x2, s2.x3, s2.x4, s2.x5, s2.x6, s2.x7, s2.x8, s2.x9, s2.x10, s2.x11, s2.x12, s2.x13, s2.x14, s2.x15,
      s2.mem, 0x401AB⟩ := by
    cases s2; simp only at pc2 bp2; subst pc2 bp2; rfl
  rw [← es2] at e3
  have eT : len - (len - target) = target := by bv_decide
  refine ⟨24 + (K2 + 8), s3, by rw [steps_add, e1, Option.bind_some, steps_add, e2, Option.bind_some, e3], pc3, sp3, bx3, bp3,
    f12, f13, f14, f15, ?_, ?_, ?_, ?_⟩
  · rw [mem3, ← eT]; exact q2
  · rw [mem3]; rw [eT] at E2; exact E2
  · rw [mem3]; exact tag2
  · intro x hF hP hA hS
    rw [mem3, out2 x hF hA hS, out1 x hF hP]

#print axioms merge_is_mergeN

end MergeCode
