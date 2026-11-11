import MergeTrace
open X86

namespace MergeCode

/-! `merge`'s loop and the whole function, with the observer. Written by allgen.py. -/

/-- The instructions of one turn, by the platform's kernel. -/
def turnK (plat : BitVec 8) : Nat := if plat = 5#8 then 52 + (362 + 12) else 52 + (467 + 13)

/-- What one turn shows. -/
noncomputable def turnShows (plat : BitVec 8) (self arr keyp fp len : BitVec 64) (last : Bool) : List Obs :=
  if plat = 5#8 then turn_avx_shows self arr keyp fp len last else turn_sse_shows self arr keyp fp len last

set_option maxRecDepth 1000000 in
theorem turnL (self arr keyp fp len nB : BitVec 64) (l0 l1 r0 r1 k0 k1 : V) (fl plat : BitVec 8) (m : Mem)
    (rcx rdx rbp rsi rdi r8 r9 r13 : BitVec 64) (zf cf : Option Bool) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : V)
    (hlo : 2#64 ≤ len) (hhi : len ≤ 55#64) (hfp : fp &&& 63#64 = 0#64)
    (hTag : m (self + 8#64) = some 1#8) (hLen : Quad m (self + 0#64) len)
    (hL0 : Vec m (arr + ((len + 18446744073709551614#64) <<< 5) + 0#64) l0) (hL1 : Vec m (arr + ((len + 18446744073709551614#64) <<< 5) + 16#64) l1)
    (hR0 : Vec m (arr + ((len + 18446744073709551615#64) <<< 5) + 0#64) r0) (hR1 : Vec m (arr + ((len + 18446744073709551615#64) <<< 5) + 16#64) r1)
    (hK0 : Vec m (keyp + 0#64) k0) (hK1 : Vec m (keyp + 16#64) k1)
    (hOwn : ∀ d : BitVec 64, inF d = true → (m (fp + d)).isSome = true)
    (hPlat : m (fp + 58#64) = some plat) (hFl : m (fp + 59#64) = some fl)
    (hF0 : m (fp + 60#64) = some fl) (hF1 : m (fp + 61#64) = some 0#8) (hF2 : m (fp + 62#64) = some 0#8) (hF3 : m (fp + 63#64) = some 0#8)
    (oSlot : ∀ x : BitVec 64, (x - (arr + ((len + 18446744073709551614#64) <<< 5))).toNat < 64 → inF (x - fp) = false)
    (oKey : ∀ x : BitVec 64, (x - keyp).toNat < 32 → inF (x - fp) = false)
    (oSelf : ∀ x : BitVec 64, (x - self).toNat < 9 → inF (x - fp) = false)
    (hLS : ∀ x : BitVec 64, (x - self).toNat < 8 → 32 ≤ (x - (arr + ((len + 18446744073709551614#64) <<< 5))).toNat) :
    ∃ S, stepsL Code.prog (turnK plat) ⟨⟨len, rcx, rdx, self, fp, rbp, rsi, rdi, r8, r9, arr, r13, keyp, nB, zf, cf, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, m, 0x40094⟩, []⟩ = some S ∧
      S.leak = turnShows plat self arr keyp fp len (decide (nB - 1#64 = 0#64)) ∧
      S.core.pc = (if nB - 1#64 = 0#64 then 0x401AB else 0x40094) ∧ S.core.rax = len - 1#64 ∧ S.core.r15 = nB - 1#64 ∧
      S.core.rbx = self ∧ S.core.rsp = fp ∧ S.core.rbp = rbp ∧ S.core.r12 = arr ∧ S.core.r14 = keyp ∧
      Vec S.core.mem (arr + ((len + 18446744073709551614#64) <<< 5) + 0#64) (merged k0 k1 l0 l1 r0 r1 fl).1 ∧
      Vec S.core.mem (arr + ((len + 18446744073709551614#64) <<< 5) + 16#64) (merged k0 k1 l0 l1 r0 r1 fl).2 ∧
      Quad S.core.mem (self + 0#64) (len - 1#64) ∧
      (∀ d : BitVec 64, inF d = true → (S.core.mem (fp + d)).isSome = true) ∧
      S.core.mem (fp + 58#64) = some plat ∧ S.core.mem (fp + 59#64) = some fl ∧ S.core.mem (fp + 60#64) = some fl ∧
      S.core.mem (fp + 61#64) = some 0#8 ∧ S.core.mem (fp + 62#64) = some 0#8 ∧ S.core.mem (fp + 63#64) = some 0#8 ∧
      (∀ x : BitVec 64, inF (x - fp) = false → 32 ≤ (x - (arr + ((len + 18446744073709551614#64) <<< 5))).toNat → 8 ≤ (x - self).toNat → S.core.mem x = m x) := by
  by_cases h : plat = 5#8
  · subst h
    simp only [turnK, turnShows, ↓reduceIte]
    exact both (turn_avx self arr keyp fp len nB l0 l1 r0 r1 k0 k1 fl m rcx rdx rbp rsi rdi r8 r9 r13 zf cf x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15
        hlo hhi hfp hTag hLen hL0 hL1 hR0 hR1 hK0 hK1 hOwn hPlat hFl hF0 hF1 hF2 hF3 oSlot oKey oSelf hLS)
      (turn_avx_leak self arr keyp fp len nB l0 l1 r0 r1 k0 k1 fl m rcx rdx rbp rsi rdi r8 r9 r13 zf cf x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15
        hlo hhi hfp hTag hLen hL0 hL1 hR0 hR1 hK0 hK1 hOwn hPlat hFl hF0 hF1 hF2 hF3 oSlot oKey oSelf hLS)
  · simp only [turnK, turnShows, h, ↓reduceIte]
    exact both (turn_sse self arr keyp fp len nB l0 l1 r0 r1 k0 k1 fl m rcx rdx rbp rsi rdi r8 r9 r13 zf cf x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15
        hlo hhi hfp hTag hLen hL0 hL1 hR0 hR1 hK0 hK1 hOwn plat h hPlat hFl hF0 hF1 hF2 hF3 oSlot oKey oSelf hLS)
      (turn_sse_leak self arr keyp fp len nB l0 l1 r0 r1 k0 k1 fl m rcx rdx rbp rsi rdi r8 r9 r13 zf cf x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15
        hlo hhi hfp hTag hLen hL0 hL1 hR0 hR1 hK0 hK1 hOwn plat h hPlat hFl hF0 hF1 hF2 hF3 oSlot oKey oSelf hLS)

/-- What `n` turns show, the newest on top: a function of where things are, the platform, the length and
the turns to go. No value of the stack, no byte of the key or the flags is among its arguments. -/
noncomputable def loopShows (plat : BitVec 8) (self arr keyp fp : BitVec 64) : Nat → BitVec 64 → BitVec 64 → List Obs
  | 0, _, _ => []
  | k + 1, len, nB => loopShows plat self arr keyp fp k (len - 1#64) (nB - 1#64) ++
      turnShows plat self arr keyp fp len (decide (nB - 1#64 = 0#64))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem loopL (self arr keyp fp : BitVec 64) (k0 k1 : V) (fl plat : BitVec 8) (P : Places self arr keyp fp) :
    ∀ (n : Nat) (es : List (V × V)) (len nB : BitVec 64) (m : Mem) (rcx rdx rbp rsi rdi r8 r9 r13 : BitVec 64) (zf cf : Option Bool) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : V),
      1 ≤ n → n + 1 ≤ es.length → len.toNat = es.length → es.length ≤ 55 → nB.toNat = n →
      Head self arr keyp fp k0 k1 fl plat m len es →
      ∃ S, stepsL Code.prog (n * turnK plat) ⟨⟨len, rcx, rdx, self, fp, rbp, rsi, rdi, r8, r9, arr, r13, keyp, nB, zf, cf, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, m, 0x40094⟩, []⟩ = some S ∧
        S.leak = loopShows plat self arr keyp fp n len nB ∧
        S.core.pc = 0x401AB ∧ S.core.rbx = self ∧ S.core.rsp = fp ∧ S.core.rbp = rbp ∧ S.core.r12 = arr ∧ S.core.r14 = keyp ∧
        Quad S.core.mem (self + 0#64) (len - nB) ∧
        Entries S.core.mem (arr + (len - nB + 18446744073709551615#64) <<< 5) (mergeN k0 k1 fl n es) ∧
        S.core.mem (self + 8#64) = some 1#8 ∧
        (∀ x : BitVec 64, inF (x - fp) = false → 1760 ≤ (x - arr).toNat → 9 ≤ (x - self).toNat → S.core.mem x = m x) := by
  obtain ⟨harr, hfp, hW, gArr, gKey, gSelf, gKeyArr, gKeySelf⟩ := P
  intro n
  induction n with
  | zero => intro es len nB m rcx rdx rbp rsi rdi r8 r9 r13 zf cf x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 h1; omega
  | succ k ih =>
    intro es len nB m rcx rdx rbp rsi rdi r8 r9 r13 zf cf x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 _ hlen2 hlen hmax hnB hH
    obtain ⟨hTag, hLen, hE, hK0, hK1, hOwn, hPlat, hFl, hF0, hF1, hF2, hF3⟩ := hH
    rcases es with _ | ⟨r, _ | ⟨l, rest⟩⟩
    · simp at hlen2
    · simp at hlen2
    simp only [List.length_cons] at hlen2 hlen hmax
    obtain ⟨hR0, hR1, hL0, hL1, hRest⟩ := hE
    have hlo : 2#64 ≤ len := by bv_omega
    have hhi : len ≤ 55#64 := by bv_omega
    have eOL : arr + ((len + 18446744073709551615#64) <<< 5) - 32#64 = arr + ((len + 18446744073709551614#64) <<< 5) := by bv_decide
    rw [eOL] at hL0 hL1 hRest
    have oSlot : ∀ x : BitVec 64, (x - (arr + ((len + 18446744073709551614#64) <<< 5))).toNat < 64 → inF (x - fp) = false := fun x hx =>
      gArr x (by rw [shl5] at hx; bv_omega)
    have hLS : ∀ x : BitVec 64, (x - self).toNat < 8 → 32 ≤ (x - (arr + ((len + 18446744073709551614#64) <<< 5))).toNat := fun x hx => by
      rw [harr, shl5]; bv_omega
    obtain ⟨⟨s1, lk1⟩, e1, hl1, pc1, ax1, r151, bx1, sp1, bp1, c12, c14, vM0, vM1, qLen1, own1, f58, f59, f60, f61, f62, f63, out1⟩ :=
      turnL self arr keyp fp len nB l.1 l.2 r.1 r.2 k0 k1 fl plat m rcx rdx rbp rsi rdi r8 r9 r13 zf cf x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15
        hlo hhi hfp hTag hLen hL0 hL1 hR0 hR1 hK0 hK1 hOwn hPlat hFl hF0 hF1 hF2 hF3 oSlot gKey gSelf hLS
    simp only at hl1 pc1 ax1 r151 bx1 sp1 bp1 c12 c14 vM0 vM1 qLen1 own1 f58 f59 f60 f61 f62 f63 out1
    subst lk1
    have tag1 : s1.mem (self + 8#64) = some 1#8 := by
      rw [out1 _ (gSelf _ (by bv_omega)) (by rw [harr, shl5]; bv_omega) (by bv_omega)]; exact hTag
    have rest1 : Entries s1.mem (arr + ((len + 18446744073709551614#64) <<< 5) - 32#64) rest :=
      entries_congr rest _ (fun x hx => out1 x (gArr x (by rw [shl5] at hx; bv_omega))
        (by rw [shl5] at hx ⊢; bv_omega) (by rw [shl5, harr] at hx; bv_omega)) hRest
    have key0 : Vec s1.mem (keyp + 0#64) k0 := vec_congr (fun x hx => out1 x (gKey x (by bv_omega))
      (by have := gKeyArr x (by bv_omega); rw [shl5]; bv_omega) (by have := gKeySelf x (by bv_omega); omega)) hK0
    have key1 : Vec s1.mem (keyp + 16#64) k1 := vec_congr (fun x hx => out1 x (gKey x (by bv_omega))
      (by have := gKeyArr x (by bv_omega); rw [shl5]; bv_omega) (by have := gKeySelf x (by bv_omega); omega)) hK1
    have eTop : arr + (len - 1#64 + 18446744073709551615#64) <<< 5 = arr + ((len + 18446744073709551614#64) <<< 5) := by bv_decide
    by_cases hk : k = 0
    · subst hk
      have hnB1 : nB = 1#64 := by bv_omega
      rw [Nat.zero_add, Nat.one_mul]
      refine ⟨⟨s1, _⟩, e1, ?_, ?_, bx1, sp1, bp1, c12, c14, ?_, ?_, tag1, ?_⟩
      · simp only [loopShows, List.nil_append]
      · show s1.pc = 0x401AB; rw [pc1, hnB1]; rfl
      · show Quad s1.mem _ _; rw [hnB1]; exact qLen1
      · show Entries s1.mem _ _; rw [hnB1, eTop]; exact ⟨vM0, vM1, rest1⟩
      · intro x hx ha hs; exact out1 x hx (by rw [shl5]; bv_omega) (by omega)
    · have hne : nB - 1#64 ≠ 0#64 := by bv_omega
      have pc1' : s1.pc = 0x40094 := by rw [pc1, if_neg hne]
      obtain ⟨rax1, rcx1, rdx1, rbx1, rsp1, rbp1, rsi1, rdi1, r81, r91, r121, r131, r141, r151v, zf1, cf1, y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, m1, pcv⟩ := s1
      simp only at pc1' ax1 r151 bx1 sp1 bp1 c12 c14 vM0 vM1 qLen1 own1 f58 f59 f60 f61 f62 f63 out1 tag1 rest1 key0 key1
      subst pcv rax1 r151v rbx1 rsp1 rbp1 r121 r141
      have H1 : Head self arr keyp fp k0 k1 fl plat m1 (len - 1#64) (merged k0 k1 l.1 l.2 r.1 r.2 fl :: rest) :=
        ⟨tag1, qLen1, ⟨by rw [eTop]; exact vM0, by rw [eTop]; exact vM1, by rw [eTop]; exact rest1⟩, key0, key1, own1,
          f58, f59, f60, f61, f62, f63⟩
      obtain ⟨S2, e2, hl2, pc2, bx2, sp2, bp2, d12, d14, q2, E2, tag2, out2⟩ :=
        ih (merged k0 k1 l.1 l.2 r.1 r.2 fl :: rest) (len - 1#64) (nB - 1#64) m1 rcx1 rdx1 rbp rsi1 rdi1 r81 r91 r131 zf1 cf1 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15
          (by omega) (by simp only [List.length_cons]; omega) (by simp only [List.length_cons]; bv_omega)
          (by simp only [List.length_cons]; omega) (by bv_omega) H1
      have eD : len - nB = len - 1#64 - (nB - 1#64) := by bv_decide
      have hC := stepsL_chain Code.prog (turnK plat) (k * turnK plat) _ _ _ S2 e1 e2
      rw [show (k + 1) * turnK plat = turnK plat + k * turnK plat by rw [Nat.succ_mul, Nat.add_comm]]
      refine ⟨⟨S2.core, _⟩, hC, ?_, pc2, bx2, sp2, bp2, d12, d14, ?_, ?_, tag2, ?_⟩
      · simp only [loopShows, hl2]
      · show Quad S2.core.mem _ _; rw [eD]; exact q2
      · show Entries S2.core.mem _ _; rw [eD]; exact E2
      · intro x hx ha hs
        show S2.core.mem x = m x
        rw [out2 x hx ha hs]; exact out1 x hx (by rw [shl5]; bv_omega) (by omega)

/-- **What a whole call of `merge` shows**: a function of where its arguments, its stack and its caller
are, of the platform byte, and of the stack's length and the target. The stack's values, the key and the
flags are not among its arguments. -/
noncomputable def mergeShows (plat : BitVec 8) (self p keyp rsp0 fp ra len target : BitVec 64) : List Obs :=
  epilogue_shows rsp0 ra ++
    (loopShows plat self (self + 9#64) keyp fp (len - target).toNat len (len - target) ++ prologue_shows self p rsp0 fp)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- **`CvStack::merge`, as compiled: its result, its memory and what it shows, in one statement.** With
`merge_is_mergeN`'s hypotheses, the recorded run of the whole function (the kernels' instructions
included) ends with `merge_is_mergeN`'s result, and its trace is `mergeShows`. -/
theorem merge_whole (self p keyp rsp0 fp len target : BitVec 64) (k0 k1 : V) (flags plat : BitVec 8) (es : List (V × V)) (m : Mem)
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
    ∃ S, stepsL Code.prog (24 + ((len - target).toNat * turnK plat + 8)) ⟨⟨rax, rcx, target, rbx, rsp0, rbp, p, self, r8, r9, r12, r13, r14, r15, zf, cf, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, m, 0x40000⟩, []⟩ = some S ∧
      S.leak = mergeShows plat self p keyp rsp0 fp ra len target ∧
      S.core.pc = ra.toNat ∧ S.core.rsp = rsp0 + 8#64 ∧ S.core.rbx = rbx ∧ S.core.rbp = rbp ∧ S.core.r12 = r12 ∧ S.core.r13 = r13 ∧ S.core.r14 = r14 ∧
      S.core.r15 = r15 ∧
      Quad S.core.mem (self + 0#64) target ∧
      Entries S.core.mem (self + 9#64 + (target + 18446744073709551615#64) <<< 5) (mergeN k0 k1 (flags ||| 4#8) (len - target).toNat es) ∧
      S.core.mem (self + 8#64) = some 1#8 ∧
      (∀ x : BitVec 64, inF (x - fp) = false → inP (x - rsp0) = false → 1760 ≤ (x - (self + 9#64)).toNat → 9 ≤ (x - self).toNat →
        S.core.mem x = m x) := by
  have hfpA : fp &&& 63#64 = 0#64 := by rw [← hfp]; bv_decide
  have pNotF : ∀ x : BitVec 64, inP (x - rsp0) = true → inF (x - fp) = false := by
    intro x hx; simp only [inP, inF] at hx ⊢; bv_decide
  obtain ⟨⟨s1, lk1⟩, e1, hl1, pc1, ax1, bx1, sp1, bp1, c12, c14, c15, s48, s40, s32, s24, s16, s8, sra, own1, f58, f59, f60, f61, f62, f63, out1⟩ :=
    both (prologue self p keyp rsp0 fp len target flags plat m rax rcx rbx rbp r8 r9 r12 r13 r14 r15 zf cf x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15
        hfp hsp hsp2 hlt hLen hKeyp hFlags hPlat hOwnP hOwnF (fun x hx => gSelf x (by bv_omega)) gP ra hRa)
      (prologue_leak self p keyp rsp0 fp len target flags plat m rax rcx rbx rbp r8 r9 r12 r13 r14 r15 zf cf x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15
        hfp hsp hsp2 hlt hLen hKeyp hFlags hPlat hOwnP hOwnF (fun x hx => gSelf x (by bv_omega)) gP ra hRa)
  simp only at hl1 pc1 ax1 bx1 sp1 bp1 c12 c14 c15 s48 s40 s32 s24 s16 s8 sra own1 f58 f59 f60 f61 f62 f63 out1
  subst lk1
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
  obtain ⟨⟨s2, lk2⟩, e2, hl2, pc2, bx2, sp2, bp2, d12, d14, q2, E2, tag2, out2⟩ :=
    loopL self (self + 9#64) keyp fp k0 k1 (flags ||| 4#8) plat P (len - target).toNat es len (len - target) m1
      b1 d1 (rsp0 + 18446744073709551608#64) si1 di1 r81 r91 r131 zf1 cf1 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15
      (by bv_omega) (by bv_omega) hlen hmax rfl H1
  simp only at hl2 pc2 bx2 sp2 bp2 d12 d14 q2 E2 tag2 out2
  subst lk2
  obtain ⟨a2, b2, d2, bx2v, sp2v, bp2v, si2, di2, r82, r92, r122, r132, r142, r152, zf2, cf2,
    z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15, m2, pc2v⟩ := s2
  simp only at pc2 bx2 sp2 bp2 d12 d14 q2 E2 tag2 out2
  subst pc2v bp2v
  have keep : ∀ x : BitVec 64, inP (x - rsp0) = true → m2 x = m1 x := by
    intro x hx
    refine out2 x (pNotF x hx) (Nat.le_of_not_lt (fun h => ?_)) (Nat.le_of_not_lt (fun h => ?_))
    · have := (gArr x h).2; rw [hx] at this; exact absurd this (by decide)
    · have := (gSelf x h).2; rw [hx] at this; exact absurd this (by decide)
  have rd : ∀ (c v : BitVec 64), (c + 48#64).ult 49#64 = true → m1.read (rsp0 + c) 64 = some v → m2.read (rsp0 + c) 64 = some v := by
    intro c v hc hv
    rw [read_congr (m := m1) _ (fun x hx => keep x (by
      have h8 : x - (rsp0 + c) < 8#64 := BitVec.lt_def.mpr (by simpa using hx)
      simp only [inP]; bv_decide))]
    exact hv
  obtain ⟨⟨s3, lk3⟩, e3, hl3, pc3, sp3, bx3, bp3, f12, f13, f14, f15, mem3⟩ :=
    both (epilogue rsp0 m2 rbx r12 r13 r14 r15 rbp ra a2 b2 d2 bx2v sp2v si2 di2 r82 r92 r122 r132 r142 r152 zf2 cf2
        z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15
        (rd _ _ (by decide) s48) (rd _ _ (by decide) s40) (rd _ _ (by decide) s32) (rd _ _ (by decide) s24) (rd _ _ (by decide) s16)
        (rd _ _ (by decide) s8) (rd _ _ (by decide) sra))
      (epilogue_leak rsp0 m2 rbx r12 r13 r14 r15 rbp ra a2 b2 d2 bx2v sp2v si2 di2 r82 r92 r122 r132 r142 r152 zf2 cf2
        z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15
        (rd _ _ (by decide) s48) (rd _ _ (by decide) s40) (rd _ _ (by decide) s32) (rd _ _ (by decide) s24) (rd _ _ (by decide) s16)
        (rd _ _ (by decide) s8) (rd _ _ (by decide) sra))
  simp only at hl3 pc3 sp3 bx3 bp3 f12 f13 f14 f15 mem3
  subst lk3
  have hBC := stepsL_chain Code.prog ((len - target).toNat * turnK plat) 8 _ _ _ _ e2 e3
  have hABC := stepsL_chain Code.prog 24 ((len - target).toNat * turnK plat + 8) _ _ _ _ e1 hBC
  have eT : len - (len - target) = target := by bv_decide
  refine ⟨_, hABC, ?_, pc3, sp3, bx3, bp3, f12, f13, f14, f15, ?_, ?_, ?_, ?_⟩
  · simp only [mergeShows, List.append_assoc]
  · show Quad s3.mem _ _; rw [mem3, ← eT]; exact q2
  · show Entries s3.mem _ _; rw [mem3]; rw [eT] at E2; exact E2
  · show s3.mem _ = _; rw [mem3]; exact tag2
  · intro x hF hP hA hS
    show s3.mem x = m x
    rw [mem3, out2 x hF hA hS, out1 x hF hP]

#print axioms merge_whole

end MergeCode
