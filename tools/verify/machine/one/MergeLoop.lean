import MergeTurn
open X86

namespace MergeCode

/-! # `CvStack::merge`'s loop, as compiled: all its turns

By induction on the turns, from `turn_avx` and `turn_sse`. -/

/-- The stack's values in memory, from the top down: the first at `a`, each next one 32 bytes lower. -/
def Entries (m : Mem) : BitVec 64 → List (V × V) → Prop
  | _, [] => True
  | a, e :: es => Vec m (a + 0#64) e.1 ∧ Vec m (a + 16#64) e.2 ∧ Entries m (a - 32#64) es

/-- **`merge`'s loop as a function** on the stack, top first: the two top values become their parent,
`n` times. -/
def mergeN (k0 k1 : V) (fl : BitVec 8) : Nat → List (V × V) → List (V × V)
  | 0, es => es
  | n + 1, r :: l :: es => mergeN k0 k1 fl n (merged k0 k1 l.1 l.2 r.1 r.2 fl :: es)
  | _ + 1, es => es

/-- Values in memory are still there in a memory that agrees on their bytes. -/
theorem entries_congr {m m' : Mem} : ∀ (es : List (V × V)) (a : BitVec 64),
    (∀ x : BitVec 64, (a + 31#64 - x).toNat < 32 * es.length → m' x = m x) → Entries m a es → Entries m' a es := by
  intro es
  induction es with
  | nil => intros; trivial
  | cons e es ih =>
    intro a h ⟨h0, h1, hr⟩
    simp only [List.length_cons] at h
    exact ⟨vec_congr (fun x hx => h x (by bv_omega)) h0, vec_congr (fun x hx => h x (by bv_omega)) h1,
      ih (a - 32#64) (fun x hx => h x (by bv_omega)) hr⟩

theorem shl5 (x : BitVec 64) : x <<< 5 = x * 32#64 := by bv_decide

/-- Where things are, and that they are apart: the stack's array is nine bytes into the `CvStack`; the
frame is aligned; and neither the array, nor the length and tag, nor the key is in `merge`'s frame, nor
the key in the `CvStack`. -/
structure Places (self arr keyp fp : BitVec 64) : Prop where
  harr : arr = self + 9#64
  hfp : fp &&& 63#64 = 0#64
  hW : self ≤ 18446744073709549846#64
  gArr : ∀ x : BitVec 64, (x - arr).toNat < 1760 → inF (x - fp) = false
  gKey : ∀ x : BitVec 64, (x - keyp).toNat < 32 → inF (x - fp) = false
  gSelf : ∀ x : BitVec 64, (x - self).toNat < 9 → inF (x - fp) = false
  gKeyArr : ∀ x : BitVec 64, (x - keyp).toNat < 32 → 1760 ≤ (x - arr).toNat
  gKeySelf : ∀ x : BitVec 64, (x - keyp).toNat < 32 → 9 ≤ (x - self).toNat

/-- What holds at the loop's head: the tag, the length, the stack's values from the top, the key, the
frame owned, and the platform and flags `merge` put in it. -/
def Head (self arr keyp fp : BitVec 64) (k0 k1 : V) (fl plat : BitVec 8) (m : Mem) (len : BitVec 64) (es : List (V × V)) : Prop :=
  m (self + 8#64) = some 1#8 ∧ Quad m (self + 0#64) len ∧ Entries m (arr + (len + 18446744073709551615#64) <<< 5) es ∧
  Vec m (keyp + 0#64) k0 ∧ Vec m (keyp + 16#64) k1 ∧ (∀ d : BitVec 64, inF d = true → (m (fp + d)).isSome = true) ∧
  m (fp + 58#64) = some plat ∧ m (fp + 59#64) = some fl ∧ m (fp + 60#64) = some fl ∧ m (fp + 61#64) = some 0#8 ∧
  m (fp + 62#64) = some 0#8 ∧ m (fp + 63#64) = some 0#8

set_option maxRecDepth 1000000 in
/-- One turn, by whichever kernel the platform byte selects. -/
theorem turn (self arr keyp fp len nB : BitVec 64) (l0 l1 r0 r1 k0 k1 : V) (fl plat : BitVec 8) (m : Mem)
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
    ∃ K s', steps Code.prog K ⟨len, rcx, rdx, self, fp, rbp, rsi, rdi, r8, r9, arr, r13, keyp, nB, zf, cf, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, m, 0x40094⟩ = some s' ∧
      s'.pc = (if nB - 1#64 = 0#64 then 0x401AB else 0x40094) ∧ s'.rax = len - 1#64 ∧ s'.r15 = nB - 1#64 ∧
      s'.rbx = self ∧ s'.rsp = fp ∧ s'.rbp = rbp ∧ s'.r12 = arr ∧ s'.r14 = keyp ∧
      Vec s'.mem (arr + ((len + 18446744073709551614#64) <<< 5) + 0#64) (merged k0 k1 l0 l1 r0 r1 fl).1 ∧
      Vec s'.mem (arr + ((len + 18446744073709551614#64) <<< 5) + 16#64) (merged k0 k1 l0 l1 r0 r1 fl).2 ∧
      Quad s'.mem (self + 0#64) (len - 1#64) ∧
      (∀ d : BitVec 64, inF d = true → (s'.mem (fp + d)).isSome = true) ∧
      s'.mem (fp + 58#64) = some plat ∧ s'.mem (fp + 59#64) = some fl ∧ s'.mem (fp + 60#64) = some fl ∧
      s'.mem (fp + 61#64) = some 0#8 ∧ s'.mem (fp + 62#64) = some 0#8 ∧ s'.mem (fp + 63#64) = some 0#8 ∧
      (∀ x : BitVec 64, inF (x - fp) = false → 32 ≤ (x - (arr + ((len + 18446744073709551614#64) <<< 5))).toNat → 8 ≤ (x - self).toNat → s'.mem x = m x) := by
  by_cases h : plat = 5#8
  · subst h
    obtain ⟨s', hs, rest⟩ := turn_avx self arr keyp fp len nB l0 l1 r0 r1 k0 k1 fl m rcx rdx rbp rsi rdi r8 r9 r13 zf cf x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15
      hlo hhi hfp hTag hLen hL0 hL1 hR0 hR1 hK0 hK1 hOwn hPlat hFl hF0 hF1 hF2 hF3 oSlot oKey oSelf hLS
    exact ⟨_, s', hs, rest⟩
  · obtain ⟨s', hs, rest⟩ := turn_sse self arr keyp fp len nB l0 l1 r0 r1 k0 k1 fl m rcx rdx rbp rsi rdi r8 r9 r13 zf cf x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15
      hlo hhi hfp hTag hLen hL0 hL1 hR0 hR1 hK0 hK1 hOwn plat h hPlat hFl hF0 hF1 hF2 hF3 oSlot oKey oSelf hLS
    exact ⟨_, s', hs, rest⟩

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- **The loop.** At its head with the stack's `len` values `es` (top first) in memory and `n` turns to go
(`1 ≤ n < len`), the compiled loop runs to its exit with the length `len - n` and the stack
`mergeN n es` in memory; the tag stays; nothing outside `merge`'s frame, the stack's array and its length
changes. No panic site is reached. -/
theorem loop (self arr keyp fp : BitVec 64) (k0 k1 : V) (fl plat : BitVec 8) (P : Places self arr keyp fp) :
    ∀ (n : Nat) (es : List (V × V)) (len nB : BitVec 64) (m : Mem) (rcx rdx rbp rsi rdi r8 r9 r13 : BitVec 64) (zf cf : Option Bool) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : V),
      1 ≤ n → n + 1 ≤ es.length → len.toNat = es.length → es.length ≤ 55 → nB.toNat = n →
      Head self arr keyp fp k0 k1 fl plat m len es →
      ∃ K s', steps Code.prog K ⟨len, rcx, rdx, self, fp, rbp, rsi, rdi, r8, r9, arr, r13, keyp, nB, zf, cf, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, m, 0x40094⟩ = some s' ∧
        s'.pc = 0x401AB ∧ s'.rbx = self ∧ s'.rsp = fp ∧ s'.rbp = rbp ∧ s'.r12 = arr ∧ s'.r14 = keyp ∧
        Quad s'.mem (self + 0#64) (len - nB) ∧
        Entries s'.mem (arr + (len - nB + 18446744073709551615#64) <<< 5) (mergeN k0 k1 fl n es) ∧
        s'.mem (self + 8#64) = some 1#8 ∧
        (∀ x : BitVec 64, inF (x - fp) = false → 1760 ≤ (x - arr).toNat → 9 ≤ (x - self).toNat → s'.mem x = m x) := by
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
    obtain ⟨K1, s1, e1, pc1, ax1, r151, bx1, sp1, bp1, c12, c14, vM0, vM1, qLen1, own1, f58, f59, f60, f61, f62, f63, out1⟩ :=
      turn self arr keyp fp len nB l.1 l.2 r.1 r.2 k0 k1 fl plat m rcx rdx rbp rsi rdi r8 r9 r13 zf cf x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15
        hlo hhi hfp hTag hLen hL0 hL1 hR0 hR1 hK0 hK1 hOwn hPlat hFl hF0 hF1 hF2 hF3 oSlot gKey gSelf hLS
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
      refine ⟨K1, s1, e1, by rw [pc1, hnB1]; rfl, bx1, sp1, bp1, c12, c14, by rw [hnB1]; exact qLen1, ?_, tag1, ?_⟩
      · rw [hnB1, eTop]; exact ⟨vM0, vM1, rest1⟩
      · intro x hx ha hs; exact out1 x hx (by rw [shl5]; bv_omega) (by omega)
    · have hne : nB - 1#64 ≠ 0#64 := by bv_omega
      have pc1' : s1.pc = 0x40094 := by rw [pc1, if_neg hne]
      obtain ⟨rax1, rcx1, rdx1, rbx1, rsp1, rbp1, rsi1, rdi1, r81, r91, r121, r131, r141, r151v, zf1, cf1, y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, m1, pcv⟩ := s1
      simp only at pc1' ax1 r151 bx1 sp1 bp1 c12 c14 vM0 vM1 qLen1 own1 f58 f59 f60 f61 f62 f63 out1 tag1 rest1 key0 key1
      subst pcv rax1 r151v rbx1 rsp1 rbp1 r121 r141
      have H1 : Head self arr keyp fp k0 k1 fl plat m1 (len - 1#64) (merged k0 k1 l.1 l.2 r.1 r.2 fl :: rest) :=
        ⟨tag1, qLen1, ⟨by rw [eTop]; exact vM0, by rw [eTop]; exact vM1, by rw [eTop]; exact rest1⟩, key0, key1, own1,
          f58, f59, f60, f61, f62, f63⟩
      obtain ⟨K2, s2, e2, pc2, bx2, sp2, bp2, d12, d14, q2, E2, tag2, out2⟩ :=
        ih (merged k0 k1 l.1 l.2 r.1 r.2 fl :: rest) (len - 1#64) (nB - 1#64) m1 rcx1 rdx1 rbp rsi1 rdi1 r81 r91 r131 zf1 cf1 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15
          (by omega) (by simp only [List.length_cons]; omega) (by simp only [List.length_cons]; bv_omega)
          (by simp only [List.length_cons]; omega) (by bv_omega) H1
      have eD : len - nB = len - 1#64 - (nB - 1#64) := by bv_decide
      refine ⟨K1 + K2, s2, by rw [steps_add, e1, Option.bind_some, e2], pc2, bx2, sp2, bp2, d12, d14, by rw [eD]; exact q2,
        by rw [eD]; exact E2, tag2, ?_⟩
      intro x hx ha hs
      rw [out2 x hx ha hs]; exact out1 x hx (by rw [shl5]; bv_omega) (by omega)

#print axioms loop

end MergeCode
