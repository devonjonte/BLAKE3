import Lemmas_ladd
import Spec_lroot
open X86 Cells

/-! # `lroot`: lemmas for the prover

Written by hand for this function; its source names them. `Levels.Fold` is what holds at the head of
`lroot`'s loop: the levels from `base` up are still to be folded, and the buffer `acc` holds the subtree
over all the chunks they do not cover. Checked by Lean; not to be read. -/

namespace Levels

variable {k : Blake3.CV} {chunks : Array Blake3.Node}

unseal Kernels.out in
/-- **What a one-block kernel leaves for a key, two values, counter 0, length 64 and any flags is the first
eight words of the specification's compression of them.** -/
theorem out_spec (k0 k1 l0 l1 r0 r1 : V) (x : BitVec 32) (fl : UInt32) (hx : x = bv fl) :
    words8 (Kernels.out k0 k1 l0 l1 r0 r1 0#64 64#32 x).1 (Kernels.out k0 k1 l0 l1 r0 r1 0#64 64#32 x).2
      = Blake3.first8 (Blake3.BLAKE3_COMPRESS (words8 k0 k1) (words8 l0 l1 ++ words8 r0 r1) 0 64 fl) := by
  have h := specCv_is_the_specifications (words8 k0 k1) (words8 l0 l1 ++ words8 r0 r1) 0 64 fl
  rw [words8_bv, block_bv] at h
  have h' : specCv (cvWords k0 k1) (blockWords l0 l1 r0 r1) 0#64 64#32 x
      = (Blake3.first8 (Blake3.BLAKE3_COMPRESS (words8 k0 k1) (words8 l0 l1 ++ words8 r0 r1) 0 64 fl)).map bv := by
    rw [hx]; exact h
  simp only [Kernels.out, h', words8, dw_mk4_0, dw_mk4_1, dw_mk4_2, dw_mk4_3]
  ext i hi
  match i, hi with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ => simp [bv]

/-- With the flags of a parent that is the root: the root's output's first eight words, of the parent node. -/
theorem root_out (k0 k1 l0 l1 r0 r1 : V) (flags : BitVec 64) (hf : flags < 256#64) :
    words8 (Kernels.out k0 k1 l0 l1 r0 r1 0#64 64#32 (BitVec.setWidth 32 (BitVec.setWidth 8 (flags ||| 4#64 ||| 8#64)))).1
        (Kernels.out k0 k1 l0 l1 r0 r1 0#64 64#32 (BitVec.setWidth 32 (BitVec.setWidth 8 (flags ||| 4#64 ||| 8#64)))).2
      = Blake3.first8 (Blake3.BLAKE3_COMPRESS (words8 k0 k1) (words8 l0 l1 ++ words8 r0 r1) 0 64
          ((⟨flags.setWidth 32⟩ ||| Blake3.PARENT) ||| Blake3.ROOT)) := by
  apply out_spec
  show _ = flags.setWidth 32 ||| 4#32 ||| 8#32
  bv_decide

/-! ## Arithmetic of addresses and counts, each with nothing else in sight -/

theorem off_bounds (lv : BitVec 64) (a : Nat) (ha : a ≤ 53) :
    64#64 ≤ lv + BitVec.ofNat 64 (64 * a + 64) - lv ∧ lv + BitVec.ofNat 64 (64 * a + 64) - lv ≤ 3456#64 := by
  constructor <;> bv_omega

theorem off_succ (lv : BitVec 64) (a : Nat) :
    lv + BitVec.ofNat 64 (64 * a + 64) + 64#64 = lv + BitVec.ofNat 64 (64 * (a + 1) + 64) := by bv_omega

theorem in_levels (lv y : BitVec 64) (a : Nat) (ha : a ≤ 53)
    (hy : (y - (lv + BitVec.ofNat 64 (64 * a + 64) + 64#64)).toNat < 64 * (53 - a)) : y - lv < 3520#64 := by bv_omega

theorem in_levels0 (lv y : BitVec 64) (hy : (y - (lv + 64#64)).toNat < 64 * 54) : y - lv < 3520#64 := by bv_omega

theorem shr_ofNat (r : Nat) (h : r < 2 ^ 54) : BitVec.ofNat 64 r >>> 1 = BitVec.ofNat 64 (r / 2) := by bv_omega

theorem count_pred (h1 : 1 ≤ chunks.size) (hn : chunks.size ≤ 2 ^ 54) :
    count chunks - 1#64 = BitVec.ofNat 64 (chunks.size - 1) := by
  simp only [count]; bv_omega

theorem two_mul_pow (c a : Nat) : c * 2 ^ (a + 1) = 2 * c * 2 ^ a := by
  rw [Nat.pow_succ, Nat.mul_comm 2 c, Nat.mul_assoc, Nat.mul_comm 2 (2 ^ a)]

theorem pow_half (a : Nat) (ha : a ≤ 53) : 2 ^ (54 - a) = 2 * 2 ^ (53 - a) := by
  rw [show 54 - a = (53 - a) + 1 by omega, Nat.pow_succ]; omega

theorem odd_of_and {r : Nat} (h : BitVec.ofNat 64 r &&& 1#64 = 1#64) : r % 2 = 1 := by
  rw [and_one_ofNat] at h
  rcases Nat.mod_two_eq_zero_or_one r with h0 | h1
  · rw [h0] at h; exact absurd h (by decide)
  · exact h1

theorem even_of_and {r : Nat} (h : ¬ BitVec.ofNat 64 r &&& 1#64 = 1#64) : r % 2 = 0 := by
  rw [and_one_ofNat] at h
  rcases Nat.mod_two_eq_zero_or_one r with h0 | h1
  · exact h0
  · rw [h1] at h; exact absurd rfl h

/-- **What holds at the head of `lroot`'s loop.** The loop is at level `a` (`base` is its address) and the
levels from there up have received `r = e` values of `2^a` chunks; the chunks they do not cover, at most
`2^a` and at least one, are a subtree whose value is in `acc`; when no level is left, `acc` holds the
root's output. -/
def Fold (m : Mem) (lv : BitVec 64) (k : Blake3.CV) (flags : BitVec 64) (chunks : Array Blake3.Node) (base e acc : BitVec 64) : Prop :=
  ∃ a r : Nat, a ≤ 54 ∧ base = lv + BitVec.ofNat 64 (64 * a + 64) ∧ e = BitVec.ofNat 64 r ∧ r < 2 ^ (54 - a) ∧
    Lev k ⟨flags.setWidth 32⟩ chunks m (54 - a) base (2 ^ a) r ∧
    r * 2 ^ a < chunks.size ∧ chunks.size ≤ r * 2 ^ a + 2 ^ a ∧
    (0 < r → Cv.At m acc (Blake3.sub k ⟨flags.setWidth 32⟩ chunks (r * 2 ^ a) (chunks.size - r * 2 ^ a))) ∧
    (r = 0 → Cv.At m acc (rootCv k ⟨flags.setWidth 32⟩ chunks))

/-- At entry: the count's cell. -/
theorem At.cell {m : Mem} {lv : BitVec 64} {mode : Blake3.Word} (h : At k mode m lv chunks) : Quad m lv (count chunks) := h.2.2.1

/-- **At entry:** the newest chunk's value, in the bottom level's next place, as the two vectors the code reads. -/
theorem At.newest {m : Mem} {lv : BitVec 64} {mode : Blake3.Word} (h : At k mode m lv chunks) (h2 : 2 ≤ chunks.size) :
    ∃ n0 n1 : V, Vec m (lv + 64#64 + ((count chunks - 1#64) &&& 1#64) <<< 5) n0 ∧
      Vec m (lv + 64#64 + ((count chunks - 1#64) &&& 1#64) <<< 5 + 16#64) n1 ∧
      words8 n0 n1 = Blake3.sub k mode chunks (chunks.size - 1) 1 := by
  obtain ⟨hn, _, _, hrest⟩ := h
  obtain ⟨_, n0, n1, h0, h1, hw⟩ := hrest (by omega)
  rw [count_pred (by omega) hn, place_bits]
  exact ⟨n0, n1, h0, h1, hw⟩

/-- **Before the loop:** the newest chunk's value copied to `acc`; the levels have received all the others. -/
theorem Fold.start {m m' : Mem} {lv flags acc : BitVec 64} {n0 n1 : V}
    (h : At k ⟨flags.setWidth 32⟩ m lv chunks) (h2 : 2 ≤ chunks.size)
    (hw : words8 n0 n1 = Blake3.sub k ⟨flags.setWidth 32⟩ chunks (chunks.size - 1) 1)
    (hp0 : Vec m' acc n0) (hp1 : Vec m' (acc + 16#64) n1)
    (same : ∀ y : BitVec 64, y - lv < 3520#64 → m' y = m y) :
    Fold m' lv k flags chunks (lv + 64#64) (count chunks - 1#64) acc := by
  obtain ⟨hn, _, _, hrest⟩ := h
  obtain ⟨hl, _⟩ := hrest (by omega)
  refine ⟨0, chunks.size - 1, by omega, by simp, count_pred (by omega) hn, by have := pow_le_54 0; simp at this ⊢; omega, ?_, by simp; omega, by simp; omega,
    fun _ => ⟨n0, n1, hp0, hp1, ?_⟩, fun h0 => by omega⟩
  · have := Lev.frame 54 (lv + 64#64) 1 (chunks.size - 1) (by omega) (fun y hy => same y (in_levels0 lv y hy)) hl
    simpa using this
  · rw [hw]; simp only [Nat.pow_zero, Nat.mul_one]
    rw [show chunks.size - (chunks.size - 1) = 1 by omega]

/-- The value in `acc`, as the two vectors the code reads. -/
theorem Fold.acc {m : Mem} {lv flags base e acc : BitVec 64} (h : Fold m lv k flags chunks base e acc) :
    ∃ a0 a1 : V, Vec m acc a0 ∧ Vec m (acc + 16#64) a1 := by
  obtain ⟨a, r, _, _, _, _, _, _, _, hpos, hzero⟩ := h
  rcases Nat.eq_zero_or_pos r with h0 | hp
  · obtain ⟨a0, a1, g0, g1, _⟩ := hzero h0; exact ⟨a0, a1, g0, g1⟩
  · obtain ⟨a0, a1, g0, g1, _⟩ := hpos hp; exact ⟨a0, a1, g0, g1⟩

/-- A level that holds a value (`e` odd): everything a turn there uses. -/
theorem Fold.odd {m : Mem} {lv flags base e acc : BitVec 64} (h : Fold m lv k flags chunks base e acc) (ho : e &&& 1#64 = 1#64) :
    ∃ a c : Nat, a ≤ 53 ∧ base = lv + BitVec.ofNat 64 (64 * a + 64) ∧ e = BitVec.ofNat 64 (2 * c + 1) ∧ 2 * c + 1 < 2 ^ (54 - a) ∧
      Cv.At m base (Blake3.sub k ⟨flags.setWidth 32⟩ chunks (2 * c * 2 ^ a) (2 ^ a)) ∧
      Lev k ⟨flags.setWidth 32⟩ chunks m (53 - a) (base + 64#64) (2 ^ (a + 1)) c ∧
      2 * c * 2 ^ a + 2 ^ a < chunks.size ∧ chunks.size ≤ 2 * c * 2 ^ a + 2 ^ a + 2 ^ a ∧
      Cv.At m acc (Blake3.sub k ⟨flags.setWidth 32⟩ chunks (2 * c * 2 ^ a + 2 ^ a) (chunks.size - (2 * c * 2 ^ a + 2 ^ a))) := by
  obtain ⟨a, r, ha, hbase, he, hr, hl, hlt, hle, hpos, _⟩ := h
  have hodd : r % 2 = 1 := odd_of_and (by rw [← he]; exact ho)
  have ha' : a ≤ 53 := by
    rcases Nat.lt_or_ge a 54 with h | h
    · omega
    · have : a = 54 := by omega
      subst this
      simp at hr; omega
  obtain ⟨c, rfl⟩ : ∃ c, r = 2 * c + 1 := ⟨r / 2, by omega⟩
  rw [show 54 - a = (53 - a) + 1 by omega, Lev_succ] at hl
  have e1 : (2 * c + 1) * 2 ^ a = 2 * c * 2 ^ a + 2 ^ a := by rw [Nat.add_mul, Nat.one_mul]
  rw [e1] at hlt hle
  have hacc := hpos (by omega)
  rw [e1] at hacc
  refine ⟨a, c, ha', hbase, he, hr, ?_, ?_, hlt, hle, hacc⟩
  · have := hl.1 hodd
    rwa [show 2 * c + 1 - 1 = 2 * c by omega] at this
  · have := hl.2
    rwa [show (2 * c + 1) / 2 = c by omega, show 2 * 2 ^ a = 2 ^ (a + 1) by rw [Nat.pow_succ]; omega] at this

/-- **Before a turn at a level that holds a value:** that value as the two vectors the code reads. -/
theorem Fold.level {m : Mem} {lv flags base e acc : BitVec 64} (h : Fold m lv k flags chunks base e acc) (ho : e &&& 1#64 = 1#64) :
    ∃ l0 l1 : V, Vec m base l0 ∧ Vec m (base + 16#64) l1 ∧ 64#64 ≤ base - lv ∧ base - lv ≤ 3456#64 := by
  obtain ⟨a, c, ha, hbase, _, _, ⟨l0, l1, g0, g1, _⟩, _⟩ := Fold.odd h ho
  have hb := off_bounds lv a ha
  rw [← hbase] at hb
  exact ⟨l0, l1, g0, g1, hb.1, hb.2⟩

/-- The same levels, one up, when a turn has written nothing in them. -/
theorem lev_up {m m' : Mem} {lv flags : BitVec 64} {a c : Nat} (ha : a ≤ 53)
    (hup : Lev k ⟨flags.setWidth 32⟩ chunks m (53 - a) (lv + BitVec.ofNat 64 (64 * a + 64) + 64#64) (2 ^ (a + 1)) c)
    (same : ∀ y : BitVec 64, y - lv < 3520#64 → m' y = m y) :
    Lev k ⟨flags.setWidth 32⟩ chunks m' (54 - (a + 1)) (lv + BitVec.ofNat 64 (64 * a + 64) + 64#64) (2 ^ (a + 1)) c := by
  rw [show 54 - (a + 1) = 53 - a by omega]
  exact Lev.frame _ _ _ _ (by omega) (fun y hy => same y (in_levels lv y a ha hy)) hup

/-- **Across a turn that makes a parent below the root:** the level's value and `acc`'s replaced, in `acc`, by
what the kernel leaves for them: the subtree over both. -/
theorem Fold.parent {m m' : Mem} {lv flags base e acc : BitVec 64} {k0 k1 l0 l1 a0 a1 : V}
    (h : Fold m lv k flags chunks base e acc) (ho : e &&& 1#64 = 1#64) (h1 : ¬ e = 1#64) (hk : words8 k0 k1 = k)
    (hl0 : Vec m base l0) (hl1 : Vec m (base + 16#64) l1) (ha0 : Vec m acc a0) (ha1 : Vec m (acc + 16#64) a1)
    (hf : flags < 256#64)
    (hp0 : Vec m' acc (Kernels.out k0 k1 l0 l1 a0 a1 0#64 64#32 (BitVec.setWidth 32 (BitVec.setWidth 8 (flags ||| 4#64)))).1)
    (hp1 : Vec m' (acc + 16#64) (Kernels.out k0 k1 l0 l1 a0 a1 0#64 64#32 (BitVec.setWidth 32 (BitVec.setWidth 8 (flags ||| 4#64)))).2)
    (same : ∀ y : BitVec 64, y - lv < 3520#64 → m' y = m y) :
    Fold m' lv k flags chunks (base + 64#64) (e >>> 1) acc := by
  obtain ⟨a, c, ha, hbase, he, hr, hleft, hup, hlt, hle, hright⟩ := Fold.odd h ho
  have h54 := pow_le_54 a
  have hc : 0 < c := by
    rcases Nat.eq_zero_or_pos c with h0 | hp
    · subst h0; exact absurd he h1
    · exact hp
  have hval : words8 (Kernels.out k0 k1 l0 l1 a0 a1 0#64 64#32 (BitVec.setWidth 32 (BitVec.setWidth 8 (flags ||| 4#64)))).1
      (Kernels.out k0 k1 l0 l1 a0 a1 0#64 64#32 (BitVec.setWidth 32 (BitVec.setWidth 8 (flags ||| 4#64)))).2
      = Blake3.sub k ⟨flags.setWidth 32⟩ chunks (c * 2 ^ (a + 1)) (chunks.size - c * 2 ^ (a + 1)) := by
    rw [Merge.parent k0 k1 l0 l1 a0 a1 flags hf, hk, cv_same hleft hl0 hl1, cv_same hright ha0 ha1, two_mul_pow]
    have hs := Blake3.go_split k ⟨flags.setWidth 32⟩ chunks (2 * c * 2 ^ a) a (chunks.size - (2 * c * 2 ^ a + 2 ^ a)) (by omega) (by omega)
    rw [← hs, show 2 ^ a + (chunks.size - (2 * c * 2 ^ a + 2 ^ a)) = chunks.size - 2 * c * 2 ^ a by omega]
    rfl
  have h2 := pow_half a ha
  subst hbase
  refine ⟨a + 1, c, by omega, off_succ lv a, by rw [he, shr_ofNat _ (by omega)]; congr 1; omega, by rw [show 54 - (a + 1) = 53 - a by omega]; omega,
    lev_up ha hup same, by rw [two_mul_pow]; omega, by rw [two_mul_pow, Nat.pow_succ]; omega, fun _ => ⟨_, _, hp0, hp1, hval⟩, fun h0 => by omega⟩

/-- **Across the turn that makes the root:** the same with the root's flags; nothing is left to fold. -/
theorem Fold.root {m m' : Mem} {lv flags base e acc : BitVec 64} {k0 k1 l0 l1 a0 a1 : V}
    (h : Fold m lv k flags chunks base e acc) (ho : e &&& 1#64 = 1#64) (h1 : e = 1#64) (hk : words8 k0 k1 = k)
    (hl0 : Vec m base l0) (hl1 : Vec m (base + 16#64) l1) (ha0 : Vec m acc a0) (ha1 : Vec m (acc + 16#64) a1)
    (hf : flags < 256#64)
    (hp0 : Vec m' acc (Kernels.out k0 k1 l0 l1 a0 a1 0#64 64#32 (BitVec.setWidth 32 (BitVec.setWidth 8 (flags ||| 4#64 ||| 8#64)))).1)
    (hp1 : Vec m' (acc + 16#64) (Kernels.out k0 k1 l0 l1 a0 a1 0#64 64#32 (BitVec.setWidth 32 (BitVec.setWidth 8 (flags ||| 4#64 ||| 8#64)))).2) :
    Fold m' lv k flags chunks (base + 64#64) (e >>> 1) acc := by
  obtain ⟨a, c, ha, hbase, he, hr, hleft, hup, hlt, hle, hright⟩ := Fold.odd h ho
  have h54 := pow_le_54 a
  have hc : c = 0 := by
    rw [h1] at he
    have := congrArg BitVec.toNat he
    simp only [BitVec.toNat_ofNat] at this
    omega
  subst hc
  simp only [Nat.mul_zero, Nat.zero_mul, Nat.zero_add] at hleft hright hlt hle
  have hval : words8 (Kernels.out k0 k1 l0 l1 a0 a1 0#64 64#32 (BitVec.setWidth 32 (BitVec.setWidth 8 (flags ||| 4#64 ||| 8#64)))).1
      (Kernels.out k0 k1 l0 l1 a0 a1 0#64 64#32 (BitVec.setWidth 32 (BitVec.setWidth 8 (flags ||| 4#64 ||| 8#64)))).2
      = rootCv k ⟨flags.setWidth 32⟩ chunks := by
    rw [root_out k0 k1 l0 l1 a0 a1 flags hf, hk, cv_same hleft hl0 hl1, cv_same hright ha0 ha1]
    have hs := Blake3.go_split k ⟨flags.setWidth 32⟩ chunks 0 a (chunks.size - 2 ^ a) (by omega) (by omega)
    rw [show 2 ^ a + (chunks.size - 2 ^ a) = chunks.size by omega, Nat.zero_add] at hs
    simp only [rootCv, Blake3.tree, hs, Blake3.parentNode]
  subst hbase
  refine ⟨a + 1, 0, by omega, off_succ lv a, by rw [h1]; rfl, Nat.two_pow_pos _, Lev_none m' _ _ _, by simp; omega,
    by simp only [Nat.zero_mul, Nat.zero_add, Nat.pow_succ]; omega, fun h0 => by omega, fun _ => ⟨_, _, hp0, hp1, hval⟩⟩

/-- **Across a turn at a level that holds nothing:** the same value covers the same chunks, one level up. -/
theorem Fold.skip {m m' : Mem} {lv flags base e acc : BitVec 64}
    (h : Fold m lv k flags chunks base e acc) (ho : ¬ e &&& 1#64 = 1#64) (hc : 0#64 < e)
    (same : ∀ y : BitVec 64, y - lv < 3520#64 → m' y = m y) (sameAcc : ∀ y : BitVec 64, y - acc < 32#64 → m' y = m y) :
    Fold m' lv k flags chunks (base + 64#64) (e >>> 1) acc := by
  obtain ⟨a, r, ha, hbase, he, hr, hl, hlt, hle, hpos, _⟩ := h
  have h54 := pow_le_54 a
  have heven : r % 2 = 0 := even_of_and (by rw [← he]; exact ho)
  have hr0 : 0 < r := by
    rcases Nat.eq_zero_or_pos r with h0 | hp
    · subst h0; subst he; exact absurd hc (by decide)
    · exact hp
  have ha' : a ≤ 53 := by
    rcases Nat.lt_or_ge a 54 with h | h
    · omega
    · have : a = 54 := by omega
      subst this
      simp at hr; omega
  obtain ⟨c, rfl⟩ : ∃ c, r = 2 * c := ⟨r / 2, by omega⟩
  rw [show 54 - a = (53 - a) + 1 by omega, Lev_succ] at hl
  have hup := hl.2
  rw [show 2 * c / 2 = c by omega, show 2 * 2 ^ a = 2 ^ (a + 1) by rw [Nat.pow_succ]; omega] at hup
  have h2 := pow_half a ha'
  have hacc := Cv.At.frame (hpos hr0) sameAcc
  subst hbase
  refine ⟨a + 1, c, by omega, off_succ lv a, by rw [he, shr_ofNat _ (by omega)]; congr 1; omega, by rw [show 54 - (a + 1) = 53 - a by omega]; omega,
    lev_up ha' hup same, by rw [two_mul_pow]; exact hlt, by rw [two_mul_pow, Nat.pow_succ]; omega, fun _ => by rw [two_mul_pow]; exact hacc, fun h0 => by omega⟩

/-- **When the loop ends:** `acc` holds the root's output, as the two vectors the code copies out. -/
theorem Fold.done {m : Mem} {lv flags base e acc : BitVec 64} (h : Fold m lv k flags chunks base e acc) (hc : ¬ 0#64 < e) :
    ∃ r0 r1 : V, Vec m acc r0 ∧ Vec m (acc + 16#64) r1 ∧ words8 r0 r1 = rootCv k ⟨flags.setWidth 32⟩ chunks := by
  obtain ⟨a, r, _, _, he, hr, _, _, _, _, hzero⟩ := h
  have h54 := pow_le_54 a
  have hr0 : r = 0 := by
    rcases Nat.eq_zero_or_pos r with h0 | hp
    · exact h0
    · exfalso; apply hc; subst he; bv_omega
  exact hzero hr0

end Levels

/-- **At the return:** the root's output at `out`. -/
theorem Lroot.exit {m' : Mem} {out flags : BitVec 64} {k : Blake3.CV} {chunks : Array Blake3.Node} {r0 r1 : V}
    (hw : words8 r0 r1 = Levels.rootCv k ⟨flags.setWidth 32⟩ chunks)
    (hp0 : Vec m' out r0) (hp1 : Vec m' (out + 16#64) r1) :
    True ∧ Cv.At m' out (Levels.rootCv k ⟨flags.setWidth 32⟩ chunks) := ⟨trivial, r0, r1, hp0, hp1, hw⟩
