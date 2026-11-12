import StackLemmas
import Lemmas_merge
import Spec_ladd
import Kernels
open X86 Cells

/-! # `ladd`: lemmas for the prover

Written by hand: for the levels (what holds at the head of `ladd`'s loop, taken apart into the cells code
reads and writes and put together again) and for this function; its source names them. Checked by Lean;
not to be read. By convention a lemma's memory is `m` (and the memory after, `m'`). -/

namespace Levels

/-- The count of the levels' chunks, as the machine holds it. -/
def count (chunks : Array Blake3.Node) : BitVec 64 := BitVec.ofNat 64 chunks.size

variable {k : Blake3.CV} {mode : Blake3.Word} {chunks : Array Blake3.Node}

theorem Lev_succ (m : Mem) (f : Nat) (a : BitVec 64) (size r : Nat) :
    Lev k mode chunks m (f + 1) a size r =
      ((r % 2 = 1 → Cv.At m a (Blake3.sub k mode chunks ((r - 1) * size) size)) ∧ Lev k mode chunks m f (a + 64#64) (2 * size) (r / 2)) := rfl

/-- Levels that have received nothing hold nothing. -/
theorem Lev_none (m : Mem) : ∀ (f : Nat) (a : BitVec 64) (size : Nat), Lev k mode chunks m f a size 0
  | 0, _, _ => rfl
  | f + 1, a, size => by
    rw [Lev_succ]
    exact ⟨fun h => absurd h (by decide), Lev_none m f (a + 64#64) (2 * size)⟩

/-- The levels are in their own bytes: a memory that agrees on them holds them too. -/
theorem Lev.frame {m m' : Mem} : ∀ (f : Nat) (a : BitVec 64) (size r : Nat), f ≤ 54 →
    (∀ y : BitVec 64, (y - a).toNat < 64 * f → m' y = m y) → Lev k mode chunks m f a size r → Lev k mode chunks m' f a size r
  | 0, _, _, _, _, _, h => h
  | f + 1, a, size, r, hf, same, h => by
    rw [Lev_succ] at h ⊢
    exact ⟨fun hr => Cv.At.frame (h.1 hr) (fun y hy => same y (by bv_omega)),
      Lev.frame f (a + 64#64) (2 * size) (r / 2) (by omega) (fun y hy => same y (by bv_omega)) h.2⟩

theorem place_odd {r : Nat} (h : r % 2 = 1) : place r = 32#64 := by simp only [place, h, ite_true]
theorem place_even {r : Nat} (h : r % 2 = 0) : place r = 0#64 := by
  simp only [place]; exact if_neg (by omega)

/-- The same when the bytes of the next value's place change: the levels do not speak of that place. -/
theorem Lev.frame_but {m m' : Mem} (f : Nat) (a : BitVec 64) (size r : Nat) (hf : f ≤ 54)
    (same : ∀ y : BitVec 64, (y - a).toNat < 64 * f → 32#64 ≤ y - (a + place r) → m' y = m y)
    (h : Lev k mode chunks m f a size r) : Lev k mode chunks m' f a size r := by
  cases f with
  | zero => exact h
  | succ f =>
    rw [Lev_succ] at h ⊢
    refine ⟨fun hr => Cv.At.frame (h.1 hr) (fun y hy => same y (by bv_omega) ?_),
      Lev.frame f (a + 64#64) (2 * size) (r / 2) (by omega) (fun y hy => same y (by bv_omega) ?_) h.2⟩
    · rw [place_odd hr]; bv_omega
    · rcases Nat.mod_two_eq_zero_or_one r with h0 | h1
      · rw [place_even h0]; bv_omega
      · rw [place_odd h1]; bv_omega

/-- From a level up to the whole: levels below one that has received `R` values, each empty, are the
levels that have received `R` times as many of the smaller values. -/
theorem Lev.below {m : Mem} (lv : BitVec 64) : ∀ (a R : Nat), a ≤ 54 →
    Lev k mode chunks m (54 - a) (lv + BitVec.ofNat 64 (64 * a + 64)) (2 ^ a) R → Lev k mode chunks m 54 (lv + 64#64) 1 (R * 2 ^ a)
  | 0, R, _, h => by simpa using h
  | a + 1, R, ha, h => by
    have ih := Lev.below lv a (2 * R) (by omega) (by
      rw [show 54 - a = (54 - (a + 1)) + 1 by omega, Lev_succ]
      refine ⟨fun h2 => absurd h2 (by omega), ?_⟩
      rw [show 2 * R / 2 = R by omega,
        show lv + BitVec.ofNat 64 (64 * a + 64) + 64#64 = lv + BitVec.ofNat 64 (64 * (a + 1) + 64) by bv_omega,
        show 2 * 2 ^ a = 2 ^ (a + 1) by rw [Nat.pow_succ]; omega]
      exact h)
    rwa [show 2 * R * 2 ^ a = R * 2 ^ (a + 1) by rw [Nat.pow_succ, Nat.mul_comm 2 R, Nat.mul_assoc, Nat.mul_comm 2 (2 ^ a)]] at ih

/-- A subtree of the chunks there are is the same subtree after one more chunk. -/
theorem go_push (k : Blake3.CV) (mode : Blake3.Word) (chunks : Array Blake3.Node) (new : Blake3.Node) :
    ∀ (n start : Nat), 1 ≤ n → start + n ≤ chunks.size →
      Blake3.tree.go k mode (chunks.push new) start n = Blake3.tree.go k mode chunks start n := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro start h1 hle
    rw [Blake3.tree.go.eq_1 k mode (chunks.push new), Blake3.tree.go.eq_1 k mode chunks]
    by_cases h : n ≤ 1
    · rw [dif_pos h, dif_pos h]
      rw [getElem!_pos (chunks.push new) start (by rw [Array.size_push]; omega), getElem!_pos chunks start (by omega)]
      exact Array.getElem_push_lt (by omega)
    · rw [dif_neg h, dif_neg h]
      have hk := Blake3.leftCount_lt n (by omega)
      have hp := Blake3.leftCount_pos n
      simp only
      rw [ih _ hk _ hp (by omega), ih _ (by omega) _ (by omega) (by omega)]

theorem sub_push (k : Blake3.CV) (mode : Blake3.Word) (chunks : Array Blake3.Node) (new : Blake3.Node) (start n : Nat)
    (h1 : 1 ≤ n) (hle : start + n ≤ chunks.size) :
    Blake3.sub k mode (chunks.push new) start n = Blake3.sub k mode chunks start n := by
  simp only [Blake3.sub, go_push k mode chunks new n start h1 hle]

/-- The new chunk's own subtree is its node. -/
theorem sub_new (k : Blake3.CV) (mode : Blake3.Word) (chunks : Array Blake3.Node) (new : Blake3.Node) :
    Blake3.sub k mode (chunks.push new) chunks.size 1 = new.cv := by
  simp only [Blake3.sub, Blake3.go_one]
  rw [getElem!_pos (chunks.push new) chunks.size (by rw [Array.size_push]; omega)]
  simp

/-- The levels of the chunks there are, are the levels after one more chunk has been added to the array. -/
theorem Lev.push (new : Blake3.Node) {m : Mem} : ∀ (f : Nat) (a : BitVec 64) (size r : Nat), 0 < size →
    r * size ≤ chunks.size → Lev k mode chunks m f a size r → Lev k mode (chunks.push new) m f a size r
  | 0, _, _, _, _, _, h => h
  | f + 1, a, size, r, hs, hle, h => by
    rw [Lev_succ] at h ⊢
    refine ⟨fun hr => ?_, Lev.push new f (a + 64#64) (2 * size) (r / 2) (by omega) ?_ h.2⟩
    · have h1 : size ≤ r * size := Nat.le_mul_of_pos_left size (by omega)
      rw [sub_push k mode chunks new _ _ hs (by rw [Nat.sub_mul, Nat.one_mul]; omega)]
      exact h.1 hr
    · have := Nat.mul_le_mul_right size (Nat.div_mul_le_self r 2)
      rw [show r / 2 * (2 * size) = r / 2 * 2 * size by rw [Nat.mul_assoc]]
      omega

/-- A parent of two whole subtrees side by side is the subtree over both. -/
theorem sub_pair (k : Blake3.CV) (mode : Blake3.Word) (chunks : Array Blake3.Node) (start a : Nat) :
    (Blake3.parentNode k mode (Blake3.sub k mode chunks start (2 ^ a)) (Blake3.sub k mode chunks (start + 2 ^ a) (2 ^ a))).cv
      = Blake3.sub k mode chunks start (2 ^ (a + 1)) := by
  have hs := Blake3.go_split k mode chunks start a (2 ^ a) (Nat.two_pow_pos a) (Nat.le_refl _)
  rw [← hs, show 2 ^ a + 2 ^ a = 2 ^ (a + 1) by rw [Nat.pow_succ]; omega]
  rfl

theorem vec_same {m : Mem} {a : BitVec 64} {v w : V} (h : Vec m a v) (h' : Vec m a w) : v = w :=
  Option.some.inj ((read_vec h).symm.trans (read_vec h'))

/-- A chaining value read as two vectors is the one memory holds there. -/
theorem cv_same {m : Mem} {a : BitVec 64} {cv : Blake3.CV} {v0 v1 : V} (h : Cv.At m a cv) (h0 : Vec m a v0) (h1 : Vec m (a + 16#64) v1) :
    words8 v0 v1 = cv := by
  obtain ⟨w0, w1, g0, g1, hw⟩ := h
  rw [vec_same h0 g0, vec_same h1 g1, hw]

theorem and_one_ofNat (n : Nat) : BitVec.ofNat 64 n &&& 1#64 = BitVec.ofNat 64 (n % 2) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
  rw [show (1 % 2 ^ 64 : Nat) = 1 from rfl, Nat.and_one_is_mod]
  omega

/-- The lowest bit of a count, shifted to a place's offset. -/
theorem place_bits (n : Nat) : (BitVec.ofNat 64 n &&& 1#64) <<< 5 = place n := by
  rw [and_one_ofNat]
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · rw [h, place_even h]; rfl
  · rw [h, place_odd h]; rfl

theorem even_ofNat {n : Nat} (h : BitVec.ofNat 64 n &&& 1#64 = 0#64) : n % 2 = 0 := by
  rw [and_one_ofNat] at h
  rcases Nat.mod_two_eq_zero_or_one n with h0 | h1
  · exact h0
  · rw [h1] at h; exact absurd h (by decide)

theorem odd_ofNat {n : Nat} (h : ¬ BitVec.ofNat 64 n &&& 1#64 = 0#64) : n % 2 = 1 := by
  rw [and_one_ofNat] at h
  rcases Nat.mod_two_eq_zero_or_one n with h0 | h1
  · rw [h0] at h; exact absurd rfl h
  · exact h1

/-- **What holds at the head of `ladd`'s loop.** The levels own their bytes and the count is in its cell.
The loop is at level `a` (`src` is its address) and `x - 1 = r` values of `2^a` chunks have been received
there: the chunks are `(r + 1) 2^a`, the levels from `a` up are as `r` values received leave them, and one
more value, the newest `2^a` chunks', is in level `a`'s next place. (With no chunk yet: nothing.) -/
def Mid (m : Mem) (lv : BitVec 64) (k : Blake3.CV) (flags : BitVec 64) (chunks : Array Blake3.Node) (src x : BitVec 64) : Prop :=
  chunks.size < 2 ^ 54 ∧ Region m lv 3520#64 ∧ Quad m lv (count chunks) ∧
  ∃ a r : Nat, a ≤ 53 ∧ src = lv + BitVec.ofNat 64 (64 * a + 64) ∧ x = BitVec.ofNat 64 (r + 1) ∧ r + 1 < 2 ^ (54 - a) ∧
    (chunks.size = 0 → a = 0 ∧ r = 0) ∧
    (0 < chunks.size → chunks.size = (r + 1) * 2 ^ a ∧
      Lev k ⟨flags.setWidth 32⟩ chunks m (54 - a) src (2 ^ a) r ∧
      Cv.At m (src + place r) (Blake3.sub k ⟨flags.setWidth 32⟩ chunks (r * 2 ^ a) (2 ^ a)))

theorem pow_le_54 (a : Nat) : 2 ^ (54 - a) ≤ 2 ^ 54 := Nat.pow_le_pow_right (by decide) (Nat.sub_le 54 a)

/-- What a holder may read at once: the count's cell, the bytes owned, where `src` is. -/
theorem Mid.cells {m : Mem} {lv src x flags : BitVec 64} {chunks : Array Blake3.Node} (h : Mid m lv k flags chunks src x) :
    Quad m lv (count chunks) ∧ Region m lv 3520#64 ∧ 64#64 ≤ src - lv ∧ src - lv ≤ 3456#64 := by
  obtain ⟨_, hR, hq, a, r, ha, hsrc, _⟩ := h
  refine ⟨hq, hR, ?_, ?_⟩ <;> (subst hsrc; bv_omega)

/-- It is in the levels' own 3520 bytes. -/
theorem Mid.frame {m m' : Mem} {lv src x flags : BitVec 64} {chunks : Array Blake3.Node} (h : Mid m lv k flags chunks src x)
    (same : ∀ y : BitVec 64, y - lv < 3520#64 → m' y = m y) : Mid m' lv k flags chunks src x := by
  obtain ⟨hn, hR, hq, a, r, ha, hsrc, hx, hr, h0, h1⟩ := h
  refine ⟨hn, ?_, quad_congr (fun y hy => same y (by bv_omega)) hq, a, r, ha, hsrc, hx, hr, h0, fun hp => ?_⟩
  · intro d hd
    rw [same _ (by bv_omega)]; exact hR d hd
  obtain ⟨e, hl, hc⟩ := h1 hp
  have hpl : place r = 0#64 ∨ place r = 32#64 := by
    rcases Nat.mod_two_eq_zero_or_one r with h | h
    · exact Or.inl (place_even h)
    · exact Or.inr (place_odd h)
  refine ⟨e, Lev.frame _ _ _ _ (by omega) (fun y hy => same y ?_) hl, Cv.At.frame hc (fun y hy => same y ?_)⟩
  · subst hsrc; bv_omega
  · subst hsrc; rcases hpl with h | h <;> (rw [h] at hy; bv_omega)

/-- **At entry:** the levels at rest are the loop's head at the bottom level. -/
theorem At.start {m : Mem} {lv flags : BitVec 64} {chunks : Array Blake3.Node} (h : At k ⟨flags.setWidth 32⟩ m lv chunks) :
    Mid m lv k flags chunks (lv + 64#64) (count chunks ||| (count chunks - 1#64) >>> 63) ∧
      Quad m lv (count chunks) ∧ Region m lv 3520#64 := by
  obtain ⟨hn, hR, hq, hrest⟩ := h
  refine ⟨⟨hn, hR, hq, 0, chunks.size - 1, by omega, by simp, ?_, ?_, fun h0 => ⟨rfl, by omega⟩, fun hp => ?_⟩, hq, hR⟩
  · -- the count, or 1 where there is none
    by_cases h0 : chunks.size = 0
    · simp only [count, h0]; decide
    · rw [show chunks.size - 1 + 1 = chunks.size by omega]
      have hc : (count chunks).toNat = chunks.size := by simp only [count, BitVec.toNat_ofNat]; omega
      have h1 : count chunks ≠ 0#64 := by intro h; rw [h] at hc; simp at hc; omega
      have h2 : count chunks < 18014398509481984#64 := by bv_omega
      show count chunks ||| (count chunks - 1#64) >>> 63 = count chunks
      generalize count chunks = c at h1 h2
      bv_decide
  · have := pow_le_54 0; simp at this ⊢; omega
  · obtain ⟨hl, hc⟩ := hrest hp
    refine ⟨by simp; omega, by simpa using hl, by simpa using hc⟩

/-- A level's two values and the room above them, when the level is full (`x` even): what a turn reads. -/
theorem Mid.even {m : Mem} {lv src x flags : BitVec 64} {chunks : Array Blake3.Node} (h : Mid m lv k flags chunks src x)
    (hc : x &&& 1#64 = 0#64) :
    ∃ a c : Nat, a ≤ 52 ∧ src = lv + BitVec.ofNat 64 (64 * a + 64) ∧ x = BitVec.ofNat 64 (2 * c + 2) ∧ 2 * c + 2 < 2 ^ (54 - a) ∧
      chunks.size = (2 * c + 2) * 2 ^ a ∧
      Cv.At m src (Blake3.sub k ⟨flags.setWidth 32⟩ chunks (2 * c * 2 ^ a) (2 ^ a)) ∧
      Cv.At m (src + 32#64) (Blake3.sub k ⟨flags.setWidth 32⟩ chunks ((2 * c + 1) * 2 ^ a) (2 ^ a)) ∧
      Lev k ⟨flags.setWidth 32⟩ chunks m (53 - a) (src + 64#64) (2 ^ (a + 1)) c := by
  obtain ⟨hn, hR, hq, a, r, ha, hsrc, hx, hr, h0, h1⟩ := h
  have hodd : r % 2 = 1 := by
    have := even_ofNat (by rw [← hx]; exact hc)
    omega
  have hp : 0 < chunks.size := by
    rcases Nat.eq_zero_or_pos chunks.size with h | h
    · have := (h0 h).2; omega
    · exact h
  have ha' : a ≤ 52 := by
    rcases Nat.lt_or_ge a 53 with h | h
    · omega
    · have : a = 53 := by omega
      subst this
      simp at hr; omega
  obtain ⟨hsz, hl, hcv⟩ := h1 hp
  obtain ⟨c, rfl⟩ : ∃ c, r = 2 * c + 1 := ⟨r / 2, by omega⟩
  rw [show 54 - a = (53 - a) + 1 by omega, Lev_succ] at hl
  rw [place_odd hodd] at hcv
  refine ⟨a, c, ha', hsrc, by rw [hx], by omega, by rw [hsz], ?_, hcv, ?_⟩
  · have := hl.1 hodd
    rwa [show 2 * c + 1 - 1 = 2 * c by omega] at this
  · have := hl.2
    rwa [show (2 * c + 1) / 2 = c by omega, show 2 * 2 ^ a = 2 ^ (a + 1) by rw [Nat.pow_succ]; omega] at this

/-- **Before a turn:** the level's two values as the four vectors the code reads, and the room the turn
writes in. -/
theorem Mid.full {m : Mem} {lv src x flags : BitVec 64} {chunks : Array Blake3.Node} (h : Mid m lv k flags chunks src x)
    (hc : x &&& 1#64 = 0#64) :
    ∃ l0 l1 r0 r1 : V, Vec m src l0 ∧ Vec m (src + 16#64) l1 ∧ Vec m (src + 32#64) r0 ∧ Vec m (src + 48#64) r1 ∧
      Region m src 128#64 ∧ 64#64 ≤ src - lv ∧ src - lv ≤ 3392#64 ∧ x ≠ 0#64 := by
  have hR := h.2.1
  obtain ⟨a, c, ha, hsrc, hx, hr, _, ⟨l0, l1, hl0, hl1, _⟩, ⟨r0, r1, hr0, hr1, _⟩, _⟩ := Mid.even h hc
  have h54 := pow_le_54 a
  rw [show src + 32#64 + 16#64 = src + 48#64 by bv_decide] at hr1
  refine ⟨l0, l1, r0, r1, hl0, hl1, hr0, hr1, ?_, ?_, ?_, ?_⟩
  · rw [hsrc]; exact region_sub hR _ _ (by bv_omega)
  · subst hsrc; bv_omega
  · subst hsrc; bv_omega
  · subst hx; bv_omega

/-- **Across a turn:** the level's two values replaced, in the level above, by what the kernel leaves for
them: the loop's head again, one level up. -/
theorem Mid.carry {m m' : Mem} {lv src x flags : BitVec 64} {chunks : Array Blake3.Node} {k0 k1 l0 l1 r0 r1 : V}
    (h : Mid m lv k flags chunks src x) (hc : x &&& 1#64 = 0#64) (hk : words8 k0 k1 = k)
    (hl0 : Vec m src l0) (hl1 : Vec m (src + 16#64) l1) (hr0 : Vec m (src + 32#64) r0) (hr1 : Vec m (src + 48#64) r1)
    (hf : flags < 256#64)
    (hp0 : Vec m' (src + 64#64 + (x >>> 1 + 1#64 &&& 1#64) <<< 5)
      (Kernels.out k0 k1 l0 l1 r0 r1 0#64 64#32 (BitVec.setWidth 32 (BitVec.setWidth 8 (flags ||| 4#64)))).1)
    (hp1 : Vec m' (src + 64#64 + (x >>> 1 + 1#64 &&& 1#64) <<< 5 + 16#64)
      (Kernels.out k0 k1 l0 l1 r0 r1 0#64 64#32 (BitVec.setWidth 32 (BitVec.setWidth 8 (flags ||| 4#64)))).2)
    (hq : Quad m' lv (count chunks)) (hR : Region m' lv 3520#64)
    (same : ∀ y : BitVec 64, y - lv < 3520#64 → 32#64 ≤ y - (src + 64#64 + (x >>> 1 + 1#64 &&& 1#64) <<< 5) → m' y = m y) :
    Mid m' lv k flags chunks (src + 64#64) (x >>> 1) := by
  have hn := h.1
  obtain ⟨a, c, ha, hsrc, hx, hr, hsz, hleft, hright, hup⟩ := Mid.even h hc
  have h54 := pow_le_54 a
  -- the place the parent went to is the level above's next place
  have hx1 : x >>> 1 = BitVec.ofNat 64 (c + 1) := by subst hx; bv_omega
  have hpl : (x >>> 1 + 1#64 &&& 1#64) <<< 5 = place c := by
    rw [hx1, ← place_bits c, ← BitVec.ofNat_add, and_one_ofNat, and_one_ofNat, show (c + 1 + 1) % 2 = c % 2 by omega]
  rw [hpl] at hp0 hp1 same
  have hpl' : place c = 0#64 ∨ place c = 32#64 := by
    rcases Nat.mod_two_eq_zero_or_one c with h | h
    · exact Or.inl (place_even h)
    · exact Or.inr (place_odd h)
  -- what the kernel left is the subtree over both values' chunks
  have hparent : words8 (Kernels.out k0 k1 l0 l1 r0 r1 0#64 64#32 (BitVec.setWidth 32 (BitVec.setWidth 8 (flags ||| 4#64)))).1
      (Kernels.out k0 k1 l0 l1 r0 r1 0#64 64#32 (BitVec.setWidth 32 (BitVec.setWidth 8 (flags ||| 4#64)))).2
      = Blake3.sub k ⟨flags.setWidth 32⟩ chunks (c * 2 ^ (a + 1)) (2 ^ (a + 1)) := by
    rw [Merge.parent k0 k1 l0 l1 r0 r1 flags hf, hk, cv_same hleft hl0 hl1,
      cv_same hright hr0 (by rw [show src + 32#64 + 16#64 = src + 48#64 by bv_decide]; exact hr1),
      show (2 * c + 1) * 2 ^ a = 2 * c * 2 ^ a + 2 ^ a by rw [Nat.add_mul, Nat.one_mul], sub_pair,
      show 2 * c * 2 ^ a = c * 2 ^ (a + 1) by rw [Nat.pow_succ, Nat.mul_comm 2 c, Nat.mul_assoc, Nat.mul_comm 2 (2 ^ a)]]
  have hp : 0 < chunks.size := by rw [hsz]; exact Nat.mul_pos (by omega) (Nat.two_pow_pos a)
  have h2 : 2 ^ (54 - a) = 2 * 2 ^ (54 - (a + 1)) := by
    rw [show 54 - a = (54 - (a + 1)) + 1 by omega, Nat.pow_succ]; omega
  refine ⟨hn, hR, hq, a + 1, c, by omega, ?_, hx1, by omega, fun h0 => by omega, fun _ => ⟨?_, ?_, ?_⟩⟩
  · subst hsrc; bv_omega
  · rw [hsz, Nat.pow_succ, show 2 * c + 2 = (c + 1) * 2 by omega, Nat.mul_assoc, Nat.mul_comm 2 (2 ^ a)]
  · rw [show 54 - (a + 1) = 53 - a by omega]
    refine Lev.frame_but _ _ _ _ (by omega) (fun y hy hy' => same y ?_ hy') hup
    subst hsrc; bv_omega
  · exact ⟨_, _, hp0, hp1, hparent⟩

end Levels

/-- The new chunk's value at `cv`. (Its own name, so that the key's value and this one are told apart.) -/
def Ladd.New (m : Mem) (cv : BitVec 64) (new : Blake3.Node) : Prop := Cv.At m cv new.cv

theorem Ladd.New.intro {m : Mem} {cv : BitVec 64} {new : Blake3.Node} (h : Cv.At m cv new.cv) : Ladd.New m cv new := h

theorem Ladd.New.frame {m m' : Mem} {cv : BitVec 64} {new : Blake3.Node} (h : Ladd.New m cv new)
    (same : ∀ x : BitVec 64, x - cv < 32#64 → m' x = m x) : Ladd.New m' cv new := Cv.At.frame h same

theorem Ladd.New.vectors {m : Mem} {cv : BitVec 64} {new : Blake3.Node} (h : Ladd.New m cv new) :
    ∃ t0 t1 : V, Vec m cv t0 ∧ Vec m (cv + 16#64) t1 ∧ words8 t0 t1 = new.cv := h

open Levels in
/-- **When the loop ends:** the level the loop stopped at keeps its value, the new chunk's value goes to the
bottom's next place and the count is one more: the levels over the chunks and the new one. -/
theorem Ladd.exit {m m' : Mem} {lv src x flags : BitVec 64} {k : Blake3.CV} {chunks : Array Blake3.Node} {new : Blake3.Node} {t0 t1 : V}
    (h : Levels.Mid m lv k flags chunks src x) (hc : ¬ x &&& 1#64 = 0#64) (hn : chunks.size + 1 < 2 ^ 54)
    (hw : words8 t0 t1 = new.cv)
    (hp0 : Vec m' (lv + 64#64 + (Levels.count chunks &&& 1#64) <<< 5) t0)
    (hp1 : Vec m' (lv + 64#64 + (Levels.count chunks &&& 1#64) <<< 5 + 16#64) t1)
    (hq : Quad m' lv (Levels.count chunks + 1#64)) (hR : Region m' lv 3520#64)
    (same : ∀ y : BitVec 64, y - lv < 3520#64 → 8#64 ≤ y - lv → 32#64 ≤ y - (lv + 64#64 + (Levels.count chunks &&& 1#64) <<< 5) → m' y = m y) :
    (Levels.count chunks + 1#64).toNat = chunks.size + 1 ∧ Levels.At k ⟨flags.setWidth 32⟩ m' lv (chunks.push new) := by
  obtain ⟨_, _, _, a, r, ha, hsrc, hx, hr, h0, h1⟩ := h
  have heven : r % 2 = 0 := by
    have := odd_ofNat (by rw [← hx]; exact hc)
    omega
  have hcount : Levels.count chunks + 1#64 = BitVec.ofNat 64 (chunks.size + 1) := by
    simp only [Levels.count, BitVec.ofNat_add]
  rw [show (Levels.count chunks &&& 1#64) <<< 5 = place chunks.size from place_bits chunks.size] at hp0 hp1 same
  have hpl : place chunks.size = 0#64 ∨ place chunks.size = 32#64 := by
    rcases Nat.mod_two_eq_zero_or_one chunks.size with h | h
    · exact Or.inl (place_even h)
    · exact Or.inr (place_odd h)
  refine ⟨by rw [hcount, BitVec.toNat_ofNat]; omega, by rw [Array.size_push]; exact hn, hR, by rw [Array.size_push, ← hcount]; exact hq, fun _ => ?_⟩
  rw [Array.size_push, Nat.add_sub_cancel]
  refine ⟨?_, ⟨t0, t1, hp0, hp1, by rw [hw, sub_new]⟩⟩
  rcases Nat.eq_zero_or_pos chunks.size with hz | hp
  · rw [hz]; exact Lev_none m' _ _ _
  obtain ⟨hsz, hl, hcv⟩ := h1 hp
  have h54 := pow_le_54 a
  -- the level the loop stopped at has now received one more: the value that waited there
  have hl1 : Lev k ⟨flags.setWidth 32⟩ chunks m (54 - a) src (2 ^ a) (r + 1) := by
    rw [show 54 - a = (53 - a) + 1 by omega, Lev_succ] at hl ⊢
    refine ⟨fun _ => ?_, by rw [show (r + 1) / 2 = r / 2 by omega]; exact hl.2⟩
    rw [place_even heven, BitVec.add_zero] at hcv
    rwa [Nat.add_sub_cancel]
  -- the bytes written are not its bytes
  have hl2 : Lev k ⟨flags.setWidth 32⟩ chunks m' (54 - a) src (2 ^ a) (r + 1) := by
    refine Lev.frame_but _ _ _ _ (by omega) (fun y hy hy' => same y ?_ ?_ ?_) hl1
    · subst hsrc; bv_omega
    · subst hsrc; bv_omega
    · rcases Nat.eq_zero_or_pos a with ha0 | ha0
      · subst ha0
        have : chunks.size = r + 1 := by rw [hsz, Nat.pow_zero, Nat.mul_one]
        rw [this]
        subst hsrc
        exact hy'
      · have ho : (BitVec.ofNat 64 (64 * a + 64)).toNat = 64 * a + 64 := by rw [BitVec.toNat_ofNat]; omega
        subst hsrc
        generalize BitVec.ofNat 64 (64 * a + 64) = c at ho hy
        clear hy' hl1 hl hcv hsz hp0 hp1 same hq hR hw hx hc hr h0 h1
        rcases hpl with h | h <;> (rw [h]; bv_omega)
  rw [hsrc] at hl2
  have hl3 := Lev.below lv a (r + 1) (by omega) hl2
  rw [← hsz] at hl3
  exact Lev.push new 54 _ 1 chunks.size (by omega) (by omega) hl3
