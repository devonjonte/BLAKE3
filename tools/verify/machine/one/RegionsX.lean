import Machine
import MemLemmas
open X86

/-! # Regions: writes that a later read finds in one step

A memory after many writes is a long chain, and a read through it compares its address with
every one. Here the chain is kept apart by region: `over m base inside f` is `m` with the bytes
of one region (those at `base + d` with `inside d`) overlaid by `f`, a table from the offset `d`
to the byte last written there. A write into the region changes only `f`; a read elsewhere
passes the whole region in one step. -/

/-- A table of written bytes, by offset. -/
abbrev Written := BitVec 64 → Option (BitVec 8)

def none' : Written := fun _ => none

/-- One more byte written at offset `d`. -/
def upd (f : Written) (d : BitVec 64) (v : BitVec 8) : Written := fun x => if x = d then some v else f x

theorem upd_apply (f : Written) (d : BitVec 64) (v : BitVec 8) (x : BitVec 64) :
    upd f d v x = if x = d then some v else f x := rfl

theorem none_apply (x : BitVec 64) : none' x = none := rfl

/-- `m`, with the region's written bytes over it. -/
def over (m : Mem) (base : BitVec 64) (inside : BitVec 64 → Bool) (f : Written) : Mem :=
  fun x => if inside (x - base) then (f (x - base)).or (m x) else m x

theorem over_none (m : Mem) (base : BitVec 64) (inside : BitVec 64 → Bool) : over m base inside none' = m := by
  funext x; simp [over, none']

theorem add_sub_self (a d : BitVec 64) : a + d - a = d := by bv_decide

/-- A read inside the region: the byte last written there, or the one below. -/
theorem over_in (m : Mem) (base : BitVec 64) (inside : BitVec 64 → Bool) (f : Written) (d : BitVec 64)
    (h : inside d = true) : over m base inside f (base + d) = (f d).or (m (base + d)) := by
  simp [over, add_sub_self, h]

/-- A read outside it: the memory below. -/
theorem over_out (m : Mem) (base : BitVec 64) (inside : BitVec 64 → Bool) (f : Written) (x : BitVec 64)
    (h : inside (x - base) = false) : over m base inside f x = m x := by
  simp [over, h]

/-- A write inside the region changes its table only. -/
theorem put8_over_in (m : Mem) (base : BitVec 64) (inside : BitVec 64 → Bool) (f : Written) (d : BitVec 64) (v : BitVec 8)
    (h : inside d = true) : (over m base inside f).put8 (base + d) v = over m base inside (upd f d v) := by
  funext x
  by_cases hx : x = base + d
  · subst hx; simp [Mem.put8, over, upd, add_sub_self, h]
  · have : x - base ≠ d := fun e => hx (by rw [← e]; bv_decide)
    simp [Mem.put8, over, upd, hx, this]

/-- A write outside the region goes to the memory below. -/
theorem put8_over_out (m : Mem) (base : BitVec 64) (inside : BitVec 64 → Bool) (f : Written) (a : BitVec 64) (v : BitVec 8)
    (h : inside (a - base) = false) : (over m base inside f).put8 a v = over (m.put8 a v) base inside f := by
  funext x
  by_cases hx : x = a
  · subst hx; simp [Mem.put8, over, h]
  · simp [Mem.put8, over, hx]

/-! ## Whole reads and writes outside a region go to the memory below -/

theorem over_read128 (b : Mem) (base : BitVec 64) (inside : BitVec 64 → Bool) (f : Written) (a : BitVec 64)
    (hout : ∀ x, (x - a).toNat < 16 → inside (x - base) = false) : (over b base inside f).read128 a = b.read128 a :=
  read128_congr (m := b) a (fun x hx => over_out _ _ _ _ x (hout x hx))

theorem over_read64 (b : Mem) (base : BitVec 64) (inside : BitVec 64 → Bool) (f : Written) (a : BitVec 64)
    (hout : ∀ x, (x - a).toNat < 8 → inside (x - base) = false) : (over b base inside f).read a 64 = b.read a 64 :=
  read_congr (m := b) a (fun x hx => over_out _ _ _ _ x (hout x hx))

theorem over_read8 (b : Mem) (base : BitVec 64) (inside : BitVec 64 → Bool) (f : Written) (a : BitVec 64)
    (hout : inside (a - base) = false) : (over b base inside f).read a 8 = b.read a 8 := by
  simp only [Mem.read, Mem.read8, over_out _ _ _ _ _ hout]

/-- Inside its sixteen bytes a `put128` does not depend on the memory under it. -/
theorem put128_in (m m' : Mem) (a : BitVec 64) (v : V) (x : BitVec 64) (hx : (x - a).toNat < 16) :
    m.put128 a v x = m'.put128 a v x := by
  have hk : (x - a).toNat = 0 ∨ (x - a).toNat = 1 ∨ (x - a).toNat = 2 ∨ (x - a).toNat = 3 ∨ (x - a).toNat = 4 ∨ (x - a).toNat = 5 ∨ (x - a).toNat = 6 ∨ (x - a).toNat = 7 ∨ (x - a).toNat = 8 ∨ (x - a).toNat = 9 ∨ (x - a).toNat = 10 ∨ (x - a).toNat = 11 ∨ (x - a).toNat = 12 ∨ (x - a).toNat = 13 ∨ (x - a).toNat = 14 ∨ (x - a).toNat = 15 := by omega
  rcases hk with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · have e : x = a + 0 := by bv_omega
    subst e; exact ((vec_put128 m a v).1).trans ((vec_put128 m' a v).1).symm
  · have e : x = a + 1 := by bv_omega
    subst e; exact ((vec_put128 m a v).2.1).trans ((vec_put128 m' a v).2.1).symm
  · have e : x = a + 2 := by bv_omega
    subst e; exact ((vec_put128 m a v).2.2.1).trans ((vec_put128 m' a v).2.2.1).symm
  · have e : x = a + 3 := by bv_omega
    subst e; exact ((vec_put128 m a v).2.2.2.1).trans ((vec_put128 m' a v).2.2.2.1).symm
  · have e : x = a + 4 := by bv_omega
    subst e; exact ((vec_put128 m a v).2.2.2.2.1).trans ((vec_put128 m' a v).2.2.2.2.1).symm
  · have e : x = a + 5 := by bv_omega
    subst e; exact ((vec_put128 m a v).2.2.2.2.2.1).trans ((vec_put128 m' a v).2.2.2.2.2.1).symm
  · have e : x = a + 6 := by bv_omega
    subst e; exact ((vec_put128 m a v).2.2.2.2.2.2.1).trans ((vec_put128 m' a v).2.2.2.2.2.2.1).symm
  · have e : x = a + 7 := by bv_omega
    subst e; exact ((vec_put128 m a v).2.2.2.2.2.2.2.1).trans ((vec_put128 m' a v).2.2.2.2.2.2.2.1).symm
  · have e : x = a + 8 := by bv_omega
    subst e; exact ((vec_put128 m a v).2.2.2.2.2.2.2.2.1).trans ((vec_put128 m' a v).2.2.2.2.2.2.2.2.1).symm
  · have e : x = a + 9 := by bv_omega
    subst e; exact ((vec_put128 m a v).2.2.2.2.2.2.2.2.2.1).trans ((vec_put128 m' a v).2.2.2.2.2.2.2.2.2.1).symm
  · have e : x = a + 10 := by bv_omega
    subst e; exact ((vec_put128 m a v).2.2.2.2.2.2.2.2.2.2.1).trans ((vec_put128 m' a v).2.2.2.2.2.2.2.2.2.2.1).symm
  · have e : x = a + 11 := by bv_omega
    subst e; exact ((vec_put128 m a v).2.2.2.2.2.2.2.2.2.2.2.1).trans ((vec_put128 m' a v).2.2.2.2.2.2.2.2.2.2.2.1).symm
  · have e : x = a + 12 := by bv_omega
    subst e; exact ((vec_put128 m a v).2.2.2.2.2.2.2.2.2.2.2.2.1).trans ((vec_put128 m' a v).2.2.2.2.2.2.2.2.2.2.2.2.1).symm
  · have e : x = a + 13 := by bv_omega
    subst e; exact ((vec_put128 m a v).2.2.2.2.2.2.2.2.2.2.2.2.2.1).trans ((vec_put128 m' a v).2.2.2.2.2.2.2.2.2.2.2.2.2.1).symm
  · have e : x = a + 14 := by bv_omega
    subst e; exact ((vec_put128 m a v).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).trans ((vec_put128 m' a v).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).symm
  · have e : x = a + 15 := by bv_omega
    subst e; exact ((vec_put128 m a v).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2).trans ((vec_put128 m' a v).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2).symm

theorem put64_in (m m' : Mem) (a : BitVec 64) (v : BitVec 64) (x : BitVec 64) (hx : (x - a).toNat < 8) :
    m.put64 a v x = m'.put64 a v x := by
  have hk : (x - a).toNat = 0 ∨ (x - a).toNat = 1 ∨ (x - a).toNat = 2 ∨ (x - a).toNat = 3 ∨ (x - a).toNat = 4 ∨ (x - a).toNat = 5 ∨ (x - a).toNat = 6 ∨ (x - a).toNat = 7 := by omega
  rcases hk with h | h | h | h | h | h | h | h
  · have e : x = a + 0 := by bv_omega
    subst e; exact ((quad_put64 m a v).1).trans ((quad_put64 m' a v).1).symm
  · have e : x = a + 1 := by bv_omega
    subst e; exact ((quad_put64 m a v).2.1).trans ((quad_put64 m' a v).2.1).symm
  · have e : x = a + 2 := by bv_omega
    subst e; exact ((quad_put64 m a v).2.2.1).trans ((quad_put64 m' a v).2.2.1).symm
  · have e : x = a + 3 := by bv_omega
    subst e; exact ((quad_put64 m a v).2.2.2.1).trans ((quad_put64 m' a v).2.2.2.1).symm
  · have e : x = a + 4 := by bv_omega
    subst e; exact ((quad_put64 m a v).2.2.2.2.1).trans ((quad_put64 m' a v).2.2.2.2.1).symm
  · have e : x = a + 5 := by bv_omega
    subst e; exact ((quad_put64 m a v).2.2.2.2.2.1).trans ((quad_put64 m' a v).2.2.2.2.2.1).symm
  · have e : x = a + 6 := by bv_omega
    subst e; exact ((quad_put64 m a v).2.2.2.2.2.2.1).trans ((quad_put64 m' a v).2.2.2.2.2.2.1).symm
  · have e : x = a + 7 := by bv_omega
    subst e; exact ((quad_put64 m a v).2.2.2.2.2.2.2).trans ((quad_put64 m' a v).2.2.2.2.2.2.2).symm

theorem over_put128 (b : Mem) (base : BitVec 64) (inside : BitVec 64 → Bool) (f : Written) (a : BitVec 64) (v : V)
    (hout : ∀ x, (x - a).toNat < 16 → inside (x - base) = false) :
    (over b base inside f).put128 a v = over (b.put128 a v) base inside f := by
  funext x
  by_cases hx : (x - a).toNat < 16
  · rw [over_out _ _ _ _ x (hout x hx)]; exact put128_in _ _ _ _ _ hx
  · rw [put128_other _ _ _ _ (by omega)]
    simp only [over]
    rw [put128_other _ _ _ _ (by omega)]

theorem over_put64 (b : Mem) (base : BitVec 64) (inside : BitVec 64 → Bool) (f : Written) (a v : BitVec 64)
    (hout : ∀ x, (x - a).toNat < 8 → inside (x - base) = false) :
    (over b base inside f).put64 a v = over (b.put64 a v) base inside f := by
  funext x
  by_cases hx : (x - a).toNat < 8
  · rw [over_out _ _ _ _ x (hout x hx)]; exact put64_in _ _ _ _ _ hx
  · rw [put64_other _ _ _ _ (by omega)]
    simp only [over]
    rw [put64_other _ _ _ _ (by omega)]

theorem over_write128 (b : Mem) (base : BitVec 64) (inside : BitVec 64 → Bool) (f : Written) (a : BitVec 64) (v : V)
    (ho : Owned16 b a) (hout : ∀ x, (x - a).toNat < 16 → inside (x - base) = false) :
    (over b base inside f).write128 a v = some (over (b.put128 a v) base inside f) := by
  rw [write_vec (owned16_congr (fun x hx => over_out _ _ _ _ x (hout x hx)) ho), over_put128 _ _ _ _ _ _ hout]

theorem over_write64 (b : Mem) (base : BitVec 64) (inside : BitVec 64 → Bool) (f : Written) (a v : BitVec 64)
    (ho : Owned8 b a) (hout : ∀ x, (x - a).toNat < 8 → inside (x - base) = false) :
    (over b base inside f).write a v 64 = some (over (b.put64 a v) base inside f) := by
  rw [write_quad (owned8_congr (fun x hx => over_out _ _ _ _ x (hout x hx)) ho), over_put64 _ _ _ _ _ _ hout]
