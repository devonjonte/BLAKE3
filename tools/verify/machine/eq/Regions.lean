import Bytes

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
