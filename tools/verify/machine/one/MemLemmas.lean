import Machine
open X86

/-! Bytes, quadwords and vectors in memory, for proofs: what a read or a write does where the
bytes are owned, and what it leaves alone. -/

namespace X86

theorem add_eq_add (a c d : BitVec 64) : (a + c = a + d) = (c = d) :=
  propext ⟨fun h => by bv_decide, fun h => by bv_decide⟩
theorem add_zero' (a : BitVec 64) : a + 0 = a := by bv_decide

/-- The sixteen bytes at `a` are owned. -/
def Owned16 (m : Mem) (a : BitVec 64) : Prop := (m (a + 0)).isSome ∧ (m (a + 1)).isSome ∧ (m (a + 2)).isSome ∧ (m (a + 3)).isSome ∧ (m (a + 4)).isSome ∧ (m (a + 5)).isSome ∧ (m (a + 6)).isSome ∧ (m (a + 7)).isSome ∧ (m (a + 8)).isSome ∧ (m (a + 9)).isSome ∧ (m (a + 10)).isSome ∧ (m (a + 11)).isSome ∧ (m (a + 12)).isSome ∧ (m (a + 13)).isSome ∧ (m (a + 14)).isSome ∧ (m (a + 15)).isSome

/-- The sixteen bytes at `a` are owned and hold `v`. -/
def Vec (m : Mem) (a : BitVec 64) (v : V) : Prop := m (a + 0) = some (by8 v 0) ∧ m (a + 1) = some (by8 v 1) ∧ m (a + 2) = some (by8 v 2) ∧ m (a + 3) = some (by8 v 3) ∧ m (a + 4) = some (by8 v 4) ∧ m (a + 5) = some (by8 v 5) ∧ m (a + 6) = some (by8 v 6) ∧ m (a + 7) = some (by8 v 7) ∧ m (a + 8) = some (by8 v 8) ∧ m (a + 9) = some (by8 v 9) ∧ m (a + 10) = some (by8 v 10) ∧ m (a + 11) = some (by8 v 11) ∧ m (a + 12) = some (by8 v 12) ∧ m (a + 13) = some (by8 v 13) ∧ m (a + 14) = some (by8 v 14) ∧ m (a + 15) = some (by8 v 15)

/-- The eight bytes at `a` are owned. -/
def Owned8 (m : Mem) (a : BitVec 64) : Prop := (m (a + 0)).isSome ∧ (m (a + 1)).isSome ∧ (m (a + 2)).isSome ∧ (m (a + 3)).isSome ∧ (m (a + 4)).isSome ∧ (m (a + 5)).isSome ∧ (m (a + 6)).isSome ∧ (m (a + 7)).isSome

/-- The eight bytes at `a` are owned and hold `v`. -/
def Quad (m : Mem) (a : BitVec 64) (v : BitVec 64) : Prop := m (a + 0) = some (byte v 0) ∧ m (a + 1) = some (byte v 1) ∧ m (a + 2) = some (byte v 2) ∧ m (a + 3) = some (byte v 3) ∧ m (a + 4) = some (byte v 4) ∧ m (a + 5) = some (byte v 5) ∧ m (a + 6) = some (byte v 6) ∧ m (a + 7) = some (byte v 7)

def Mem.put128 (m : Mem) (a : BitVec 64) (v : V) : Mem := ((((((((((((((((m.put8 (a + 0) (by8 v 0)).put8 (a + 1) (by8 v 1)).put8 (a + 2) (by8 v 2)).put8 (a + 3) (by8 v 3)).put8 (a + 4) (by8 v 4)).put8 (a + 5) (by8 v 5)).put8 (a + 6) (by8 v 6)).put8 (a + 7) (by8 v 7)).put8 (a + 8) (by8 v 8)).put8 (a + 9) (by8 v 9)).put8 (a + 10) (by8 v 10)).put8 (a + 11) (by8 v 11)).put8 (a + 12) (by8 v 12)).put8 (a + 13) (by8 v 13)).put8 (a + 14) (by8 v 14)).put8 (a + 15) (by8 v 15))
def Mem.put64 (m : Mem) (a : BitVec 64) (v : BitVec 64) : Mem := ((((((((m.put8 (a + 0) (byte v 0)).put8 (a + 1) (byte v 1)).put8 (a + 2) (byte v 2)).put8 (a + 3) (byte v 3)).put8 (a + 4) (byte v 4)).put8 (a + 5) (byte v 5)).put8 (a + 6) (byte v 6)).put8 (a + 7) (byte v 7))

theorem vec_owned {m : Mem} {a : BitVec 64} {v : V} (h : Vec m a v) : Owned16 m a := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := h
  exact ⟨by rw [h0]; rfl, by rw [h1]; rfl, by rw [h2]; rfl, by rw [h3]; rfl, by rw [h4]; rfl, by rw [h5]; rfl, by rw [h6]; rfl, by rw [h7]; rfl, by rw [h8]; rfl, by rw [h9]; rfl, by rw [h10]; rfl, by rw [h11]; rfl, by rw [h12]; rfl, by rw [h13]; rfl, by rw [h14]; rfl, by rw [h15]; rfl⟩

theorem quad_owned {m : Mem} {a : BitVec 64} {v : BitVec 64} (h : Quad m a v) : Owned8 m a := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨by rw [h0]; rfl, by rw [h1]; rfl, by rw [h2]; rfl, by rw [h3]; rfl, by rw [h4]; rfl, by rw [h5]; rfl, by rw [h6]; rfl, by rw [h7]; rfl⟩

theorem read_vec {m : Mem} {a : BitVec 64} {v : V} (h : Vec m a v) : m.read128 a = some v := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := h
  simp only [Mem.read128, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq, by8,
    Nat.reduceMul]
  bv_decide

theorem write_vec {m : Mem} {a : BitVec 64} (o : Owned16 m a) (v : V) : m.write128 a v = some (m.put128 a v) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := o
  simp_all [Mem.write128, Mem.write8, Mem.put8, Mem.put128, add_eq_add]

theorem vec_put128 (m : Mem) (a : BitVec 64) (v : V) : Vec (m.put128 a v) a v := by
  simp [Vec, Mem.put128, Mem.put8, add_eq_add]

theorem put8_other (m : Mem) (a : BitVec 64) (b : BitVec 8) (x : BitVec 64) (h : x ≠ a) : m.put8 a b x = m x := by
  simp [Mem.put8, h]

theorem put128_other (m : Mem) (a : BitVec 64) (v : V) (x : BitVec 64) (h : 16 ≤ (x - a).toNat) : m.put128 a v x = m x := by
  simp only [Mem.put128]
  rw [put8_other _ _ _ _ (by intro e; subst e; revert h; bv_omega), put8_other _ _ _ _ (by intro e; subst e; revert h; bv_omega), put8_other _ _ _ _ (by intro e; subst e; revert h; bv_omega), put8_other _ _ _ _ (by intro e; subst e; revert h; bv_omega), put8_other _ _ _ _ (by intro e; subst e; revert h; bv_omega), put8_other _ _ _ _ (by intro e; subst e; revert h; bv_omega), put8_other _ _ _ _ (by intro e; subst e; revert h; bv_omega), put8_other _ _ _ _ (by intro e; subst e; revert h; bv_omega), put8_other _ _ _ _ (by intro e; subst e; revert h; bv_omega), put8_other _ _ _ _ (by intro e; subst e; revert h; bv_omega), put8_other _ _ _ _ (by intro e; subst e; revert h; bv_omega), put8_other _ _ _ _ (by intro e; subst e; revert h; bv_omega), put8_other _ _ _ _ (by intro e; subst e; revert h; bv_omega), put8_other _ _ _ _ (by intro e; subst e; revert h; bv_omega), put8_other _ _ _ _ (by intro e; subst e; revert h; bv_omega), put8_other _ _ _ _ (by intro e; subst e; revert h; bv_omega)]

theorem put8_isSome (m : Mem) (a : BitVec 64) (v : BitVec 8) (x : BitVec 64) (h : (m x).isSome) : (m.put8 a v x).isSome := by
  simp only [Mem.put8]; split <;> simp_all

theorem put128_isSome (m : Mem) (a : BitVec 64) (v : V) (x : BitVec 64) (h : (m x).isSome) : (m.put128 a v x).isSome := by
  simp only [Mem.put128]
  exact (put8_isSome _ _ _ _ (put8_isSome _ _ _ _ (put8_isSome _ _ _ _ (put8_isSome _ _ _ _ (put8_isSome _ _ _ _ (put8_isSome _ _ _ _ (put8_isSome _ _ _ _ (put8_isSome _ _ _ _ (put8_isSome _ _ _ _ (put8_isSome _ _ _ _ (put8_isSome _ _ _ _ (put8_isSome _ _ _ _ (put8_isSome _ _ _ _ (put8_isSome _ _ _ _ (put8_isSome _ _ _ _ (put8_isSome _ _ _ _ h))))))))))))))))

theorem read_quad {m : Mem} {a : BitVec 64} {v : BitVec 64} (h : Quad m a v) : m.read a 64 = some v := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := h
  simp only [add_zero'] at h0
  simp only [Mem.read, Mem.read8, h0, h1, h2, h3, h4, h5, h6, h7, Option.map_some, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
    Option.some.injEq, byte, Nat.reduceMul]
  bv_decide

theorem write_quad {m : Mem} {a : BitVec 64} (o : Owned8 m a) (v : BitVec 64) : m.write a v 64 = some (m.put64 a v) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := o
  simp only [add_zero'] at h0
  simp_all [Mem.write, Mem.write8, Mem.put8, Mem.put64, add_eq_add, add_zero']

theorem quad_put64 (m : Mem) (a v : BitVec 64) : Quad (m.put64 a v) a v := by
  simp [Quad, Mem.put64, Mem.put8, add_eq_add]

theorem put64_other (m : Mem) (a v x : BitVec 64) (h : 8 ≤ (x - a).toNat) : m.put64 a v x = m x := by
  simp only [Mem.put64]
  rw [put8_other _ _ _ _ (by intro e; subst e; revert h; bv_omega), put8_other _ _ _ _ (by intro e; subst e; revert h; bv_omega), put8_other _ _ _ _ (by intro e; subst e; revert h; bv_omega), put8_other _ _ _ _ (by intro e; subst e; revert h; bv_omega), put8_other _ _ _ _ (by intro e; subst e; revert h; bv_omega), put8_other _ _ _ _ (by intro e; subst e; revert h; bv_omega), put8_other _ _ _ _ (by intro e; subst e; revert h; bv_omega), put8_other _ _ _ _ (by intro e; subst e; revert h; bv_omega)]

theorem put64_isSome (m : Mem) (a v x : BitVec 64) (h : (m x).isSome) : (m.put64 a v x).isSome := by
  simp only [Mem.put64]
  exact (put8_isSome _ _ _ _ (put8_isSome _ _ _ _ (put8_isSome _ _ _ _ (put8_isSome _ _ _ _ (put8_isSome _ _ _ _ (put8_isSome _ _ _ _ (put8_isSome _ _ _ _ (put8_isSome _ _ _ _ h))))))))

theorem owned16_put128 (m : Mem) (a b : BitVec 64) (v : V) (o : Owned16 m b) : Owned16 (m.put128 a v) b := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := o
  exact ⟨put128_isSome _ _ _ _ h0, put128_isSome _ _ _ _ h1, put128_isSome _ _ _ _ h2, put128_isSome _ _ _ _ h3, put128_isSome _ _ _ _ h4, put128_isSome _ _ _ _ h5, put128_isSome _ _ _ _ h6, put128_isSome _ _ _ _ h7, put128_isSome _ _ _ _ h8, put128_isSome _ _ _ _ h9, put128_isSome _ _ _ _ h10, put128_isSome _ _ _ _ h11, put128_isSome _ _ _ _ h12, put128_isSome _ _ _ _ h13, put128_isSome _ _ _ _ h14, put128_isSome _ _ _ _ h15⟩

/-- A 64-bit read sees only its eight bytes. -/
theorem read_congr {m m' : Mem} (a : BitVec 64) (h : ∀ x, (x - a).toNat < 8 → m' x = m x) :
    m'.read a 64 = m.read a 64 := by
  simp only [Mem.read, Mem.read8]
  rw [h a (by bv_omega), h (a + 1) (by bv_omega), h (a + 2) (by bv_omega), h (a + 3) (by bv_omega),
    h (a + 4) (by bv_omega), h (a + 5) (by bv_omega), h (a + 6) (by bv_omega), h (a + 7) (by bv_omega)]

/-- Two regions of memory share no byte: `n` bytes at `a`, `k` bytes at `b`. -/
def Apart (a : BitVec 64) (n : Nat) (b : BitVec 64) (k : Nat) : Prop := k ≤ (a - b).toNat ∧ n ≤ (b - a).toNat

theorem put64_eq (m : Mem) (a v x : BitVec 64) : m.put64 a v x =
    if (x - a).toNat < 8 then (m.put64 a v x) else m x := by
  split
  · rfl
  · exact put64_other _ _ _ _ (by omega)

theorem owned16_put64 (m : Mem) (a b v : BitVec 64) (o : Owned16 m b) : Owned16 (m.put64 a v) b := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := o
  exact ⟨put64_isSome _ _ _ _ h0, put64_isSome _ _ _ _ h1, put64_isSome _ _ _ _ h2, put64_isSome _ _ _ _ h3, put64_isSome _ _ _ _ h4, put64_isSome _ _ _ _ h5, put64_isSome _ _ _ _ h6, put64_isSome _ _ _ _ h7, put64_isSome _ _ _ _ h8, put64_isSome _ _ _ _ h9, put64_isSome _ _ _ _ h10, put64_isSome _ _ _ _ h11, put64_isSome _ _ _ _ h12, put64_isSome _ _ _ _ h13, put64_isSome _ _ _ _ h14, put64_isSome _ _ _ _ h15⟩

theorem owned16_put8 (m : Mem) (a b : BitVec 64) (v : BitVec 8) (o : Owned16 m b) : Owned16 (m.put8 a v) b := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := o
  exact ⟨put8_isSome _ _ _ _ h0, put8_isSome _ _ _ _ h1, put8_isSome _ _ _ _ h2, put8_isSome _ _ _ _ h3, put8_isSome _ _ _ _ h4, put8_isSome _ _ _ _ h5, put8_isSome _ _ _ _ h6, put8_isSome _ _ _ _ h7, put8_isSome _ _ _ _ h8, put8_isSome _ _ _ _ h9, put8_isSome _ _ _ _ h10, put8_isSome _ _ _ _ h11, put8_isSome _ _ _ _ h12, put8_isSome _ _ _ _ h13, put8_isSome _ _ _ _ h14, put8_isSome _ _ _ _ h15⟩

theorem owned8_put128 (m : Mem) (a b : BitVec 64) (v : V) (o : Owned8 m b) : Owned8 (m.put128 a v) b := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := o
  exact ⟨put128_isSome _ _ _ _ h0, put128_isSome _ _ _ _ h1, put128_isSome _ _ _ _ h2, put128_isSome _ _ _ _ h3, put128_isSome _ _ _ _ h4, put128_isSome _ _ _ _ h5, put128_isSome _ _ _ _ h6, put128_isSome _ _ _ _ h7⟩

theorem owned8_put64 (m : Mem) (a b v : BitVec 64) (o : Owned8 m b) : Owned8 (m.put64 a v) b := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := o
  exact ⟨put64_isSome _ _ _ _ h0, put64_isSome _ _ _ _ h1, put64_isSome _ _ _ _ h2, put64_isSome _ _ _ _ h3, put64_isSome _ _ _ _ h4, put64_isSome _ _ _ _ h5, put64_isSome _ _ _ _ h6, put64_isSome _ _ _ _ h7⟩

theorem owned8_put8 (m : Mem) (a b : BitVec 64) (v : BitVec 8) (o : Owned8 m b) : Owned8 (m.put8 a v) b := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := o
  exact ⟨put8_isSome _ _ _ _ h0, put8_isSome _ _ _ _ h1, put8_isSome _ _ _ _ h2, put8_isSome _ _ _ _ h3, put8_isSome _ _ _ _ h4, put8_isSome _ _ _ _ h5, put8_isSome _ _ _ _ h6, put8_isSome _ _ _ _ h7⟩

/-- One byte written where it is owned. -/
theorem write_byte {m : Mem} {a : BitVec 64} (o : (m a).isSome) (v : BitVec 64) : m.write a v 8 = some (m.put8 a (byte v 0)) := by
  simp [Mem.write, Mem.write8, o]

/-- One byte read. -/
theorem read_byte {m : Mem} {a : BitVec 64} {b : BitVec 8} (h : m a = some b) : m.read a 8 = some (b.setWidth 64) := by
  simp [Mem.read, Mem.read8, h]

/-- A vector read sees only its sixteen bytes. -/
theorem read128_congr {m m' : Mem} (a : BitVec 64) (h : ∀ x, (x - a).toNat < 16 → m' x = m x) :
    m'.read128 a = m.read128 a := by
  simp only [Mem.read128]
  rw [h (a + 0) (by bv_omega), h (a + 1) (by bv_omega), h (a + 2) (by bv_omega), h (a + 3) (by bv_omega), h (a + 4) (by bv_omega), h (a + 5) (by bv_omega), h (a + 6) (by bv_omega), h (a + 7) (by bv_omega), h (a + 8) (by bv_omega), h (a + 9) (by bv_omega), h (a + 10) (by bv_omega), h (a + 11) (by bv_omega), h (a + 12) (by bv_omega), h (a + 13) (by bv_omega), h (a + 14) (by bv_omega), h (a + 15) (by bv_omega)]

/-- A vector in memory is still there in a memory that agrees on its sixteen bytes. -/
theorem vec_congr {m m' : Mem} {a : BitVec 64} {v : V} (h : ∀ x, (x - a).toNat < 16 → m' x = m x) (hv : Vec m a v) : Vec m' a v := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := hv
  exact ⟨by rw [h (a + 0) (by bv_omega)]; exact h0, by rw [h (a + 1) (by bv_omega)]; exact h1, by rw [h (a + 2) (by bv_omega)]; exact h2, by rw [h (a + 3) (by bv_omega)]; exact h3, by rw [h (a + 4) (by bv_omega)]; exact h4, by rw [h (a + 5) (by bv_omega)]; exact h5, by rw [h (a + 6) (by bv_omega)]; exact h6, by rw [h (a + 7) (by bv_omega)]; exact h7, by rw [h (a + 8) (by bv_omega)]; exact h8, by rw [h (a + 9) (by bv_omega)]; exact h9, by rw [h (a + 10) (by bv_omega)]; exact h10, by rw [h (a + 11) (by bv_omega)]; exact h11, by rw [h (a + 12) (by bv_omega)]; exact h12, by rw [h (a + 13) (by bv_omega)]; exact h13, by rw [h (a + 14) (by bv_omega)]; exact h14, by rw [h (a + 15) (by bv_omega)]; exact h15⟩

theorem owned16_congr {m m' : Mem} {a : BitVec 64} (h : ∀ x, (x - a).toNat < 16 → m' x = m x) (o : Owned16 m a) : Owned16 m' a := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := o
  exact ⟨by rw [h (a + 0) (by bv_omega)]; exact h0, by rw [h (a + 1) (by bv_omega)]; exact h1, by rw [h (a + 2) (by bv_omega)]; exact h2, by rw [h (a + 3) (by bv_omega)]; exact h3, by rw [h (a + 4) (by bv_omega)]; exact h4, by rw [h (a + 5) (by bv_omega)]; exact h5, by rw [h (a + 6) (by bv_omega)]; exact h6, by rw [h (a + 7) (by bv_omega)]; exact h7, by rw [h (a + 8) (by bv_omega)]; exact h8, by rw [h (a + 9) (by bv_omega)]; exact h9, by rw [h (a + 10) (by bv_omega)]; exact h10, by rw [h (a + 11) (by bv_omega)]; exact h11, by rw [h (a + 12) (by bv_omega)]; exact h12, by rw [h (a + 13) (by bv_omega)]; exact h13, by rw [h (a + 14) (by bv_omega)]; exact h14, by rw [h (a + 15) (by bv_omega)]; exact h15⟩

theorem quad_congr {m m' : Mem} {a v : BitVec 64} (h : ∀ x, (x - a).toNat < 8 → m' x = m x) (hq : Quad m a v) : Quad m' a v := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := hq
  exact ⟨by rw [h (a + 0) (by bv_omega)]; exact h0, by rw [h (a + 1) (by bv_omega)]; exact h1, by rw [h (a + 2) (by bv_omega)]; exact h2, by rw [h (a + 3) (by bv_omega)]; exact h3, by rw [h (a + 4) (by bv_omega)]; exact h4, by rw [h (a + 5) (by bv_omega)]; exact h5, by rw [h (a + 6) (by bv_omega)]; exact h6, by rw [h (a + 7) (by bv_omega)]; exact h7⟩

theorem owned8_congr {m m' : Mem} {a : BitVec 64} (h : ∀ x, (x - a).toNat < 8 → m' x = m x) (o : Owned8 m a) : Owned8 m' a := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := o
  exact ⟨by rw [h (a + 0) (by bv_omega)]; exact h0, by rw [h (a + 1) (by bv_omega)]; exact h1, by rw [h (a + 2) (by bv_omega)]; exact h2, by rw [h (a + 3) (by bv_omega)]; exact h3, by rw [h (a + 4) (by bv_omega)]; exact h4, by rw [h (a + 5) (by bv_omega)]; exact h5, by rw [h (a + 6) (by bv_omega)]; exact h6, by rw [h (a + 7) (by bv_omega)]; exact h7⟩

/-- A byte put somewhere else. -/
theorem put8_far (m : Mem) (a : BitVec 64) (b : BitVec 8) (x : BitVec 64) (h : 1 ≤ (x - a).toNat) : m.put8 a b x = m x :=
  put8_other _ _ _ _ (by intro e; subst e; revert h; bv_omega)

theorem put8_same (m : Mem) (a : BitVec 64) (b : BitVec 8) : m.put8 a b a = some b := by simp [Mem.put8]

theorem owned16_mono {m m' : Mem} (h : ∀ x, (m x).isSome → (m' x).isSome) {a : BitVec 64} (o : Owned16 m a) : Owned16 m' a := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := o
  exact ⟨h _ h0, h _ h1, h _ h2, h _ h3, h _ h4, h _ h5, h _ h6, h _ h7, h _ h8, h _ h9, h _ h10, h _ h11, h _ h12, h _ h13, h _ h14, h _ h15⟩

theorem owned8_mono {m m' : Mem} (h : ∀ x, (m x).isSome → (m' x).isSome) {a : BitVec 64} (o : Owned8 m a) : Owned8 m' a := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := o
  exact ⟨h _ h0, h _ h1, h _ h2, h _ h3, h _ h4, h _ h5, h _ h6, h _ h7⟩

end X86
