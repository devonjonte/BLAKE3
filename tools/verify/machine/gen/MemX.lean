import X86
open X86

/-! What the x86-64 model's reads and writes do to words (Bytes.lean) and to the eight bytes of a stack slot. -/

theorem read_word {m : Mem} {a : BitVec 64} {w : BitVec 32} (h : Word m a w) :
    m.read a 32 = some (w.setWidth 64) := by
  obtain ⟨h0, h1, h2, h3⟩ := h
  simp only [Mem.read, Mem.read8, h0, h1, h2, h3, Option.map_some, Option.bind_eq_bind, Option.bind_some,
    Option.pure_def, Option.some.injEq, b0, b1, b2, b3]
  bv_decide

theorem write_word {m : Mem} {a : BitVec 64} {w : BitVec 32} (h : Word m a w) (v : BitVec 64) :
    m.write a v 32 = some (m.put32 a (v.setWidth 32)) := by
  obtain ⟨h0, h1, h2, h3⟩ := h
  have e0 : byte v 0 = b0 (v.setWidth 32) := by simp only [byte, b0]; bv_decide
  have e1 : byte v 1 = b1 (v.setWidth 32) := by simp only [byte, b1]; bv_decide
  have e2 : byte v 2 = b2 (v.setWidth 32) := by simp only [byte, b2]; bv_decide
  have e3 : byte v 3 = b3 (v.setWidth 32) := by simp only [byte, b3]; bv_decide
  simp_all [Mem.write, Mem.write8, Mem.put8, Mem.put32]

/-- The eight bytes at `a` are owned. -/
def Owned8 (m : Mem) (a : BitVec 64) : Prop :=
  (m a).isSome ∧ (m (a + 1)).isSome ∧ (m (a + 2)).isSome ∧ (m (a + 3)).isSome ∧
    (m (a + 4)).isSome ∧ (m (a + 5)).isSome ∧ (m (a + 6)).isSome ∧ (m (a + 7)).isSome

def Mem.put64 (m : Mem) (a : BitVec 64) (v : BitVec 64) : Mem :=
  (((((((m.put8 a (byte v 0)).put8 (a + 1) (byte v 1)).put8 (a + 2) (byte v 2)).put8 (a + 3) (byte v 3)).put8
    (a + 4) (byte v 4)).put8 (a + 5) (byte v 5)).put8 (a + 6) (byte v 6)).put8 (a + 7) (byte v 7)

theorem write_quad {m : Mem} {a : BitVec 64} (h : Owned8 m a) (v : BitVec 64) :
    m.write a v 64 = some (m.put64 a v) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := h
  simp_all [Mem.write, Mem.write8, Mem.put8, Mem.put64]

theorem read_put64 (m : Mem) (a v : BitVec 64) : (m.put64 a v).read a 64 = some v := by
  simp [Mem.read, Mem.read8, Mem.put64, Mem.put8, add_eq_add, self_eq_add, add_eq_self, byte]
  bv_decide

theorem put64_other (m : Mem) (a v x : BitVec 64) (h : 8 ≤ (x - a).toNat) : m.put64 a v x = m x := by
  have h0 : x ≠ a := by intro e; subst e; simp at h
  have h1 : x ≠ a + 1 := by intro e; subst e; revert h; bv_omega
  have h2 : x ≠ a + 2 := by intro e; subst e; revert h; bv_omega
  have h3 : x ≠ a + 3 := by intro e; subst e; revert h; bv_omega
  have h4 : x ≠ a + 4 := by intro e; subst e; revert h; bv_omega
  have h5 : x ≠ a + 5 := by intro e; subst e; revert h; bv_omega
  have h6 : x ≠ a + 6 := by intro e; subst e; revert h; bv_omega
  have h7 : x ≠ a + 7 := by intro e; subst e; revert h; bv_omega
  simp_all [Mem.put64, Mem.put8]

/-- A 64-bit read sees only its eight bytes. -/
theorem read_congr {m m' : Mem} (a : BitVec 64) (h : ∀ x, (x - a).toNat < 8 → m' x = m x) :
    m'.read a 64 = m.read a 64 := by
  simp only [Mem.read, Mem.read8]
  rw [h a (by bv_omega), h (a + 1) (by bv_omega), h (a + 2) (by bv_omega), h (a + 3) (by bv_omega),
    h (a + 4) (by bv_omega), h (a + 5) (by bv_omega), h (a + 6) (by bv_omega), h (a + 7) (by bv_omega)]

