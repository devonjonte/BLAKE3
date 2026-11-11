import A64
open A64

/-! Words in memory, for proofs: what a 32-bit or 64-bit read and write do where the bytes are owned. -/

namespace A64

theorem add_eq_add (a c d : BitVec 64) : (a + c = a + d) = (c = d) :=
  propext ⟨fun h => by bv_decide, fun h => by bv_decide⟩
theorem self_eq_add (a d : BitVec 64) : (a = a + d) = (0 = d) :=
  propext ⟨fun h => by bv_decide, fun h => by bv_decide⟩
theorem add_eq_self (a c : BitVec 64) : (a + c = a) = (c = 0) :=
  propext ⟨fun h => by bv_decide, fun h => by bv_decide⟩
theorem add_add (a c d : BitVec 64) : a + c + d = a + (c + d) := by bv_decide
theorem sub_lit (a c : BitVec 64) : a - c = a + (-c) := by bv_decide

def b0 (w : BitVec 32) : BitVec 8 := w.extractLsb' 0 8
def b1 (w : BitVec 32) : BitVec 8 := w.extractLsb' 8 8
def b2 (w : BitVec 32) : BitVec 8 := w.extractLsb' 16 8
def b3 (w : BitVec 32) : BitVec 8 := w.extractLsb' 24 8

/-- The four bytes at `a` are owned and hold `w`, little-endian. -/
def Word (m : Mem) (a : BitVec 64) (w : BitVec 32) : Prop :=
  m a = some (b0 w) ∧ m (a + 1) = some (b1 w) ∧ m (a + 2) = some (b2 w) ∧ m (a + 3) = some (b3 w)

def Mem.put32 (m : Mem) (a : BitVec 64) (w : BitVec 32) : Mem :=
  (((m.put8 a (b0 w)).put8 (a + 1) (b1 w)).put8 (a + 2) (b2 w)).put8 (a + 3) (b3 w)

theorem read_word {m : Mem} {a : BitVec 64} {w : BitVec 32} (h : Word m a w) :
    m.read32 a = some (w.setWidth 64) := by
  obtain ⟨h0, h1, h2, h3⟩ := h
  simp only [Mem.read32, Mem.read8, h0, h1, h2, h3, Option.map_some, Option.bind_eq_bind, Option.bind_some,
    Option.pure_def, Option.some.injEq, b0, b1, b2, b3]
  bv_decide

theorem write_word {m : Mem} {a : BitVec 64} {w : BitVec 32} (h : Word m a w) (v : BitVec 64) :
    m.write32 a v = some (m.put32 a (v.setWidth 32)) := by
  obtain ⟨h0, h1, h2, h3⟩ := h
  have e0 : byte v 0 = b0 (v.setWidth 32) := by simp only [byte, b0]; bv_decide
  have e1 : byte v 1 = b1 (v.setWidth 32) := by simp only [byte, b1]; bv_decide
  have e2 : byte v 2 = b2 (v.setWidth 32) := by simp only [byte, b2]; bv_decide
  have e3 : byte v 3 = b3 (v.setWidth 32) := by simp only [byte, b3]; bv_decide
  simp_all [Mem.write32, Mem.write8, Mem.put8, Mem.put32, add_eq_add, self_eq_add, add_eq_self]

theorem word_put32 (m : Mem) (a : BitVec 64) (w : BitVec 32) : Word (m.put32 a w) a w := by
  simp_all [Word, Mem.put32, Mem.put8, add_eq_add, self_eq_add, add_eq_self]

theorem put32_other (m : Mem) (a : BitVec 64) (w : BitVec 32) (x : BitVec 64) (h : 4 ≤ (x - a).toNat) :
    m.put32 a w x = m x := by
  have h0 : x ≠ a := by intro e; subst e; simp at h
  have h1 : x ≠ a + 1 := by intro e; subst e; revert h; bv_omega
  have h2 : x ≠ a + 2 := by intro e; subst e; revert h; bv_omega
  have h3 : x ≠ a + 3 := by intro e; subst e; revert h; bv_omega
  simp_all [Mem.put32, Mem.put8]

end A64
