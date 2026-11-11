import Std.Tactic.BVDecide

/-! # Memory as the bytes a program owns, and words and slices in it

Shared by every machine model: `m a = none` is a byte the program does not own. -/

abbrev Mem := BitVec 64 → Option (BitVec 8)

/-- One byte put at `a`, whoever owns it. -/
def Mem.put8 (m : Mem) (a : BitVec 64) (v : BitVec 8) : Mem := fun x => if x = a then some v else m x

theorem add_eq_add (a c d : BitVec 64) : (a + c = a + d) = (c = d) :=
  propext ⟨fun h => by bv_decide, fun h => by rw [h]⟩
theorem self_eq_add (a d : BitVec 64) : (a = a + d) = (0 = d) :=
  propext ⟨fun h => by bv_decide, fun h => by rw [← h]; bv_decide⟩
theorem add_eq_self (a c : BitVec 64) : (a + c = a) = (c = 0) :=
  propext ⟨fun h => by bv_decide, fun h => by rw [h]; bv_decide⟩

def b0 (w : BitVec 32) : BitVec 8 := w.extractLsb' 0 8
def b1 (w : BitVec 32) : BitVec 8 := w.extractLsb' 8 8
def b2 (w : BitVec 32) : BitVec 8 := w.extractLsb' 16 8
def b3 (w : BitVec 32) : BitVec 8 := w.extractLsb' 24 8

/-- The four bytes at `a` are owned and hold `w`, little-endian. -/
def Word (m : Mem) (a : BitVec 64) (w : BitVec 32) : Prop :=
  m a = some (b0 w) ∧ m (a + 1) = some (b1 w) ∧ m (a + 2) = some (b2 w) ∧ m (a + 3) = some (b3 w)

def Mem.put32 (m : Mem) (a : BitVec 64) (w : BitVec 32) : Mem :=
  (((m.put8 a (b0 w)).put8 (a + 1) (b1 w)).put8 (a + 2) (b2 w)).put8 (a + 3) (b3 w)

theorem put32_congr (m : Mem) (a : BitVec 64) {x y : BitVec 32} (h : x = y) : m.put32 a x = m.put32 a y := by rw [h]

theorem word_put32 (m : Mem) (a : BitVec 64) (w : BitVec 32) : Word (m.put32 a w) a w := by
  simp_all [Word, Mem.put32, Mem.put8, add_eq_add, self_eq_add, add_eq_self]

theorem put32_other (m : Mem) (a : BitVec 64) (w : BitVec 32) (x : BitVec 64) (h : 4 ≤ (x - a).toNat) :
    m.put32 a w x = m x := by
  have h0 : x ≠ a := by intro e; subst e; simp at h
  have h1 : x ≠ a + 1 := by intro e; subst e; revert h; bv_omega
  have h2 : x ≠ a + 2 := by intro e; subst e; revert h; bv_omega
  have h3 : x ≠ a + 3 := by intro e; subst e; revert h; bv_omega
  simp_all [Mem.put32, Mem.put8]

/-- The words of `ws`, in order from address `q`, each owned. -/
def Holds (m : Mem) : BitVec 64 → List (BitVec 32) → Prop
  | _, [] => True
  | q, w :: ws => Word m q w ∧ Holds m (q + 4) ws

/-- A list in memory is still there in a memory that agrees on its bytes. -/
theorem holds_congr {m m' : Mem} : ∀ (ws : List (BitVec 32)) (q : BitVec 64), 4 * ws.length < 2 ^ 63 →
    (∀ x, (x - q).toNat < 4 * ws.length → m' x = m x) → Holds m q ws → Holds m' q ws := by
  intro ws
  induction ws with
  | nil => intros; trivial
  | cons w ws ih =>
    intro q hn h ⟨hw, ht⟩
    simp only [List.length_cons] at hn h
    refine ⟨?_, ih (q + 4) (by omega) (fun x hx => h x (by bv_omega)) ht⟩
    obtain ⟨h0, h1, h2, h3⟩ := hw
    exact ⟨by rw [h q (by bv_omega)]; exact h0, by rw [h (q + 1) (by bv_omega)]; exact h1,
      by rw [h (q + 2) (by bv_omega)]; exact h2, by rw [h (q + 3) (by bv_omega)]; exact h3⟩
