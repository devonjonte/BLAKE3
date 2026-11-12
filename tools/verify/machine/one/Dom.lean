import Machine
open X86

/-! # No instruction changes which addresses are the program's (not to be read)

A write is a fault unless the program owns the byte, and nothing maps or unmaps memory: after any run the
same addresses hold a byte as before. So the stack a caller lends a function is the caller's again at the
return, whatever the function did there. -/

namespace X86

/-- The same addresses are the program's in both memories. -/
def Mem.SameDom (m m' : Mem) : Prop := ∀ x, (m' x).isSome = (m x).isSome

theorem Mem.SameDom.refl (m : Mem) : m.SameDom m := fun _ => rfl
theorem Mem.SameDom.trans {a b c : Mem} (h1 : a.SameDom b) (h2 : b.SameDom c) : a.SameDom c := fun x => (h2 x).trans (h1 x)

theorem Mem.write8_dom {m m' : Mem} {a : BitVec 64} {v : BitVec 8} (h : m.write8 a v = some m') : m.SameDom m' := by
  unfold Mem.write8 at h
  split at h
  · cases h
    intro x
    simp only [Mem.put8]
    split
    · subst x; simp_all
    · rfl
  · cases h

/-- A chain of byte writes, one link. -/
theorem Mem.dom_link {m0 m m' : Mem} {a : BitVec 64} {v : BitVec 8} {f : Mem → Option Mem} (h0 : m0.SameDom m)
    (h : (m.write8 a v >>= f) = some m') (k : ∀ m1, m0.SameDom m1 → f m1 = some m' → m0.SameDom m') : m0.SameDom m' := by
  cases hw : m.write8 a v with
  | none => rw [hw] at h; cases h
  | some m1 => rw [hw] at h; exact k m1 (h0.trans (Mem.write8_dom hw)) h

theorem Mem.write_dom {m m' : Mem} {a v : BitVec 64} {w : Nat} (h : m.write a v w = some m') : m.SameDom m' := by
  unfold Mem.write at h
  split at h
  · exact Mem.write8_dom h
  all_goals
    repeat (refine Mem.dom_link (by first | exact Mem.SameDom.refl _ | assumption) h ?_; clear h; intro _ _ h)
    exact Mem.SameDom.trans (by assumption) (Mem.write8_dom h)

theorem Mem.write128_dom {m m' : Mem} {a : BitVec 64} {v : V} (h : m.write128 a v = some m') : m.SameDom m' := by
  unfold Mem.write128 at h
  repeat (refine Mem.dom_link (by first | exact Mem.SameDom.refl _ | assumption) h ?_; clear h; intro _ _ h)
  exact Mem.SameDom.trans (by assumption) (Mem.write8_dom h)

@[simp] theorem State.set_mem (s : State) (r : Reg) (v : BitVec 64) : (s.set r v).mem = s.mem := by cases r <;> rfl
@[simp] theorem State.setx_mem (s : State) (i : Nat) (v : V) : (s.setx i v).mem = s.mem := by
  unfold State.setx; split <;> rfl

/-- Whatever state this gives, its memory has the domain of `m`. -/
def Keeps (m : Mem) (o : Option State) : Prop := ∀ s', o = some s' → m.SameDom s'.mem

theorem keeps_some {m : Mem} {t : State} (h : m.SameDom t.mem) : Keeps m (some t) := fun s' e => by cases e; exact h
theorem keeps_none {m : Mem} : Keeps m none := fun s' e => by cases e
theorem keeps_bind {α : Type} {m : Mem} {x : Option α} {f : α → Option State} (h : ∀ a, Keeps m (f a)) : Keeps m (x >>= f) := by
  intro s' e
  cases x with
  | none => cases e
  | some a => exact h a s' e
theorem keeps_map {α : Type} {m : Mem} {x : Option α} {f : α → State} (h : ∀ a, m.SameDom (f a).mem) : Keeps m (x.map f) := by
  intro s' e
  cases x with
  | none => cases e
  | some a => cases e; exact h a
theorem keeps_ite {m : Mem} {c : Prop} [Decidable c] {a b : Option State} (ha : Keeps m a) (hb : Keeps m b) : Keeps m (if c then a else b) := by
  split <;> assumption
theorem keeps_write {m : Mem} {t : State} {w : Nat} {o : Opnd} {v : BitVec 64} (h : m.SameDom t.mem) : Keeps m (write t w o v) := by
  intro s' e
  unfold write at e
  split at e
  · cases e; simpa using h
  · cases e
  · cases hw : t.mem.write _ v w with
    | none => rw [hw] at e; cases e
    | some m1 => rw [hw] at e; cases e; exact h.trans (Mem.write_dom hw)
theorem keeps_mwrite {m : Mem} {t : State} {a v : BitVec 64} {w : Nat} {f : Mem → State} (h : m.SameDom t.mem) (hf : ∀ m1, (f m1).mem = m1) :
    Keeps m ((t.mem.write a v w).map f) := by
  intro s' e
  cases hw : t.mem.write a v w with
  | none => rw [hw] at e; cases e
  | some m1 => rw [hw] at e; cases e; rw [hf]; exact h.trans (Mem.write_dom hw)
theorem keeps_mwrite128 {m : Mem} {t : State} {a : BitVec 64} {v : V} {f : Mem → State} (h : m.SameDom t.mem) (hf : ∀ m1, (f m1).mem = m1) :
    Keeps m ((t.mem.write128 a v).map f) := by
  intro s' e
  cases hw : t.mem.write128 a v with
  | none => rw [hw] at e; cases e
  | some m1 => rw [hw] at e; cases e; rw [hf]; exact h.trans (Mem.write128_dom hw)

macro "dom_leaf" : tactic => `(tactic| (first
  | exact Mem.SameDom.refl _
  | (simp only [State.set_mem, State.setx_mem]; exact Mem.SameDom.refl _)
  | (intro _; simp only [State.set_mem, State.setx_mem]; exact Mem.SameDom.refl _)
  | (intro _; rfl)
  | (intro _; split <;> exact Mem.SameDom.refl _)))

macro "dom_arm" : tactic => `(tactic| (
  repeat (first
    | exact keeps_none
    | (apply keeps_some; dom_leaf)
    | (apply keeps_write; dom_leaf)
    | (apply keeps_mwrite <;> dom_leaf)
    | (apply keeps_mwrite128 <;> dom_leaf)
    | (apply keeps_map; dom_leaf)
    | (apply keeps_ite)
    | (apply keeps_bind; intro _)
    | (split))))

/-- **One instruction leaves the same addresses the program's.** -/
theorem step_dom (i : Instr) (next : Nat) (s s' : State) (h : step i next s = some s') : s.mem.SameDom s'.mem := by
  have k : Keeps s.mem (step i next s) := by
    unfold step
    cases i <;> dsimp only <;> dom_arm
  exact k s' h

/-- **Any run leaves the same addresses the program's.** -/
theorem steps_dom (prog : Nat → Option (Instr × Nat)) : ∀ (k : Nat) (s s' : State), steps prog k s = some s' → s.mem.SameDom s'.mem
  | 0, s, s', h => by cases h; exact Mem.SameDom.refl _
  | k + 1, s, s', h => by
    simp only [steps] at h
    cases hp : prog s.pc with
    | none => rw [hp] at h; cases h
    | some x =>
      obtain ⟨i, next⟩ := x
      rw [hp] at h
      dsimp only at h
      cases hs : step i next s with
      | none => rw [hs] at h; cases h
      | some s1 => rw [hs] at h; exact (step_dom i next s s1 hs).trans (steps_dom prog k s1 s' h)

end X86
