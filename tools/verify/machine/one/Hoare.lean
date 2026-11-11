import Machine
open X86

/-! # If the precondition holds, the postcondition holds: the rules, proved once

A function's contract is a claim about the machine: from any state at its first instruction in which
the precondition holds, the code runs to its return and the postcondition holds there. These are the
rules a compiler's generated proof is built from. They are proved here once, for any program, and say
nothing of any particular one. -/

namespace Hoare

/-- From a state where `P` holds, the program runs some number of instructions without a fault and
arrives where `Q` holds. (Total correctness: it does arrive.) -/
def Triple (prog : Nat → Option (Instr × Nat)) (P Q : State → Prop) : Prop :=
  ∀ s, P s → ∃ k s', steps prog k s = some s' ∧ Q s'

/-- One piece after another. -/
theorem seq {prog : Nat → Option (Instr × Nat)} {P Q R : State → Prop}
    (h1 : Triple prog P Q) (h2 : Triple prog Q R) : Triple prog P R := by
  intro s hp
  obtain ⟨k1, s1, hs1, hq⟩ := h1 s hp
  obtain ⟨k2, s2, hs2, hr⟩ := h2 s1 hq
  exact ⟨k1 + k2, s2, by rw [steps_add, hs1, Option.bind_some, hs2], hr⟩

/-- A stronger precondition, a weaker postcondition. -/
theorem weaken {prog : Nat → Option (Instr × Nat)} {P P' Q Q' : State → Prop}
    (h : Triple prog P Q) (hp : ∀ s, P' s → P s) (hq : ∀ s, Q s → Q' s) : Triple prog P' Q' := by
  intro s hs
  obtain ⟨k, s', hk, hq'⟩ := h s (hp s hs)
  exact ⟨k, s', hk, hq s' hq'⟩

/-- **A loop, by its invariant.** `Inv` is what holds each time the loop's first instruction is
reached, and `measure` a number that each turn makes smaller. If one turn, started where `Inv`
holds, either comes back with `Inv` and a smaller measure or leaves with `Post`, then the loop,
started where `Inv` holds, leaves with `Post`: however many turns that takes. -/
theorem loop {prog : Nat → Option (Instr × Nat)} {Inv Post : State → Prop} (measure : State → Nat)
    (turn : ∀ s, Inv s → ∃ k s', steps prog k s = some s' ∧ ((Inv s' ∧ measure s' < measure s) ∨ Post s')) :
    Triple prog Inv Post := by
  have all : ∀ n s, measure s < n → Inv s → ∃ k s', steps prog k s = some s' ∧ Post s' := by
    intro n
    induction n with
    | zero => intro s h; exact absurd h (Nat.not_lt_zero _)
    | succ n ih =>
      intro s hn hinv
      obtain ⟨k, s1, hk, hcase⟩ := turn s hinv
      rcases hcase with ⟨hinv1, hlt⟩ | hpost
      · obtain ⟨k2, s2, hk2, hp2⟩ := ih s1 (Nat.lt_of_lt_of_le hlt (Nat.le_of_lt_succ hn)) hinv1
        exact ⟨k + k2, s2, by rw [steps_add, hk, Option.bind_some, hk2], hp2⟩
      · exact ⟨k, s1, hk, hpost⟩
  intro s hinv
  exact all (measure s + 1) s (Nat.lt_succ_self _) hinv

#print axioms loop
#print axioms seq

end Hoare
