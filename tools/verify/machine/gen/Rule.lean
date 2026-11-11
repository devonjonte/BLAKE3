import Bytes
import Fold

/-! # One rule for a loop over a slice, on any machine

The language's loop (`Scan` of Lang.lean) means: fold a function over the words, leaving each
value where its word was. This file proves, once, what compiled code needs for that: if ONE
turn of the machine's loop does one step of the function (`Turn`), the whole loop does the whole
fold, for a slice of any length, changes no byte outside it, and shows an observer only the
slice's address and length. The machine is any type of states with a step function; which
register holds what is given by the `View`. -/

/-- A machine, and where a compiled loop keeps its things. `S` is the machine's state, `O` what
an observer sees, `K` whatever the loop must leave alone (the callee's registers, the stack
pointer). -/
structure View (S O K : Type) where
  /-- Exactly `n` instructions. -/
  steps : Nat → S → Option S
  steps_add : ∀ a b s, steps (a + b) s = (steps a s).bind (steps b)
  mem : S → Mem
  pc : S → Nat
  leak : S → List O
  /-- The loop's first instruction, and where it leaves to. -/
  head : Nat
  exit : Nat
  /-- The instructions of one turn. -/
  turn : Nat
  /-- The carried value, the address of the next word, the bytes of the slice not yet done. -/
  acc : S → BitVec 32
  /-- Where the newest value is when a turn ends (the register the function returns). -/
  out : S → BitVec 32
  ptr : S → BitVec 64
  left : S → BitVec 64
  kept : S → K
  /-- What else must hold at the loop's head (a constant kept in a register). -/
  good : S → Prop
  /-- What one turn shows an observer, given the word's address and whether it is the last. -/
  obs : BitVec 64 → Bool → List O

/-- One turn of the loop does one step of `f`. -/
def Turn {S O K : Type} (V : View S O K) (f : BitVec 32 → BitVec 32 → BitVec 32) : Prop :=
  ∀ (s : S) (w : BitVec 32), V.pc s = V.head → V.good s → Word (V.mem s) (V.ptr s) w →
    ∃ s', V.steps V.turn s = some s' ∧
      V.acc s' = f (V.acc s) w ∧ V.out s' = f (V.acc s) w ∧ V.ptr s' = V.ptr s + 4 ∧ V.left s' = V.left s - 4 ∧
      V.mem s' = (V.mem s).put32 (V.ptr s) (f (V.acc s) w) ∧ V.kept s' = V.kept s ∧ V.good s' ∧
      V.pc s' = (if V.left s = 4 then V.exit else V.head) ∧
      V.leak s' = V.obs (V.ptr s) (decide (V.left s = 4)) ++ V.leak s

/-- What the whole loop shows: each word's address and whether it was the last. No word, and
nothing computed from one, is in it. -/
def loopLeak {O : Type} (obs : BitVec 64 → Bool → List O) : BitVec 64 → Nat → List O → List O
  | p, 0, seen => obs p true ++ seen
  | p, n + 1, seen => loopLeak obs (p + 4) n (obs p false ++ seen)

theorem more_words (n : Nat) (h : 4 * (n + 1 + 1) < 2 ^ 63) : BitVec.ofNat 64 (4 * (n + 1 + 1)) ≠ 4 := by bv_omega

/-- **The rule.** From the loop's head with the words `w :: rest` at `ptr` and their bytes in
`left`: `turn` instructions a word bring the machine to the loop's exit with the fold carried,
the scan in the words' place, every other byte and everything `kept` as it was, and a trace that
is a function of the slice's address and length. -/
theorem loop_rule {S O K : Type} (V : View S O K) (f : BitVec 32 → BitVec 32 → BitVec 32) (ht : Turn V f)
    (rest : List (BitVec 32)) : ∀ (w : BitVec 32) (s : S),
    V.pc s = V.head → V.good s → Holds (V.mem s) (V.ptr s) (w :: rest) →
    V.left s = BitVec.ofNat 64 (4 * (rest.length + 1)) → 4 * (rest.length + 1) < 2 ^ 63 →
    ∃ s', V.steps (V.turn * (rest.length + 1)) s = some s' ∧ V.pc s' = V.exit ∧
      V.out s' = foldW f (V.acc s) (w :: rest) ∧
      Holds (V.mem s') (V.ptr s) (scanW f (V.acc s) (w :: rest)) ∧
      (∀ x, 4 * (rest.length + 1) ≤ (x - V.ptr s).toNat → V.mem s' x = V.mem s x) ∧
      V.kept s' = V.kept s ∧
      V.leak s' = loopLeak V.obs (V.ptr s) rest.length (V.leak s) := by
  induction rest with
  | nil =>
    intro w s hpc hg ⟨hw, _⟩ hl _
    obtain ⟨s', hs, _, hacc, _, _, hmem, hk, _, hpc', hleak⟩ := ht s w hpc hg hw
    have h4 : V.left s = 4 := by rw [hl]; rfl
    simp only [h4, ↓reduceIte, decide_true] at hpc' hleak
    refine ⟨s', by simpa using hs, hpc', hacc, ?_, ?_, hk, hleak⟩
    · rw [hmem]; exact ⟨word_put32 _ _ _, trivial⟩
    · intro x hx; rw [hmem]; exact put32_other _ _ _ x hx
  | cons w2 rest ih =>
    intro w s hpc hg ⟨hw, hrest⟩ hl hn
    simp only [List.length_cons] at hl hn ⊢
    obtain ⟨s1, hs, hacc, _, hptr, hleft, hmem, hk, hg1, hpc1, hleak⟩ := ht s w hpc hg hw
    have h4 : V.left s ≠ 4 := by rw [hl]; exact more_words _ hn
    simp only [h4, ↓reduceIte, decide_false] at hpc1 hleak
    have hrest1 : Holds (V.mem s1) (V.ptr s1) (w2 :: rest) := by
      rw [hmem, hptr]
      exact holds_congr _ _ (by simp only [List.length_cons]; omega)
        (fun x hx => put32_other _ _ _ x (by simp only [List.length_cons] at hx; bv_omega)) hrest
    obtain ⟨s', hs', hpc', hacc', hh, hf, hk', hleak'⟩ :=
      ih w2 s1 hpc1 hg1 hrest1 (by rw [hleft, hl]; bv_omega) (by omega)
    refine ⟨s', ?_, hpc', ?_, ?_, ?_, by rw [hk', hk], ?_⟩
    · rw [show V.turn * (rest.length + 1 + 1) = V.turn + V.turn * (rest.length + 1) by
        rw [Nat.mul_add, Nat.mul_one, Nat.add_comm], V.steps_add, hs, Option.bind_some, hs']
    · rw [hacc', hacc]; rfl
    · rw [hacc, hptr] at hh
      refine ⟨?_, hh⟩
      obtain ⟨p0, p1, p2, p3⟩ := word_put32 (V.mem s) (V.ptr s) (f (V.acc s) w)
      rw [hptr] at hf
      exact ⟨by rw [hf _ (by bv_omega), hmem]; exact p0, by rw [hf _ (by bv_omega), hmem]; exact p1,
        by rw [hf _ (by bv_omega), hmem]; exact p2, by rw [hf _ (by bv_omega), hmem]; exact p3⟩
    · intro x hx
      rw [hptr] at hf
      rw [hf x (by bv_omega), hmem, put32_other _ _ _ x (by bv_omega)]
    · rw [hleak', hleak, hptr]; rfl

#print axioms loop_rule
