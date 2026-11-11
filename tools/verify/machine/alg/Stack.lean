import Blake3
import Theorems

/-! # The hasher's stack computes the specification's tree

The specification (C2SP's BLAKE3, `Blake3.tree`) defines the tree from the top: split the chunks
at the largest power of two below their number, and so on down. A hasher that takes its input
in pieces cannot do that; it keeps a stack of chaining values and merges. This file proves that
the stack algorithm of the core crate's `hasher.rs` (`push`: merge the stack to as many values
as the chunk counter has one bits, then push; `final_node`: fold the last chunk's node into the
stack from the top) gives the specification's tree, for any number of chunks.

It names no code: it is about the algorithm. A proof about machine code needs only that the
code runs these functions. -/

namespace Blake3

set_option linter.deprecated false

abbrev CV := Vector Word 8

/-- The number of one bits. -/
def ones (n : Nat) : Nat := if n = 0 then 0 else n % 2 + ones (n / 2)
decreasing_by omega

theorem ones_zero : ones 0 = 0 := by rw [ones]; rfl

theorem ones_pos (n : Nat) (h : 0 < n) : ones n = n % 2 + ones (n / 2) := by
  rw [ones, if_neg (by omega)]

theorem ones_two_mul (x : Nat) : ones (2 * x) = ones x := by
  cases x with
  | zero => rfl
  | succ y => rw [ones_pos _ (by omega), show 2 * (y + 1) % 2 = 0 by omega, show 2 * (y + 1) / 2 = y + 1 by omega, Nat.zero_add]

theorem ones_two_mul_add_one (x : Nat) : ones (2 * x + 1) = ones x + 1 := by
  rw [ones_pos _ (by omega), show (2 * x + 1) % 2 = 1 by omega, show (2 * x + 1) / 2 = x by omega, Nat.add_comm]

theorem ones_pow_mul (a x : Nat) : ones (2 ^ a * x) = ones x := by
  induction a with
  | zero => simp
  | succ a ih => rw [Nat.pow_succ, Nat.mul_comm (2 ^ a) 2, Nat.mul_assoc, ones_two_mul, ih]

/-- Adding a power of two below every one bit adds one bit. -/
theorem ones_add_pow (a q : Nat) : ones (2 ^ (a + 1) * q + 2 ^ a) = ones (2 ^ (a + 1) * q) + 1 := by
  have e : 2 ^ (a + 1) * q + 2 ^ a = 2 ^ a * (2 * q + 1) := by
    rw [Nat.pow_succ, Nat.mul_add, Nat.mul_one, Nat.mul_assoc]
  rw [e, ones_pow_mul, ones_pow_mul, ones_two_mul_add_one]

theorem ones_succ_le (x : Nat) : ones (x + 1) ≤ ones x + 1 := by
  induction x using Nat.strongRecOn with
  | _ x ih =>
    rcases Nat.mod_two_eq_zero_or_one x with h | h
    · have e : x = 2 * (x / 2) := by omega
      rw [e, ones_two_mul_add_one, ones_two_mul]; omega
    · have e : x = 2 * (x / 2) + 1 := by omega
      have e2 : x + 1 = 2 * (x / 2 + 1) := by omega
      rw [e2, ones_two_mul]
      have := ih (x / 2) (by omega)
      have e3 : ones x = ones (x / 2) + 1 := by
        conv => lhs; rw [e]
        exact ones_two_mul_add_one _
      omega

/-- Adding a power of two adds at most one bit. -/
theorem ones_add_pow_le (j : Nat) : ∀ x, ones (x + 2 ^ j) ≤ ones x + 1 := by
  induction j with
  | zero => intro x; simpa using ones_succ_le x
  | succ j ih =>
    intro x
    rcases Nat.mod_two_eq_zero_or_one x with h | h
    · have e : x + 2 ^ (j + 1) = 2 * (x / 2 + 2 ^ j) := by rw [Nat.pow_succ]; omega
      have e1 : ones x = ones (x / 2) := by
        conv => lhs; rw [show x = 2 * (x / 2) by omega]
        exact ones_two_mul _
      rw [e, ones_two_mul, e1]; exact ih _
    · have e : x + 2 ^ (j + 1) = 2 * (x / 2 + 2 ^ j) + 1 := by rw [Nat.pow_succ]; omega
      have e1 : ones x = ones (x / 2) + 1 := by
        conv => lhs; rw [show x = 2 * (x / 2) + 1 by omega]
        exact ones_two_mul_add_one _
      rw [e, ones_two_mul_add_one, e1]; have := ih (x / 2); omega

variable (key : Vector Word 8) (mode : Word) (chunks : Array Node)

/-- The chaining value of the specification's subtree over `n` chunks from `start`. -/
def sub (start n : Nat) : CV := (tree.go key mode chunks start n).cv

theorem go_one (start : Nat) : tree.go key mode chunks start 1 = chunks[start]! := by
  rw [tree.go]; simp

/-- The specification splits `2^a + r` chunks, `1 ≤ r ≤ 2^a`, after the first `2^a`. -/
theorem go_split (start a r : Nat) (h1 : 1 ≤ r) (hr : r ≤ 2 ^ a) :
    tree.go key mode chunks start (2 ^ a + r) =
      parentNode key mode (sub key mode chunks start (2 ^ a)) (sub key mode chunks (start + 2 ^ a) r) := by
  have hp := Nat.two_pow_pos a
  have hk : leftCount (2 ^ a + r) = 2 ^ a := (split_unique (2 ^ a + r) a (by omega) (by omega) (by omega)).symm
  rw [tree.go, dite_cond_eq_false (eq_false (by omega))]
  simp only [hk, Nat.add_sub_cancel_left, sub]

/-- **A stack**, top first, of the chaining values of complete subtrees that together cover the
`m` chunks from `start`: each of `2^a` chunks, the exponents rising from the top, none below
`lo`. (They are the one bits of `m`.) -/
inductive Stk (start : Nat) : Nat → List CV → Nat → Prop
  | nil (lo : Nat) : Stk start lo [] 0
  | cons (lo a : Nat) (below : List CV) (m' : Nat) : lo ≤ a → Stk start (a + 1) below m' →
      Stk start lo (sub key mode chunks (start + m') (2 ^ a) :: below) (m' + 2 ^ a)

theorem Stk.mono {start lo lo' : Nat} {st : List CV} {m : Nat} (h : Stk key mode chunks start lo st m) (hl : lo' ≤ lo) :
    Stk key mode chunks start lo' st m := by
  cases h with
  | nil => exact Stk.nil lo'
  | cons _ a below m' ha hb => exact Stk.cons lo' a below m' (by omega) hb

/-- A stack has as many values as its chunk count has one bits, and `2^lo` divides the count. -/
theorem Stk.len {start lo : Nat} {st : List CV} {m : Nat} (h : Stk key mode chunks start lo st m) :
    st.length = ones m ∧ 2 ^ lo ∣ m := by
  induction h with
  | nil lo => exact ⟨ones_zero.symm, Nat.dvd_zero _⟩
  | cons lo a below m' ha _ ih =>
    obtain ⟨hl, q, hq⟩ := ih
    refine ⟨?_, Nat.dvd_add ?_ (Nat.pow_dvd_pow 2 ha)⟩
    · rw [List.length_cons, hl, hq, ones_add_pow]
    · exact Nat.dvd_trans (Nat.pow_dvd_pow 2 (by omega)) ⟨q, hq⟩

/-- `final_node`'s loop: a node folded into the stack from the top. -/
def finish (st : List CV) (node : Node) : Node := st.foldl (fun nd cv => parentNode key mode cv nd.cv) node

/-- **Finishing a stack gives the specification's subtree.** If the stack covers the `m` chunks
from `start` and the node is the specification's subtree over the next `r` (no more than the
stack's smallest subtree), the fold is the specification's subtree over all `m + r`. -/
theorem finish_stk {start lo : Nat} {st : List CV} {m : Nat} (h : Stk key mode chunks start lo st m) :
    ∀ r, 1 ≤ r → r ≤ 2 ^ lo →
      finish key mode st (tree.go key mode chunks (start + m) r) = tree.go key mode chunks start (m + r) := by
  induction h with
  | nil lo => intro r _ _; simp [finish]
  | cons lo a below m' ha _ ih =>
    intro r h1 hr
    have hle : 2 ^ lo ≤ 2 ^ a := Nat.pow_le_pow_right (by decide) ha
    have hs := go_split key mode chunks (start + m') a r h1 (by omega)
    simp only [finish, List.foldl_cons]
    rw [show start + (m' + 2 ^ a) = start + m' + 2 ^ a by omega]
    have := ih (2 ^ a + r) (by omega) (by rw [Nat.pow_succ]; omega)
    simp only [finish] at this
    rw [show m' + 2 ^ a + r = m' + (2 ^ a + r) by omega, ← this, hs]
    rfl

/-- `CvStack::merge`: while the stack has more than `target` values, the top two become their
parent. -/
def mergeTo (target : Nat) : List CV → List CV
  | top :: second :: below =>
    if target < below.length + 2 then mergeTo target ((parentNode key mode second top).cv :: below)
    else top :: second :: below
  | st => st
termination_by st => st.length

/-- **A lazy push, then the merge, is a stack again.** On a stack over `m` chunks whose subtrees
all have at least `2^a` chunks, put the chaining value of the next `2^a` chunks; merged to the
number of one bits of the new count, it is the stack over `m + 2^a` chunks. -/
theorem merge_lazy {start : Nat} : ∀ (st : List CV) (a m : Nat), Stk key mode chunks start a st m →
    Stk key mode chunks start a
      (mergeTo key mode (ones (m + 2 ^ a)) (sub key mode chunks (start + m) (2 ^ a) :: st)) (m + 2 ^ a) := by
  intro st
  induction st with
  | nil =>
    intro a m h
    cases h
    rw [mergeTo]
    exact Stk.cons a a [] 0 (Nat.le_refl a) (Stk.nil (a + 1))
    all_goals simp
  | cons top below ih =>
    intro a m h
    cases h with
    | cons _ b _ m' hab hb =>
      obtain ⟨hlen, q, hq⟩ := hb.len
      rw [mergeTo]
      by_cases e : a = b
      · subst e
        have hle := ones_add_pow_le (a + 1) m'
        have hm : m' + 2 ^ a + 2 ^ a = m' + 2 ^ (a + 1) := by rw [Nat.pow_succ]; omega
        rw [if_pos (by rw [hm, hlen]; omega)]
        have hs := go_split key mode chunks (start + m') a (2 ^ a) (Nat.two_pow_pos a) (Nat.le_refl _)
        have hcv : (parentNode key mode (sub key mode chunks (start + m') (2 ^ a))
            (sub key mode chunks (start + (m' + 2 ^ a)) (2 ^ a))).cv = sub key mode chunks (start + m') (2 ^ (a + 1)) := by
          rw [show start + (m' + 2 ^ a) = start + m' + 2 ^ a by omega, ← hs,
            show 2 ^ a + 2 ^ a = 2 ^ (a + 1) by rw [Nat.pow_succ]; omega]
          rfl
        rw [hcv, hm]
        exact Stk.mono key mode chunks (ih (a + 1) m' hb) (Nat.le_succ a)
      · have hlt : a + 1 ≤ b := by omega
        have hd : 2 ^ (a + 1) ∣ m' + 2 ^ b :=
          Nat.dvd_add (Nat.dvd_trans (Nat.pow_dvd_pow 2 (by omega)) ⟨q, hq⟩) (Nat.pow_dvd_pow 2 hlt)
        obtain ⟨q2, hq2⟩ := hd
        have h1 : ones (m' + 2 ^ b + 2 ^ a) = ones (m' + 2 ^ b) + 1 := by rw [hq2, ones_add_pow]
        have h2 : ones (m' + 2 ^ b) = ones m' + 1 := by rw [hq, ones_add_pow]
        rw [if_neg (by rw [h1, h2, hlen]; omega)]
        exact Stk.cons a a _ _ (Nat.le_refl a) (Stk.cons (a + 1) b below m' hlt hb)

/-- The hasher's stack after `n` whole chunks were pushed one by one (`push`: merge to the one
bits of the counter, then put the chunk's chaining value on top). -/
def pushed : Nat → List CV
  | 0 => []
  | n + 1 => (chunks[n]!).cv :: mergeTo key mode (ones n) (pushed n)

theorem pushed_merged (n : Nat) : Stk key mode chunks 0 0 (mergeTo key mode (ones n) (pushed key mode chunks n)) n := by
  induction n with
  | zero => rw [pushed, mergeTo]; exact Stk.nil 0; all_goals simp
  | succ n ih =>
    have h := merge_lazy key mode chunks _ 0 n ih
    simp only [Nat.pow_zero, Nat.zero_add] at h
    rw [pushed]
    have e : sub key mode chunks n 1 = (chunks[n]!).cv := by rw [sub, go_one]
    rw [← e]; exact h

/-- **The hasher's stack computes the specification's tree.** For any `n ≥ 1` chunks: push all
but the last one by one, merge to the one bits of the count, and fold the last chunk's node in
from the top (`final_node`): the node is `Blake3.tree`'s root. -/
theorem stack_is_the_tree (h : 0 < chunks.size) :
    finish key mode (mergeTo key mode (ones (chunks.size - 1)) (pushed key mode chunks (chunks.size - 1)))
      (chunks[chunks.size - 1]!) = tree key mode chunks := by
  have hs := finish_stk key mode chunks (pushed_merged key mode chunks (chunks.size - 1)) 1 (Nat.le_refl 1) (by simp)
  rw [go_one, Nat.zero_add] at hs
  rw [hs, tree, show chunks.size - 1 + 1 = chunks.size by omega]

#print axioms stack_is_the_tree

/-- If `2^a` divides a stack's count, none of its subtrees is smaller than `2^a`. -/
theorem Stk.raise {start lo : Nat} {st : List CV} {m : Nat} (h : Stk key mode chunks start lo st m) (a : Nat)
    (hd : 2 ^ a ∣ m) : Stk key mode chunks start a st m := by
  cases h with
  | nil => exact Stk.nil a
  | cons _ b below m' hb hbelow =>
    by_cases hab : a ≤ b
    · exact Stk.cons a b below m' hab hbelow
    · exfalso
      obtain ⟨_, q, hq⟩ := hbelow.len
      have h2 : 2 ^ (b + 1) ∣ m' + 2 ^ b := Nat.dvd_trans (Nat.pow_dvd_pow 2 (by omega)) hd
      have h3 : 2 ^ (b + 1) ∣ 2 ^ b := (Nat.dvd_add_right ⟨q, hq⟩).mp h2
      have := Nat.le_of_dvd (Nat.two_pow_pos b) h3
      rw [Nat.pow_succ] at this
      have := Nat.two_pow_pos b
      omega

/-- **Any run of the hasher's pushes.** The stack after pushes of whole subtrees, each of `2^a`
chunks where `2^a` divides the chunks so far (`hasher.rs`'s `feed` pushes such subtrees, `fill`
single chunks): before each push the stack is merged to the one bits of the count. -/
inductive Pushes : List CV → Nat → Prop
  | start : Pushes [] 0
  | push (st : List CV) (m a : Nat) : Pushes st m → 2 ^ a ∣ m →
      Pushes (sub key mode chunks m (2 ^ a) :: mergeTo key mode (ones m) st) (m + 2 ^ a)

theorem pushes_merged {st : List CV} {m : Nat} (h : Pushes key mode chunks st m) :
    Stk key mode chunks 0 0 (mergeTo key mode (ones m) st) m := by
  induction h with
  | start => rw [mergeTo]; exact Stk.nil 0; all_goals simp
  | push st m a _ hd ih =>
    have h := merge_lazy key mode chunks _ a m (ih.raise key mode chunks a hd)
    rw [Nat.zero_add] at h
    exact h.mono key mode chunks (Nat.zero_le a)

/-- **Whatever subtrees the hasher pushed, its final node is the specification's tree.** After
any such pushes covering all chunks but the last, merged, the last chunk's node folded in from
the top is `Blake3.tree`'s root. -/
theorem pushes_give_the_tree {st : List CV} (h : Pushes key mode chunks st (chunks.size - 1)) (hn : 0 < chunks.size) :
    finish key mode (mergeTo key mode (ones (chunks.size - 1)) st) (chunks[chunks.size - 1]!) = tree key mode chunks := by
  have hs := finish_stk key mode chunks (pushes_merged key mode chunks h) 1 (Nat.le_refl 1) (by simp)
  rw [go_one, Nat.zero_add] at hs
  rw [hs, tree, show chunks.size - 1 + 1 = chunks.size by omega]

#print axioms pushes_give_the_tree

/-- The specification's chunk nodes of an input (section 4.2), as `Blake3.blake3` makes them. -/
def chunksOf (input : ByteArray) : Array Node :=
  (Array.range (max 1 ((input.size + 1023) / 1024))).map fun i =>
    chunkNode key mode (input.extract (1024 * i) (1024 * (i + 1))) i

/-- **The hasher's algorithm is BLAKE3.** For any key, mode, input and output length: push every
chunk but the last, merge, fold the last chunk's node in, and take the root's output: the bytes
are the specification's `blake3`. What is left to prove about the code is that each compiled
function computes its part of this: a chunk's node, a parent's chaining value, the stack's
moves, the output's bytes. -/
theorem hasher_is_blake3 (input : ByteArray) (outLen : Nat) :
    output (finish key mode
        (mergeTo key mode (ones ((chunksOf key mode input).size - 1))
          (pushed key mode (chunksOf key mode input) ((chunksOf key mode input).size - 1)))
        ((chunksOf key mode input)[(chunksOf key mode input).size - 1]!)) outLen
      = blake3 key mode input outLen := by
  have hn : 0 < (chunksOf key mode input).size := by simp [chunksOf]; omega
  rw [stack_is_the_tree key mode _ hn]
  rfl

#print axioms hasher_is_blake3

end Blake3
