import Stack

/-! # Whole groups of chunks are leaves of the specification's tree

The specification defines the tree from the top. A hasher that takes many chunks at a time (a wide
kernel takes 32) makes each group's subtree first and then a tree over the groups' values. This file
proves that this is the specification's tree: with the chunks in groups of `2^b`, the last group of
`1` to `2^b` chunks, the tree over the chunks is the tree over the groups' own trees.

It names no code and no machine. -/

namespace Blake3

set_option linter.deprecated false

variable (key : Vector Word 8) (mode : Word) (chunks : Array Node)

/-- A number of two or more is a power of two and a rest of one up to that power. -/
theorem pow_and_rest (m : Nat) (h : 2 ≤ m) : ∃ a r, m = 2 ^ a + r ∧ 1 ≤ r ∧ r ≤ 2 ^ a := by
  refine ⟨(m - 1).log2, m - leftCount m, ?_, ?_, ?_⟩
  · have := leftCount_lt m h; unfold leftCount at this ⊢; omega
  · exact (split_nonempty m h).2
  · exact left_big m h

/-- The chunks in groups of `size`, the last of `last` chunks: how many chunks `g` groups from the
first are, where `g` may count the last (`count` groups in all). -/
def groupsLen (size last count g : Nat) : Nat := if g < count then g * size else (count - 1) * size + last

/-- **The specification's subtree over `m` whole groups from group `g0` is its subtree over those
groups' own subtrees**: `groups` holds, for each group, the node of the specification's subtree over
its chunks. -/
theorem go_groups (b last count : Nat) (hl1 : 1 ≤ last) (hl : last ≤ 2 ^ b) (groups : Array Node)
    (hg : ∀ g, g < count → groups[g]! = tree.go key mode chunks (g * 2 ^ b) (if g + 1 < count then 2 ^ b else last)) :
    ∀ (m g0 : Nat), 1 ≤ m → g0 + m ≤ count →
      tree.go key mode chunks (g0 * 2 ^ b) (if g0 + m < count then m * 2 ^ b else (m - 1) * 2 ^ b + last) =
        tree.go key mode groups g0 m := by
  intro m
  induction m using Nat.strongRecOn with
  | _ m ih =>
    intro g0 h1 hc
    rcases Nat.lt_or_ge m 2 with hm | hm
    · -- one group: its own subtree
      have e : m = 1 := by omega
      subst e
      rw [go_one, hg g0 (by omega)]
      by_cases hlast : g0 + 1 < count
      · simp [hlast]
      · simp [hlast]
    · obtain ⟨a, r, e, hr1, hr⟩ := pow_and_rest m hm
      subst e
      have hp := Nat.two_pow_pos a
      have hb := Nat.two_pow_pos b
      -- the chunks: a power of two, and a rest of one up to it
      have hn : (if g0 + (2 ^ a + r) < count then (2 ^ a + r) * 2 ^ b else (2 ^ a + r - 1) * 2 ^ b + last) =
          2 ^ (a + b) + (if g0 + (2 ^ a + r) < count then r * 2 ^ b else (r - 1) * 2 ^ b + last) := by
        rw [Nat.pow_add]
        by_cases hh : g0 + (2 ^ a + r) < count
        · simp only [hh, if_true]; rw [Nat.add_mul]
        · simp only [hh, if_false]
          have : 2 ^ a + r - 1 = 2 ^ a + (r - 1) := by omega
          rw [this, Nat.add_mul]; omega
      have hrest1 : 1 ≤ (if g0 + (2 ^ a + r) < count then r * 2 ^ b else (r - 1) * 2 ^ b + last) := by
        by_cases hh : g0 + (2 ^ a + r) < count
        · simp only [hh, if_true]; exact Nat.le_trans hb (Nat.le_mul_of_pos_left _ hr1)
        · simp only [hh, if_false]; omega
      have hrest : (if g0 + (2 ^ a + r) < count then r * 2 ^ b else (r - 1) * 2 ^ b + last) ≤ 2 ^ (a + b) := by
        rw [Nat.pow_add]
        by_cases hh : g0 + (2 ^ a + r) < count
        · simp only [hh, if_true]; exact Nat.mul_le_mul_right _ hr
        · simp only [hh, if_false]
          have h1' : (r - 1) * 2 ^ b + 2 ^ b = r * 2 ^ b := by
            have : r = (r - 1) + 1 := by omega
            conv => rhs; rw [this, Nat.add_mul, Nat.one_mul]
          have h2' : r * 2 ^ b ≤ 2 ^ a * 2 ^ b := Nat.mul_le_mul_right _ hr
          omega
      rw [hn, go_split key mode chunks _ (a + b) _ hrest1 hrest, go_split key mode groups g0 a r hr1 hr]
      -- the left: 2^a whole groups; the right: the r groups after them
      have left := ih (2 ^ a) (by omega) g0 (by omega) (by omega)
      have hleft : g0 + 2 ^ a < count := by omega
      simp only [hleft, if_true] at left
      have right := ih r (by omega) (g0 + 2 ^ a) hr1 (by omega)
      have hstart : (g0 + 2 ^ a) * 2 ^ b = g0 * 2 ^ b + 2 ^ (a + b) := by rw [Nat.add_mul, Nat.pow_add]
      rw [hstart, Nat.add_assoc] at right
      simp only [sub]
      rw [← Nat.pow_add] at left
      rw [left, right]

/-- **The tree over the chunks is the tree over their groups**: `count` groups of `2^b` chunks, the
last of `1` to `2^b`. -/
theorem tree_groups (b last count : Nat) (hc : 1 ≤ count) (hl1 : 1 ≤ last) (hl : last ≤ 2 ^ b) (groups : Array Node)
    (hsize : chunks.size = (count - 1) * 2 ^ b + last) (hgs : groups.size = count)
    (hg : ∀ g, g < count → groups[g]! = tree.go key mode chunks (g * 2 ^ b) (if g + 1 < count then 2 ^ b else last)) :
    tree key mode chunks = tree key mode groups := by
  have := go_groups key mode chunks b last count hl1 hl groups hg count 0 hc (by omega)
  simp only [Nat.zero_mul, Nat.zero_add, Nat.lt_irrefl, if_false] at this
  rw [tree, tree, hsize, hgs]; exact this

end Blake3
