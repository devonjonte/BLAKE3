import Spec_adler32

/-! Algebra for block implementations, independent of the machine and vector width.
The original byte-wise specification remains the definition being proved. -/
namespace Adler32

def total : List (BitVec 8) → Nat
  | [] => 0
  | x :: xs => x.toNat + total xs

def weighted : List (BitVec 8) → Nat
  | [] => 0
  | x :: xs => (xs.length + 1) * x.toNat + weighted xs

/-- One block's affine action, with the two modular reductions postponed. -/
def block (a b : Nat) (xs : List (BitVec 8)) : Nat × Nat :=
  ((a + total xs) % 65521,
   (b + xs.length * a + weighted xs) % 65521)

/-- Reducing after each byte equals reducing the block's two affine sums. -/
theorem fold_eq_block (xs : List (BitVec 8)) (a b : Nat) :
    xs.foldl step (a % 65521, b % 65521) = block a b xs := by
  induction xs generalizing a b with
  | nil => simp [block, total, weighted]
  | cons x xs ih =>
    have hstep : step (a % 65521, b % 65521) x =
        ((a + x.toNat) % 65521, (b + a + x.toNat) % 65521) := by
      simp [step, Nat.add_mod, Nat.add_assoc]
    rw [List.foldl_cons, hstep, ih]
    unfold block
    simp only [total, weighted, List.length_cons, Nat.mul_add, Nat.add_mul, Nat.one_mul]
    congr 1
    · congr 1; omega
    · congr 1; omega

/-- The block law specializes to the existing complete-message specification. -/
theorem sums_eq_block (xs : List (BitVec 8)) : sums xs = block 1 0 xs := by
  simpa [sums] using fold_eq_block xs 1 0

theorem total_append (xs ys : List (BitVec 8)) : total (xs ++ ys) = total xs + total ys := by
  induction xs with
  | nil => simp [total]
  | cons x xs ih => simp [total, ih, Nat.add_assoc]

/-- Concatenating blocks adds the later block's length times the earlier byte sum. -/
theorem weighted_append (xs ys : List (BitVec 8)) :
    weighted (xs ++ ys) = weighted xs + ys.length * total xs + weighted ys := by
  induction xs with
  | nil => simp [weighted, total]
  | cons x xs ih =>
    simp only [List.cons_append, weighted, List.length_append, total, ih,
      Nat.mul_add, Nat.add_mul, Nat.one_mul]
    omega

/-- Every byte contributes at most 255 to a raw sum. -/
theorem total_le (xs : List (BitVec 8)) : total xs ≤ 255 * xs.length := by
  induction xs with
  | nil => simp [total]
  | cons x xs ih =>
    have hx := x.isLt
    simp only [total, List.length_cons, Nat.mul_add, Nat.mul_one]
    omega

/-- Twice the raw weighted sum is bounded without division or rounding. -/
theorem twice_weighted_le (xs : List (BitVec 8)) :
    2 * weighted xs ≤ 255 * xs.length * (xs.length + 1) := by
  induction xs with
  | nil => simp [weighted]
  | cons x xs ih =>
    have hx : x.toNat ≤ 255 := by have := x.isLt; omega
    have hm := Nat.mul_le_mul_left (2 * (xs.length + 1)) hx
    simp only [weighted, List.length_cons]
    simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul, Nat.mul_assoc] at ih hm ⊢
    omega

/-- A fixed 4 KiB kernel can return its two raw sums in one 64-bit word. -/
theorem raw4096_bounds (xs : List (BitVec 8)) (h : xs.length = 4096) :
    total xs ≤ 1044480 ∧ weighted xs ≤ 2139617280 := by
  have ha := total_le xs
  have hb := twice_weighted_le xs
  rw [h] at ha hb
  constructor <;> omega

/-- Canonical entry sums permit u32 arithmetic around a 4 KiB raw-sums kernel. -/
theorem update4096_bounds (xs : List (BitVec 8)) (h : xs.length = 4096)
    (a b : Nat) (ha : a < 65521) (hb : b < 65521) :
    a + total xs < 2 ^ 32 ∧ b + 4096 * a + weighted xs < 2 ^ 32 := by
  obtain ⟨hs, hw⟩ := raw4096_bounds xs h
  constructor <;> omega

/-- Four raw4096 calls can postpone reduction, with u32 A and u64 B. -/
theorem update16384_bounds (xs : List (BitVec 8)) (h : xs.length = 16384)
    (a b : Nat) (ha : a < 65521) (hb : b < 65521) :
    a + total xs < 2 ^ 32 ∧ b + 16384 * a + weighted xs < 2 ^ 36 := by
  have hs := total_le xs
  have hw := twice_weighted_le xs
  rw [h] at hs hw
  constructor <;> omega

/-- At most 22 bytes from seed one need neither modular reduction. -/
theorem seed22_bounds (xs : List (BitVec 8)) (h : xs.length ≤ 22) :
    1 + total xs < 65521 ∧ xs.length + weighted xs < 65521 := by
  have hs := total_le xs
  have hw := twice_weighted_le xs
  have hn : xs.length + 1 ≤ 23 := by omega
  have hm := Nat.mul_le_mul (Nat.mul_le_mul_left 255 h) hn
  constructor <;> omega

#print axioms update16384_bounds
#print axioms seed22_bounds
#print axioms fold_eq_block
#print axioms weighted_append
#print axioms raw4096_bounds
#print axioms update4096_bounds
end Adler32
