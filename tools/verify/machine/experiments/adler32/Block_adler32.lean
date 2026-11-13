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

#print axioms fold_eq_block
#print axioms weighted_append
end Adler32
