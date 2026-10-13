import StackProofs
import ChildrenProofs
open Aeneas Aeneas.Std Result
open Bridge WideBridge ChildrenProof

/-! # The Hasher

`fill`, `feed`, and `final_node` (src/hasher_core.rs) are the Hasher's
update and finalization over its stack (src/stack_core.rs). Given kernels
that meet their contracts, a Hasher's root node, after any updates, is the
specification's root node over all the bytes the updates gave: the stack
holds the chaining values of `HasherProof.stackCvs` over the full chunks,
followed while no partial chunk waits by one subtree not yet merged. -/

namespace HasherCoreProof

/-- The stack's merge commutes with a map that commutes with its node. -/
theorem merge_map {α β : Type} (f : α → β) (node : α → α → α) (node' : β → β → β)
    (hf : ∀ a b, f (node a b) = node' (f a) (f b)) (t : Nat) (l : List α) :
    (HasherProof.merge node t l).map f = HasherProof.merge node' t (l.map f) := by
  induction l using HasherProof.merge.induct node t with
  | case1 b a rest h ih =>
    rw [HasherProof.merge, if_pos h, ih]
    simp only [List.map_cons]
    conv_rhs => rw [HasherProof.merge, if_pos (by simpa using h)]
    rw [hf]
  | case2 b a rest h =>
    rw [HasherProof.merge, if_neg h]
    simp only [List.map_cons]
    conv_rhs => rw [HasherProof.merge, if_neg (by simpa using h)]
  | case3 l h =>
    match l, h with
    | [], _ => simp [HasherProof.merge]
    | [a], _ => simp [HasherProof.merge]
    | b :: a :: r, h => exact absurd rfl (h b a r)

/-- A power-of-two block's tree: the parent of its two halves'. -/
theorem goIdx_pow_split {α : Type} (leaf : Nat → α) (node : α → α → α) (c k : Nat) :
    goIdx leaf node c (2 ^ (k + 1)) = node (goIdx leaf node c (2 ^ k)) (goIdx leaf node (c + 2 ^ k) (2 ^ k)) := by
  rw [goIdx]
  have h1 : ¬ 2 ^ (k + 1) ≤ 1 := by
    have := Nat.one_le_two_pow (n := k); rw [pow_succ]; omega
  have hl : (2 ^ (k + 1) - 1).log2 = k := by
    rw [Nat.log2_eq_iff (by have := Nat.one_le_two_pow (n := k); rw [pow_succ]; omega)]
    have := Nat.one_le_two_pow (n := k); rw [pow_succ]; constructor <;> omega
  simp only [h1, ↓reduceIte, hl]
  congr 2
  rw [pow_succ]; omega

/-- A parent node determines its children's chaining values. -/
theorem nodeOp_cv_inj (key : Vector Blake3.Word 8) (mode : Blake3.Word) (L R L' R' : Blake3.Node)
    (h : nodeOp key mode L R = nodeOp key mode L' R') : L.cv = L'.cv ∧ R.cv = R'.cv := by
  simp only [nodeOp, Blake3.parentNode, Blake3.Node.mk.injEq] at h
  obtain ⟨-, hm, -⟩ := h
  have hl := congrArg Vector.toList hm
  simp only [Vector.toList_append] at hl
  obtain ⟨h1, h2⟩ := List.append_inj hl (by simp)
  exact ⟨Vector.toList_inj.mp h1, Vector.toList_inj.mp h2⟩

/-- The stack's subtrees depend on the leaves below its count alone. -/
theorem stackCvs_congr {α : Type} (leaf leaf' : Nat → α) (node : α → α → α) (c : Nat)
    (h : ∀ i, i < c → leaf i = leaf' i) :
    HasherProof.stackCvs leaf node c = HasherProof.stackCvs leaf' node c := by
  induction c using Nat.strong_induction_on generalizing leaf leaf' with
  | _ c ih =>
  rw [HasherProof.stackCvs, HasherProof.stackCvs]
  split
  · rfl
  · rename_i hc
    have := Nat.log2_self_le (n := c) (by omega)
    have := Nat.one_le_two_pow (n := c.log2)
    simp only
    rw [goIdx_congr leaf leaf' node 0 (2 ^ c.log2) (fun i _ hi => h i (by omega)) (by omega),
      ih (c - 2 ^ c.log2) (by omega) _ _ (fun i hi => h (i + 2 ^ c.log2) (by omega))]

/-! ## The stack's values, as the specification's subtrees -/

section
variable (key : Vector Blake3.Word 8) (mode : Blake3.Word) (abs : StackProof.Cv → Vector Blake3.Word 8)

/-- The stack holds the chaining values of the subtrees over the first `c`
chunks of `M`, merged. -/
def Merged (M : List Std.U8) (vals : List StackProof.Cv) (c : Nat) : Prop :=
  vals.map abs = (HasherProof.stackCvs (leafN key mode M 0) (nodeOp key mode) c).map Blake3.Node.cv

/-- The stack holds them over the first `c'` chunks, then the subtree of the
next `2 ^ j`, not yet merged: `c' + 2 ^ j = c`. -/
def Pending (M : List Std.U8) (vals : List StackProof.Cv) (c : Nat) : Prop :=
  ∃ c' j, 2 ^ j ∣ c' ∧ c' + 2 ^ j = c ∧
    vals.map abs = (HasherProof.stackCvs (leafN key mode M 0) (nodeOp key mode) c').map Blake3.Node.cv ++
      [(goIdx (leafN key mode M 0) (nodeOp key mode) c' (2 ^ j)).cv]

/-- Merging either to the 1-bits of `c` leaves them merged. -/
theorem merge_merged
    (M : List Std.U8) (vals : List StackProof.Cv) (c : Nat)
    (h : Merged key mode abs M vals c ∨ Pending key mode abs M vals c) :
    HasherProof.merge (cvOp key mode) (HasherProof.ones c) (vals.reverse.map abs) =
      ((HasherProof.stackCvs (leafN key mode M 0) (nodeOp key mode) c).map Blake3.Node.cv).reverse := by
  rw [List.map_reverse]
  rcases h with hm | ⟨c', j, hj, hc, hp⟩
  · rw [hm, ← List.map_reverse,
      ← merge_map Blake3.Node.cv (nodeOp key mode) (cvOp key mode) (fun a b => rfl),
      StackProof.merge_short _ _ _ (by rw [List.length_reverse, HasherProof.stackCvs_length]),
      List.map_reverse]
  · rw [hp, List.reverse_append, List.reverse_singleton, List.singleton_append, ← List.map_reverse,
      ← List.map_cons, ← merge_map Blake3.Node.cv (nodeOp key mode) (cvOp key mode) (fun a b => rfl),
      ← hc, HasherProof.merge_push _ _ c' j hj, List.map_reverse]

end

/-! ## Two small functions: the bit count and the subtree's length -/

theorem ones_zero : HasherProof.ones 0 = 0 := by rw [HasherProof.ones]; simp

theorem ones_pos' (c : Nat) (h : c ≠ 0) : HasherProof.ones c = 1 + HasherProof.ones (c - 2 ^ c.log2) := by
  rw [HasherProof.ones, if_neg h]

theorem ones_bit (c : Nat) : HasherProof.ones (2 * c) = HasherProof.ones c ∧
    HasherProof.ones (2 * c + 1) = HasherProof.ones c + 1 := by
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    by_cases hc : c = 0
    · subst hc
      refine ⟨by simp, ?_⟩
      rw [ones_pos' 1 (by omega)]; simp [ones_zero]
    · have hl := Nat.log2_self_le hc
      have hlt := Nat.lt_log2_self (n := c)
      have hd : c - 2 ^ c.log2 < c := by have := Nat.one_le_two_pow (n := c.log2); omega
      have e1 : (2 * c).log2 = c.log2 + 1 := Nat.log2_two_mul hc
      have e2 : (2 * c + 1).log2 = c.log2 + 1 := by
        rw [Nat.log2_eq_iff (by omega)]; constructor <;> rw [Nat.pow_succ] <;> omega
      obtain ⟨ih1, ih2⟩ := ih _ hd
      constructor
      · rw [ones_pos' _ (by omega), e1, ones_pos' c hc, Nat.pow_succ,
          show 2 * c - 2 ^ c.log2 * 2 = 2 * (c - 2 ^ c.log2) by omega, ih1]
      · rw [ones_pos' _ (by omega), e2, ones_pos' c hc, Nat.pow_succ,
          show 2 * c + 1 - 2 ^ c.log2 * 2 = 2 * (c - 2 ^ c.log2) + 1 by omega, ih2]; omega

/-- Clearing the lowest 1-bit: one fewer. -/
theorem ones_and_pred (x : Nat) (hx : x ≠ 0) : HasherProof.ones (x &&& (x - 1)) + 1 = HasherProof.ones x := by
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    obtain ⟨y, rfl | rfl⟩ : ∃ y, x = 2 * y ∨ x = 2 * y + 1 := ⟨x / 2, by omega⟩
    · have hy : y ≠ 0 := by omega
      have e : 2 * y &&& (2 * y - 1) = 2 * (y &&& (y - 1)) := by
        rw [show 2 * y - 1 = 2 * (y - 1) + 1 by omega]
        apply Nat.eq_of_testBit_eq; intro i
        cases i with
        | zero => simp [Nat.testBit_zero]
        | succ i =>
          rw [Nat.testBit_and, Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ,
            show (2 * (y - 1) + 1) / 2 = y - 1 by omega, show 2 * y / 2 = y by omega,
            show 2 * (y &&& (y - 1)) / 2 = y &&& (y - 1) by omega, Nat.testBit_and]
      rw [e, (ones_bit _).1, (ones_bit y).1]
      exact ih y (by omega) hy
    · have e : (2 * y + 1) &&& (2 * y + 1 - 1) = 2 * y := by
        rw [show 2 * y + 1 - 1 = 2 * y by omega]
        apply Nat.eq_of_testBit_eq; intro i
        cases i with
        | zero => simp [Nat.testBit_zero]
        | succ i =>
          rw [Nat.testBit_and, Nat.testBit_succ, Nat.testBit_succ,
            show (2 * y + 1) / 2 = y by omega, show 2 * y / 2 = y by omega, Bool.and_self]
      rw [e, (ones_bit y).1, (ones_bit y).2]

theorem ones_le (k : Nat) : ∀ c, c < 2 ^ k → HasherProof.ones c ≤ k := by
  induction k with
  | zero => intro c hc; have : c = 0 := by simp at hc; omega
            subst this; simp [ones_zero]
  | succ k ih =>
    intro c hc
    by_cases h0 : c = 0
    · subst h0; simp [ones_zero]
    · by_cases hk : c < 2 ^ k
      · have := ih c hk; omega
      · have hl : c.log2 = k := by
          rw [Nat.log2_eq_iff h0]; constructor <;> omega
        rw [ones_pos' c h0, hl]
        have := ih (c - 2 ^ k) (by rw [Nat.pow_succ] at hc; omega)
        omega

open hashercore in
/-- `ones`, as compiled from src/hasher_core.rs: the number of 1-bits. -/
theorem ones_spec (x : Std.U64) : ones x ⦃ r => r.val = HasherProof.ones x.val ⦄ := by
  unfold ones ones_loop
  apply loop.spec_decr_nat (fun st : Std.U64 × Std.Usize => st.1.val)
    (fun st => st.2.val + HasherProof.ones st.1.val = HasherProof.ones x.val)
  · rintro ⟨y, n⟩ hinv
    simp only at hinv
    unfold ones_loop.body
    by_cases hy : y != 0#u64
    · simp only [hy, ↓reduceIte]
      have hy0 : y.val ≠ 0 := by simp at hy; scalar_tac
      have hb : HasherProof.ones x.val ≤ 64 := ones_le 64 _ (by scalar_tac)
      step as ⟨i, hi⟩
      step as ⟨y1, hy1⟩
      have hk := ones_and_pred y.val hy0
      have hy1' : y1.val = y.val &&& (y.val - 1) := by rw [hy1]; simp [hi]
      step as ⟨n1, hn1⟩
      refine ⟨by rw [hn1, hy1']; omega, ?_⟩
      rw [hy1']; have := Nat.and_le_right (n := y.val) (m := y.val - 1); omega
    · simp only [hy]
      have : y.val = 0 := by simp at hy; scalar_tac
      rw [this, ones_zero] at hinv; simpa using hinv
  · simp

open hashercore in
/-- The halving loop: from a power of two `2 ^ k` (`10 ≤ k`) at most `r`,
halve while it leaves part of the bytes so far, `c * 1024`. -/
theorem subtree_len_loop_spec (c : Std.U64) (r : Nat) (so_far : Std.U64) (hso : so_far.val = c.val * 1024)
    (len : Std.Usize) (k : Nat) (hlen : len.val = 2 ^ k) (hk : 10 ≤ k) (hle : len.val ≤ r) :
    subtree_len_loop len so_far ⦃ q => ∃ j, q.val = 1024 * 2 ^ j ∧ 2 ^ j ∣ c.val ∧ q.val ≤ r ⦄ := by
  unfold subtree_len_loop
  apply loop.spec_decr_nat (fun l : Std.Usize => l.val)
    (fun l => ∃ k, l.val = 2 ^ k ∧ 10 ≤ k ∧ l.val ≤ r)
  · rintro l ⟨k, hl, hk, hle⟩
    unfold subtree_len_loop.body
    have hp : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    step as ⟨i, hi⟩
    step as ⟨i1, hi1⟩
    step as ⟨i2, hi2⟩
    have hmax : l.val < 2 ^ 64 := by
      have : l.val < 2 ^ System.Platform.numBits := by scalar_tac
      rcases System.Platform.numBits_eq with h | h <;> rw [h] at this <;> omega
    have hi1' : i1.val = 2 ^ k - 1 := by rw [hi1]; simp [hi]; omega
    have hand : i2.val = (c.val * 1024) % 2 ^ k := by
      rw [hi2]; simp only [UScalar.val_and, hi1', hso]; rw [Nat.and_comm, Nat.and_two_pow_sub_one_eq_mod]
    split
    · rename_i hnz
      have hk10 : 10 < k := by
        by_contra h
        have hk' : k = 10 := by omega
        have : i2.val = 0 := by rw [hand, hk']; omega
        simp [this] at hnz
      step as ⟨l1, hl1⟩
      refine ⟨⟨k - 1, ?_, by omega, ?_⟩, ?_⟩
      · rw [hl1, hl, show k = k - 1 + 1 by omega, Nat.pow_succ]; simp
      · omega
      · omega
    · rename_i hz
      have h0 : (c.val * 1024) % 2 ^ k = 0 := by rw [← hand]; simp at hz; scalar_tac
      simp only [WP.spec_ok]
      obtain ⟨m, rfl⟩ : ∃ m, k = m + 10 := ⟨k - 10, by omega⟩
      have e : (2 : Nat) ^ (m + 10) = 2 ^ m * 1024 := by rw [Nat.pow_add]
      refine ⟨m, by rw [hl, e]; omega, ?_, hle⟩
      rw [e] at h0
      exact (Nat.mul_dvd_mul_iff_right (by omega : 0 < 1024)).mp (Nat.dvd_of_mod_eq_zero h0)
  · exact ⟨k, hlen, hk, hle⟩

open hashercore in
/-- `subtree_len`, as compiled from src/hasher_core.rs: from chunk `c`
(below 2^54) with more than a chunk to go, a chunk times a power of two
dividing `c`, at most what is left. -/
theorem subtree_len_spec (c : Std.U64) (r : Std.Usize) (hc : c.val < 2 ^ 54) (hr : 1024 < r.val) :
    subtree_len c r ⦃ q => ∃ j, q.val = 1024 * 2 ^ j ∧ 2 ^ j ∣ c.val ∧ q.val ≤ r.val ⦄ := by
  unfold subtree_len
  have hr0 : r.val ≠ 0 := by omega
  have hlog10 : 10 ≤ Nat.log 2 r.val := Nat.le_log_of_pow_le (by omega) (by omega)
  have hpow := Nat.pow_log_le_self 2 hr0
  have hlt := Nat.lt_pow_succ_log_self (b := 2) (by omega) r.val
  have hbits := System.Platform.numBits_eq
  have hrmax : r.val < 2 ^ System.Platform.numBits := by scalar_tac
  have hlogb : Nat.log 2 r.val < System.Platform.numBits := Nat.log_lt_of_lt_pow hr0 hrmax
  step as ⟨i, hi, _⟩
  have hlz : (core.num.Usize.leading_zeros r).val = System.Platform.numBits - Nat.log 2 r.val - 1 := by
    simp only [core.num.Usize.leading_zeros, BitVec.leadingZeros]
    have : r.bv ≠ 0 := by intro h; apply hr0; simp [UScalar.val, h]
    simp only [this, ↓reduceIte, UScalar.val]
    rw [BitVec.natCast_eq_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    have : System.Platform.numBits ≤ 64 := by rcases hbits with h | h <;> omega
    have : (64 : Nat) < 2 ^ UScalarTy.U32.numBits := by simp
    omega
  step as ⟨i1, hi1⟩
  step as ⟨i2, hi2, _⟩
  step as ⟨len, hlen, _⟩
  step as ⟨i3, hi3⟩
  have hi3' : i3.val = 1024 := by rw [hi3]; simp [CHUNK_LEN]
  have hmul : c.val * i3.val ≤ Std.U64.max := by rw [hi3']; scalar_tac
  step as ⟨so_far, hso⟩
  have hi2' : i2.val = Nat.log 2 r.val := by
    rw [hi2, hi, hi1, hlz]; simp; omega
  apply subtree_len_loop_spec c r.val so_far (by rw [hso, hi3']) len (Nat.log 2 r.val)
    ?_ hlog10 ?_
  · rw [hlen, hi2', Nat.one_shiftLeft]
    apply Nat.mod_eq_of_lt
    have : 2 ^ Nat.log 2 r.val < 2 ^ System.Platform.numBits := Nat.pow_lt_pow_right (by omega) hlogb
    rw [Usize.size_def, Usize.numBits_def, UScalarTy.Usize_numBits_eq]; exact this
  · rw [hlen, hi2', Nat.one_shiftLeft, Nat.mod_eq_of_lt (by
      have : 2 ^ Nat.log 2 r.val < 2 ^ System.Platform.numBits := Nat.pow_lt_pow_right (by omega) hlogb
      rw [Usize.size_def, Usize.numBits_def, UScalarTy.Usize_numBits_eq]; exact this)]
    exact hpow

/-! ## The stack's code -/

open hashercore in
/-- A stack no longer than its target: the merge leaves it as it is. -/
theorem merge_noop_spec {P : Type} (PI : Parent P) (p : P) (s : CvStack) (target : Std.Usize)
    (hle : s.len.val ≤ target.val) :
    CvStack.merge PI s p target ⦃ s' => s' = s ⦄ := by
  unfold CvStack.merge CvStack.merge_loop
  have : CvStack.merge_loop.body PI p target s = ok (ControlFlow.done (s.cvs, s.len)) := by
    unfold CvStack.merge_loop.body
    have hng : ¬ s.len > target := by scalar_tac
    simp [hng, massert]
  rw [loop]
  simp only [this]
  simp

/-- The number of 1-bits of `c` is at most one more than its log. -/
theorem ones_le_log2 (c : Nat) : HasherProof.ones c ≤ c.log2 + 1 := by
  induction c using Nat.strong_induction_on with
  | _ c ih =>
  rw [HasherProof.ones]
  split
  · omega
  · rename_i hc
    have h1 := Nat.log2_self_le (n := c) (by omega)
    have h2 := Nat.lt_log2_self (n := c)
    by_cases hr : c - 2 ^ c.log2 = 0
    · rw [hr, HasherProof.ones]; simp
    · have := ih (c - 2 ^ c.log2) (by have := Nat.one_le_two_pow (n := c.log2); omega)
      have hlt : (c - 2 ^ c.log2).log2 < c.log2 := by
        rw [Nat.log2_lt (by omega)]; rw [pow_succ] at h2; omega
      omega

theorem ones_lt_55 (c : Nat) (hc : c < 2 ^ 54) : HasherProof.ones c < 55 := by
  have := ones_le_log2 c
  have : c.log2 < 54 := by
    by_cases h0 : c = 0
    · simp [h0]
    · exact (Nat.log2_lt h0).mpr hc
  omega

/-- The values' count is the stack's length. -/
theorem vals_length (st : hashercore.CvStack) (hinv : StackProof.Inv st) :
    (StackProof.vals st).length = st.len.val := by
  unfold StackProof.vals
  cases h : st.cvs with
  | none => simp; exact hinv.2 h
  | some a => simp; have := hinv.1; omega

section
variable (key : Vector Blake3.Word 8) (mode : Blake3.Word) (abs : StackProof.Cv → Vector Blake3.Word 8)

open hashercore in
/-- Merging to the 1-bits of `c` leaves the stack merged. -/
theorem merge_to_spec {P : Type} (PI : Parent P) (p : P)
    (hp : ∀ a b, PI.parent p a b ⦃ v => abs v = cvOp key mode (abs a) (abs b) ⦄)
    (M : List Std.U8) (st : CvStack) (hinv : StackProof.Inv st) (c : Nat)
    (h : Merged key mode abs M (StackProof.vals st) c ∨ Pending key mode abs M (StackProof.vals st) c)
    (t : Std.Usize) (ht : t.val = HasherProof.ones c) :
    CvStack.merge PI st p t ⦃ st' => StackProof.Inv st' ∧
      Merged key mode abs M (StackProof.vals st') c ⦄ := by
  by_cases hc : c = 0
  · subst hc
    have hv : StackProof.vals st = [] := by
      rcases h with hm | ⟨c', j, _, hcj, _⟩
      · simpa [Merged, HasherProof.stackCvs] using hm
      · have := Nat.one_le_two_pow (n := j); omega
    have hl : st.len.val = 0 := by rw [← vals_length st hinv, hv]; rfl
    apply WP.spec_mono (merge_noop_spec PI p st t (by omega))
    rintro st' rfl
    exact ⟨hinv, by simp [Merged, hv, HasherProof.stackCvs]⟩
  · apply WP.spec_mono (StackProof.merge_spec PI p abs (cvOp key mode) hp st t hinv
      (by rw [ht]; exact HasherProof.ones_pos c (by omega)))
    rintro st' ⟨hinv', this⟩
    refine ⟨hinv', ?_⟩
    rw [ht, merge_merged key mode abs M _ c h, List.map_reverse] at this
    unfold Merged
    exact List.reverse_inj.mp this

open hashercore in
/-- `push`: the stack merged to the 1-bits of `c`, then the subtree of the
next `2 ^ j` chunks on top. -/
theorem push_spec' {C K : Type} (CI : Chunk C) (FI : Feed K C) (k : K)
    (hp : ∀ a b, FI.ParentInst.parent k a b ⦃ v => abs v = cvOp key mode (abs a) (abs b) ⦄)
    (M : List Std.U8) (st : CvStack) (hinv : StackProof.Inv st) (c : Nat) (hc : c < 2 ^ 54)
    (h : Merged key mode abs M (StackProof.vals st) c ∨ Pending key mode abs M (StackProof.vals st) c)
    (cv : StackProof.Cv) (j : Nat) (hj : 2 ^ j ∣ c)
    (hx : abs cv = (goIdx (leafN key mode M 0) (nodeOp key mode) c (2 ^ j)).cv)
    (counter : Std.U64) (hcounter : counter.val = c) :
    push CI FI k st 0#u64 cv counter ⦃ st' => StackProof.Inv st' ∧
      (StackProof.vals st').map abs =
        (HasherProof.stackCvs (leafN key mode M 0) (nodeOp key mode) c).map Blake3.Node.cv ++
          [(goIdx (leafN key mode M 0) (nodeOp key mode) c (2 ^ j)).cv] ⦄ := by
  unfold push
  step as ⟨i, hi⟩
  step with ones_spec i as ⟨t, ht⟩
  step with merge_to_spec key mode abs FI.ParentInst k hp M st hinv c h t
    (by rw [ht, hi]; simp [hcounter]) as ⟨st1, hinv1, hm1⟩
  have hlen : st1.len.val < 55 := by
    rw [← vals_length st1 hinv1, ← List.length_map (f := abs), hm1, List.length_map,
      HasherProof.stackCvs_length]
    exact ones_lt_55 c hc
  step with StackProof.push_spec st1 cv hinv1 hlen as ⟨st2, hinv2, hv2⟩
  refine ⟨hinv2, ?_⟩
  rw [hv2, List.map_append, hm1]
  simp [hx]

end

/-! ## Leaves, as the message grows -/

/-- A full chunk of `M` is unchanged by appending to `M`. -/
theorem chunkOf_append (M X : List Std.U8) (i : Nat) (h : 1024 * (i + 1) ≤ M.length) :
    chunkOf (M ++ X) 0 i = chunkOf M 0 i := by
  simp only [chunkOf, Nat.sub_zero]
  rw [List.drop_append_of_le_length (by omega), List.take_append_of_le_length (by simp; omega)]

/-- The chunks of bytes appended at chunk `c` (the message `M` holding `c`
chunks), as chunks of the slice from `c`. -/
theorem chunkOf_tail (M X : List Std.U8) (c i : Nat) (hM : M.length = 1024 * c) (hi : c ≤ i) :
    chunkOf (M ++ X) 0 i = chunkOf X c i := by
  simp only [chunkOf, Nat.sub_zero]
  rw [List.drop_append, List.drop_eq_nil_of_le (by omega), List.nil_append, hM, Nat.mul_sub]

section
variable (key : Vector Blake3.Word 8) (mode : Blake3.Word) (abs : StackProof.Cv → Vector Blake3.Word 8)

theorem leafN_append (M X : List Std.U8) (i : Nat) (h : 1024 * (i + 1) ≤ M.length) :
    leafN key mode (M ++ X) 0 i = leafN key mode M 0 i := by
  simp only [leafN, chunkOf_append M X i h]

theorem merged_append (M X : List Std.U8) (vals : List StackProof.Cv) (c : Nat) (hM : 1024 * c ≤ M.length)
    (h : Merged key mode abs M vals c) : Merged key mode abs (M ++ X) vals c := by
  unfold Merged at *
  rw [h, stackCvs_congr _ _ _ c (fun i hi => (leafN_append key mode M X i (by omega)).symm)]

theorem pending_append (M X : List Std.U8) (vals : List StackProof.Cv) (c : Nat) (hM : 1024 * c ≤ M.length)
    (h : Pending key mode abs M vals c) : Pending key mode abs (M ++ X) vals c := by
  obtain ⟨c', j, hj, hc, hv⟩ := h
  refine ⟨c', j, hj, hc, ?_⟩
  rw [hv, stackCvs_congr _ _ _ c' (fun i hi => (leafN_append key mode M X i (by omega)).symm),
    goIdx_congr _ _ _ c' (2 ^ j) (fun i _ hi => (leafN_append key mode M X i (by omega)).symm)
      Nat.one_le_two_pow]

/-- The leaves of a slice appended at chunk `c` are the message's. -/
theorem leafN_tail (M X : List Std.U8) (c i : Nat) (hM : M.length = 1024 * c) (hi : c ≤ i) :
    leafN key mode X c i = leafN key mode (M ++ X) 0 i := by
  simp only [leafN, chunkOf_tail M X c i hM hi]

end

/-! ## The kernels' contracts -/

open hashercore in
/-- The Hasher's kernels meet their contracts: `R ch c P` reads a chunk
state `ch` as chunk number `c` holding the bytes `P`, and `abs` a chaining
value as the specification's. -/
structure Contracts {C K : Type} (CI : Chunk C) (FI : Feed K C) (k : K)
    (key : Vector Blake3.Word 8) (mode : Blake3.Word) (abs : StackProof.Cv → Vector Blake3.Word 8)
    (R : C → Nat → List Std.U8 → Prop) : Prop where
  counter : ∀ ch c P, R ch c P → CI.counter ch ⦃ u => u.val = c ⦄
  len : ∀ ch c P, R ch c P → CI.len ch ⦃ n => n.val = P.length ⦄
  update : ∀ ch c P (x : Slice Std.U8), R ch c P → P.length + x.length ≤ 1024 →
    CI.update ch x ⦃ ch' => R ch' c (P ++ x.val) ⦄
  advance : ∀ ch c (n : Std.U64), R ch c [] → c + n.val ≤ Std.U64.max →
    CI.advance ch n ⦃ ch' => R ch' (c + n.val) [] ⦄
  parent : ∀ a b, FI.ParentInst.parent k a b ⦃ v => abs v = cvOp key mode (abs a) (abs b) ⦄
  new_chunk : ∀ c, FI.new_chunk k c ⦃ ch => R ch c.val [] ⦄
  chunk_cv : ∀ ch c P, R ch c P → P.length = 1024 →
    FI.chunk_cv k ch ⦃ v => abs v = (Blake3.chunkNode key mode (toBA P) c).cv ⦄
  whole_chunk_cv : ∀ (x : Slice Std.U8) (c : Std.U64), x.length = 1024 →
    FI.whole_chunk_cv k x c ⦃ v => abs v = (Blake3.chunkNode key mode (toBA x.val) c.val).cv ⦄
  subtree_cv : ∀ (x : Slice Std.U8) (a : Std.Usize) (c : Std.U64), 1024 ≤ x.length →
    FI.subtree_cv k x a c ⦃ o => ∀ v, o = some v →
      abs v = (goIdx (leafN key mode x.val c.val) (nodeOp key mode) c.val (chunks x.length)).cv ⦄
  children : ∀ (x : Slice Std.U8) (a : Std.Usize) (c : Std.U64), 1024 < x.length →
    FI.children k x a c ⦃ r => ∃ L R : Blake3.Node,
      nodeOp key mode L R = goIdx (leafN key mode x.val c.val) (nodeOp key mode) c.val (chunks x.length) ∧
      r.val.map abs = [L.cv, R.cv] ⦄

section
variable (key : Vector Blake3.Word 8) (mode : Blake3.Word) (abs : StackProof.Cv → Vector Blake3.Word 8)

/-- Pending, after at least one chunk. -/
def PendingPos (M : List Std.U8) (vals : List StackProof.Cv) (c : Nat) : Prop :=
  ∃ c' j, 0 < c' ∧ 2 ^ j ∣ c' ∧ c' + 2 ^ j = c ∧
    vals.map abs = (HasherProof.stackCvs (leafN key mode M 0) (nodeOp key mode) c').map Blake3.Node.cv ++
      [(goIdx (leafN key mode M 0) (nodeOp key mode) c' (2 ^ j)).cv]

theorem pendingPos_pending (M : List Std.U8) (vals : List StackProof.Cv) (c : Nat)
    (h : PendingPos key mode abs M vals c) : Pending key mode abs M vals c := by
  obtain ⟨c', j, _, hj, hc, hv⟩ := h; exact ⟨c', j, hj, hc, hv⟩

end

/-! ## `feed` -/

section
variable (key : Vector Blake3.Word 8) (mode : Blake3.Word) (abs : StackProof.Cv → Vector Blake3.Word 8)

open hashercore in
/-- The loop's state: the bytes consumed so far (`M`) and the rest make
`T`; the chunk is empty and numbered `M`'s chunk count; the stack merged or
pending; and once nothing is left, a pending subtree follows a chunk. -/
def FeedInv {C : Type} (R : C → Nat → List Std.U8 → Prop) (T : List Std.U8) (st : C × CvStack × Slice Std.U8) : Prop :=
  ∃ M c, R st.1 c [] ∧ M ++ st.2.2.val = T ∧ M.length = 1024 * c ∧ T.length < 1024 * 2 ^ 54 ∧
    StackProof.Inv st.2.1 ∧
    (Merged key mode abs M (StackProof.vals st.2.1) c ∨ Pending key mode abs M (StackProof.vals st.2.1) c) ∧
    (st.2.2.length = 0 → (c = 0 ∧ StackProof.vals st.2.1 = []) ∨ PendingPos key mode abs M (StackProof.vals st.2.1) c)

/-- A subtree over a slice appended at chunk `c`, as one over the message. -/
theorem goIdx_tail (M X : List Std.U8) (c n : Nat) (hM : M.length = 1024 * c) (hn : 1 ≤ n) :
    goIdx (leafN key mode X c) (nodeOp key mode) c n = goIdx (leafN key mode (M ++ X) 0) (nodeOp key mode) c n :=
  goIdx_congr _ _ _ c n (fun i hi _ => leafN_tail key mode M X c i hM hi) hn

open hashercore in
/-- The SME2 hook, where the loop asks it (after the first chunk): any value
it gives is the subtree's. -/
theorem flat_spec {C K : Type} (CI : Chunk C) (FI : Feed K C) (k : K)
    (R : C → Nat → List Std.U8 → Prop)
    (hK : Contracts CI FI k key mode abs R) (sub : Slice Std.U8) (ahead : Std.Usize) (counter : Std.U64)
    (hs : 1024 ≤ sub.length) :
    (if counter > 0#u64 then FI.subtree_cv k sub ahead counter else ok none) ⦃ o => ∀ v, o = some v →
      0 < counter.val ∧ abs v = (goIdx (leafN key mode sub.val counter.val) (nodeOp key mode) counter.val
        (chunks sub.length)).cv ⦄ := by
  split
  · rename_i hpos
    apply WP.spec_mono (hK.subtree_cv sub ahead counter hs)
    intro o ho v hv
    exact ⟨by scalar_tac, ho v hv⟩
  · simp

open hashercore in
theorem feed_loop_spec {C K : Type} (CI : Chunk C) (FI : Feed K C) (k : K)
    (R : C → Nat → List Std.U8 → Prop)
    (hK : Contracts CI FI k key mode abs R) (T : List Std.U8)
    (ch : C) (s : CvStack) (inp : Slice Std.U8) (h : FeedInv key mode abs R T (ch, s, inp)) :
    feed_loop CI FI k ch s 0#u64 inp ⦃ r => r.2.2.length ≤ 1024 ∧ FeedInv key mode abs R T r ⦄ := by
  unfold feed_loop
  apply loop.spec_decr_nat (fun st : C × CvStack × Slice Std.U8 => st.2.2.length)
    (fun st => FeedInv key mode abs R T st)
  · rintro ⟨ch, s, inp⟩ ⟨M, c, hR, hM, hML, htot, hinv, hst, hz⟩
    simp only at hR hM hML hinv hst hz
    have hC : CHUNK_LEN.val = 1024 := by simp [CHUNK_LEN]
    unfold feed_loop.body
    simp only
    split
    · rename_i hgt
      have hgt' : 1024 < inp.length := by simp only [Slice.length]; scalar_tac
      step with hK.counter ch c [] hR as ⟨counter, hcounter⟩
      step with subtree_len_spec counter inp.len (by
        have := congrArg List.length hM; simp only [List.length_append] at this; rw [hcounter]; omega) (by simp only [Slice.length] at hgt'; scalar_tac)
        as ⟨len, j, hlen, hj, hle⟩
      step as ⟨i2, hi2⟩
      step as ⟨nch, hchunks⟩
      step as ⟨ahead, hahead, hahead1⟩
      step as ⟨sub, hsub, hsubl⟩
      have hj1 : 1 ≤ 2 ^ j := Nat.one_le_two_pow
      have hsl : sub.length = 1024 * 2 ^ j := by rw [hsubl, hlen]
      have hsv : sub.val = inp.val.take len.val := by rw [hsub, List.slice_zero_j]
      have hch : nch.val = 2 ^ j := by
        rw [hchunks]; simp [hi2, hlen, hC]
      have hcs : sub.length / 1024 + 0 = 2 ^ j := by rw [hsl]; omega
      have hck : chunks (sub.length) = 2 ^ j := by unfold chunks; rw [hsl]; omega
      have hcv : counter.val = c := hcounter
      have hM'L : (M ++ sub.val).length = 1024 * (c + 2 ^ j) := by
        rw [List.length_append, hML, show sub.val.length = sub.length from rfl, hsl]; ring
      have hTl : (M ++ sub.val).length ≤ T.length := by
        have hle' : len.val ≤ inp.val.length := by scalar_tac
        rw [← hM, List.length_append, List.length_append, hsv, List.length_take]; omega
      have hbound : c + 2 ^ j < 2 ^ 54 := by omega
      have hst' : Merged key mode abs (M ++ sub.val) (StackProof.vals s) c ∨
          Pending key mode abs (M ++ sub.val) (StackProof.vals s) c := by
        rcases hst with h1 | h1
        · exact Or.inl (merged_append key mode abs M _ _ _ (by omega) h1)
        · exact Or.inr (pending_append key mode abs M _ _ _ (by omega) h1)
      have hsub' : ∀ n, 1 ≤ n → goIdx (leafN key mode sub.val counter.val) (nodeOp key mode) counter.val n =
          goIdx (leafN key mode (M ++ sub.val) 0) (nodeOp key mode) c n := by
        intro n hn; rw [hcv]; exact goIdx_tail key mode M sub.val c n hML hn
      step with flat_spec key mode abs CI FI k R hK sub ahead counter (by omega) as ⟨flat, hflat⟩
      apply WP.spec_bind (Pₘ := fun s1 => StackProof.Inv s1 ∧
        Pending key mode abs (M ++ sub.val) (StackProof.vals s1) (c + 2 ^ j) ∧
        (len.val = inp.length → PendingPos key mode abs (M ++ sub.val) (StackProof.vals s1) (c + 2 ^ j)))
      · cases flat with
        | some cv =>
          obtain ⟨hpos, hv⟩ := hflat cv rfl
          simp only
          apply WP.spec_mono (push_spec' key mode abs CI FI k hK.parent
            (M ++ sub.val) s hinv c (by omega) hst' cv j (hcv ▸ hj)
            (by rw [hv, hck, hsub' _ hj1]) counter hcv)
          rintro s1 ⟨hinv1, hv1⟩
          exact ⟨hinv1, ⟨c, j, hcv ▸ hj, rfl, hv1⟩,
            fun _ => ⟨c, j, by omega, hcv ▸ hj, rfl, hv1⟩⟩
        | none =>
          simp only
          split
          · rename_i hle1
            have hle1' : len.val ≤ CHUNK_LEN.val := hle1
            have hj0 : 2 ^ j = 1 := by rw [hC] at hle1'; omega
            have hsl1 : sub.length = 1024 := by omega
            step with hK.whole_chunk_cv sub counter hsl1 as ⟨a, ha⟩
            have hx : abs a = (goIdx (leafN key mode (M ++ sub.val) 0) (nodeOp key mode) c (2 ^ 0)).cv := by
              rw [ha, pow_zero, goIdx, if_pos (le_refl 1), leafN, chunkOf_tail M sub.val _ _ hML (le_refl _),
                hcv]
              simp only [chunkOf, Nat.sub_self, Nat.mul_zero, List.drop_zero]
              rw [List.take_of_length_le (by simp only [Slice.length] at hsl1; omega)]
            apply WP.spec_mono (push_spec' key mode abs CI FI k hK.parent
              (M ++ sub.val) s hinv c (by omega) hst' a 0 (by simp) hx counter hcv)
            rintro s1 ⟨hinv1, hv1⟩
            rw [pow_zero] at hv1
            refine ⟨hinv1, ⟨c, 0, by simp, by rw [hj0, pow_zero], by rw [pow_zero]; exact hv1⟩, ?_⟩
            intro hall; omega
          · rename_i hgt1
            have hj0 : 1 ≤ j := by
              by_contra hc0; have : j = 0 := by omega
              subst this
              have hgt1' : ¬ len.val ≤ CHUNK_LEN.val := hgt1
              rw [hC] at hgt1'; omega
            obtain ⟨j0, rfl⟩ : ∃ j0, j = j0 + 1 := ⟨j - 1, by omega⟩
            step with hK.children sub ahead counter (by omega) as ⟨a, L, R, hLR, hmap⟩
            rw [hck, hsub' _ hj1, goIdx_pow_split] at hLR
            obtain ⟨hL, hR⟩ := nodeOp_cv_inj key mode _ _ _ _ hLR
            obtain ⟨x, y, hxy⟩ : ∃ x y, a.val = [x, y] := by
              have hl2 : a.val.length = 2 := by simp
              match h : a.val, hl2 with
              | [x, y], _ => exact ⟨x, y, rfl⟩
            rw [hxy] at hmap
            simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hmap
            obtain ⟨hx, hy⟩ := hmap
            step as ⟨left, hleft⟩
            step as ⟨right, hright⟩
            have hl' : left = x := by rw [hleft]; simp [hxy]
            have hr' : right = y := by rw [hright]; simp [hxy]
            have hj0d : 2 ^ j0 ∣ c := by
              rw [← hcv]; exact Nat.dvd_trans (Nat.pow_dvd_pow 2 (by omega)) hj
            step with push_spec' key mode abs CI FI k hK.parent
              (M ++ sub.val) s hinv c (by rw [pow_succ] at hbound; omega) hst' left j0 hj0d
              (by rw [hl', hx, ← hL]) counter hcv as ⟨s2, hinv2, hv2⟩
            step as ⟨i4, hi4⟩
            step as ⟨i5, hi5⟩
            have hi5v : i5.val = c + 2 ^ j0 := by
              rw [hi5, hi4, hch, hcv, pow_succ]; omega
            apply WP.spec_mono (push_spec' key mode abs CI FI k hK.parent
              (M ++ sub.val) s2 hinv2 (c + 2 ^ j0) (by rw [pow_succ] at hbound; omega)
              (Or.inr ⟨c, j0, hj0d, rfl, hv2⟩) right j0 (Nat.dvd_add hj0d (dvd_refl _))
              (by rw [hr', hy, ← hR]) i5 hi5v)
            rintro s3 ⟨hinv3, hv3⟩
            have hsum : c + 2 ^ j0 + 2 ^ j0 = c + 2 ^ (j0 + 1) := by rw [pow_succ]; omega
            refine ⟨hinv3, ⟨c + 2 ^ j0, j0, Nat.dvd_add hj0d (dvd_refl _), hsum, hv3⟩,
              fun _ => ⟨c + 2 ^ j0, j0, by have := Nat.one_le_two_pow (n := j0); omega,
                Nat.dvd_add hj0d (dvd_refl _), hsum, hv3⟩⟩
      · rintro s1 ⟨hinv1, hp1, hpos1⟩
        step with hK.advance ch c nch hR (by rw [hch]; scalar_tac) as ⟨ch1, hR1⟩
        step as ⟨inp1, hinp1, hinp1l⟩
        have hle' : len.val ≤ inp.val.length := by scalar_tac
        rw [hch] at hR1
        refine ⟨⟨M ++ sub.val, c + 2 ^ j, hR1, ?_, hM'L, htot, hinv1, Or.inr hp1, ?_⟩, ?_⟩
        · rw [← hM, hinp1, hsv, List.append_assoc, List.take_append_drop]
        · intro h0; right
          apply hpos1
          simp only [Slice.length] at h0 hinp1l ⊢; scalar_tac
        · simp only [Slice.length] at hinp1l ⊢; scalar_tac
    · rename_i hle
      simp only [WP.spec_ok]
      refine ⟨by simp only [Slice.length]; scalar_tac, M, c, hR, hM, hML, htot, hinv, hst, hz⟩
  · exact h

end

/-! ## The root's node -/

open hashercore in
/-- `get`: value `i` of the stack's values. -/
theorem get_spec (st : CvStack) (hinv : StackProof.Inv st) (i : Std.Usize) (hi : i.val < st.len.val) :
    CvStack.get st i ⦃ v => v = (StackProof.vals st)[i.val]! ⦄ := by
  unfold CvStack.get
  have hlt : i < st.len := by scalar_tac
  cases h : st.cvs with
  | none => have := hinv.2 h; omega
  | some a =>
    simp only [hlt, massert, decide_true, ↓reduceIte, h]
    have hal : a.val.length = 55 := by simp
    step*
    simp only [StackProof.vals, h]
    have hin : i.val < (a.val.take st.len.val).length := by rw [List.length_take]; have := hinv.1; omega
    rw [getElem!_pos _ i.val hin, List.getElem_take]
    simp_all [getElem!_pos _ i.val (by omega : i.val < a.val.length)]

open hashercore in
/-- The Nodes kernels meet their contracts: `RN n X` reads a node `n` as the
specification's node `X`. -/
structure NodeContracts {C K N : Type} (CI : Chunk C) (NI : Nodes K C N) (k : K)
    (key : Vector Blake3.Word 8) (mode : Blake3.Word) (abs : StackProof.Cv → Vector Blake3.Word 8)
    (R : C → Nat → List Std.U8 → Prop) (RN : N → Blake3.Node → Prop) : Prop where
  len : ∀ ch c P, R ch c P → CI.len ch ⦃ n => n.val = P.length ⦄
  chunk_node : ∀ ch c P, R ch c P → NI.chunk_node k ch ⦃ n => RN n (Blake3.chunkNode key mode (toBA P) c) ⦄
  parent_node : ∀ a b, NI.parent_node k a b ⦃ n => RN n (Blake3.parentNode key mode (abs a) (abs b)) ⦄
  node_cv : ∀ n X, RN n X → NI.node_cv k n ⦃ v => abs v = X.cv ⦄

section
variable (key : Vector Blake3.Word 8) (mode : Blake3.Word) (abs : StackProof.Cv → Vector Blake3.Word 8)

open hashercore in
/-- The fold: each value below `n0`, from the top, the parent's left child. -/
theorem final_loop_spec {C K N : Type} (CI : Chunk C) (NI : Nodes K C N) (k : K)
    (R : C → Nat → List Std.U8 → Prop) (RN : N → Blake3.Node → Prop)
    (hN : NodeContracts CI NI k key mode abs R RN)
    (st : CvStack) (hinv : StackProof.Inv st) (S : List Blake3.Node)
    (hS : (StackProof.vals st).map abs = S.map Blake3.Node.cv)
    (n0 : Std.Usize) (hn0 : n0.val ≤ st.len.val) (out0 : N) (base : Blake3.Node) (h0 : RN out0 base) :
    final_node_loop NI k st n0 out0 ⦃ out =>
      RN out ((S.take n0.val).foldr (fun s acc => nodeOp key mode s acc) base) ⦄ := by
  have hlen : S.length = st.len.val := by
    rw [← List.length_map (f := Blake3.Node.cv), ← hS, List.length_map, vals_length st hinv]
  unfold final_node_loop
  apply loop.spec_decr_nat (fun x : Std.Usize × N => x.1.val)
    (fun x : Std.Usize × N => x.1.val ≤ n0.val ∧
      RN x.2 (((S.take n0.val).drop x.1.val).foldr (fun s acc => nodeOp key mode s acc) base))
  · rintro ⟨n, out⟩ ⟨hn, hout⟩
    simp only at hn hout
    unfold final_node_loop.body
    simp only
    split
    · rename_i hpos
      step as ⟨n1, hn1⟩
      step with get_spec st hinv n1 (by scalar_tac) as ⟨a, ha⟩
      step with hN.node_cv out _ hout as ⟨a1, ha1⟩
      step with hN.parent_node a a1 as ⟨out1, hout1⟩
      refine ⟨by omega, ?_, by omega⟩
      have hi : n1.val < (S.take n0.val).length := by rw [List.length_take]; omega
      have hn1' : n1.val + 1 = n.val := by scalar_tac
      rw [List.drop_eq_getElem_cons hi, List.foldr_cons, hn1']
      have hav : abs a = (S.take n0.val)[n1.val].cv := by
        rw [ha, List.getElem_take]
        have hv : n1.val < (StackProof.vals st).length := by rw [vals_length st hinv]; omega
        rw [getElem!_pos (StackProof.vals st) n1.val hv]
        have := congrArg (fun l : List (Vector Blake3.Word 8) => l[n1.val]?) hS
        simp only [List.getElem?_map, List.getElem?_eq_getElem hv,
          List.getElem?_eq_getElem (by omega : n1.val < S.length), Option.map_some, Option.some.injEq] at this
        exact this
      have e : Blake3.parentNode key mode (abs a) (abs a1) = nodeOp key mode (S.take n0.val)[n1.val]
          (((S.take n0.val).drop n.val).foldr (fun s acc => nodeOp key mode s acc) base) := by
        rw [hav, ha1]; rfl
      exact e ▸ hout1
    · rename_i hz
      have hz' : n.val = 0 := by scalar_tac
      simp only [WP.spec_ok]
      rw [hz', List.drop_zero] at hout; exact hout
  · exact ⟨le_refl _, by simpa using h0⟩

end

/-! ## The Hasher's state between updates -/

section
variable (key : Vector Blake3.Word 8) (mode : Blake3.Word) (abs : StackProof.Cv → Vector Blake3.Word 8)

open hashercore in
/-- After the bytes `M`: the chunk holds the bytes after `M`'s last full
chunks (at most a chunk, all of `M`'s last chunk when it ends one); the
stack holds the subtrees over the full chunks, merged when a chunk is
partly filled, and else perhaps with one subtree not yet merged (after at
least one chunk). -/
def HInv {C : Type} (R : C → Nat → List Std.U8 → Prop) (M : List Std.U8) (ch : C) (st : CvStack) : Prop :=
  ∃ c P, R ch c P ∧ (∃ F, M = F ++ P ∧ F.length = 1024 * c) ∧ P.length ≤ 1024 ∧
    M.length < 1024 * 2 ^ 54 ∧ StackProof.Inv st ∧
    (0 < P.length → Merged key mode abs M (StackProof.vals st) c) ∧
    (P = [] → (c = 0 ∧ StackProof.vals st = []) ∨ PendingPos key mode abs M (StackProof.vals st) c)

open hashercore in
/-- `feed`: from the loop's state, the Hasher's. -/
theorem feed_spec {C K : Type} (CI : Chunk C) (FI : Feed K C) (k : K)
    (R : C → Nat → List Std.U8 → Prop)
    (hK : Contracts CI FI k key mode abs R) (T : List Std.U8)
    (ch : C) (s : CvStack) (inp : Slice Std.U8) (h : FeedInv key mode abs R T (ch, s, inp)) :
    feed CI FI k ch s 0#u64 inp ⦃ r => HInv key mode abs R T r.1 r.2 ⦄ := by
  unfold feed
  step with feed_loop_spec key mode abs CI FI k R hK T ch s inp h as ⟨ch1, s1, inp1, hle, hfi⟩
  obtain ⟨M, c, hR, hM, hML, htot, hinv, hst, hz⟩ := hfi
  simp only at hR hM hML hinv hst hz hle ⊢
  step as ⟨b, hb⟩
  split
  · rename_i hbt
    have h0 : inp1.length = 0 := by simp_all [Slice.length]
    have hv : inp1.val = [] := by simpa [Slice.length] using h0
    simp only [WP.spec_ok]
    rw [hv, List.append_nil] at hM
    subst hM
    exact ⟨c, [], hR, ⟨M, by simp, hML⟩, by simp, htot, hinv, fun h => by simp at h, fun _ => hz h0⟩
  · rename_i hbf
    have hpos : 0 < inp1.length := by
      by_contra h0; apply hbf; simp_all [Slice.length]
    step with hK.update ch1 c [] inp1 hR (by simpa using hle) as ⟨ch2, hR2⟩
    step with hK.counter ch2 c _ hR2 as ⟨c2, hc2⟩
    step as ⟨i1, hi1⟩
    step with ones_spec i1 as ⟨t, ht⟩
    have hst' : Merged key mode abs T (StackProof.vals s1) c ∨ Pending key mode abs T (StackProof.vals s1) c := by
      rw [← hM]
      rcases hst with h1 | h1
      · exact Or.inl (merged_append key mode abs M _ _ _ (by omega) h1)
      · exact Or.inr (pending_append key mode abs M _ _ _ (by omega) h1)
    step with merge_to_spec key mode abs FI.ParentInst k hK.parent T s1 hinv c hst' t
      (by rw [ht, hi1, hc2]; simp) as ⟨s2, hinv2, hm2⟩
    refine ⟨c, inp1.val, by simpa using hR2, ⟨M, hM.symm, hML⟩, by simpa [Slice.length] using hle, htot, hinv2,
      fun _ => hm2, fun he => ?_⟩
    simp only [Slice.length] at hpos; rw [he] at hpos; simp at hpos

open hashercore in
/-- `fill`: the partial chunk filled from the input; with the rest empty, the
Hasher's state after all the input, and else the loop's. -/
theorem fill_spec {C K : Type} (CI : Chunk C) (FI : Feed K C) (k : K)
    (R : C → Nat → List Std.U8 → Prop)
    (hK : Contracts CI FI k key mode abs R) (M : List Std.U8)
    (ch : C) (st : CvStack) (h : HInv key mode abs R M ch st) (input : Slice Std.U8)
    (hbound : M.length + input.length < 1024 * 2 ^ 54) :
    fill CI FI k ch st 0#u64 input ⦃ r =>
      (r.1.length = 0 → HInv key mode abs R (M ++ input.val) r.2.1 r.2.2) ∧
      (0 < r.1.length → FeedInv key mode abs R (M ++ input.val) (r.2.1, r.2.2, r.1)) ⦄ := by
  obtain ⟨c, P, hR, ⟨F, hF, hFl⟩, hPl, hMl, hinv, hmerged, hempty⟩ := h
  have hC : CHUNK_LEN.val = 1024 := by simp [CHUNK_LEN]
  have htot : (M ++ input.val).length < 1024 * 2 ^ 54 := by
    rw [List.length_append]; simpa [Slice.length] using hbound
  unfold fill
  step with hK.len ch c P hR as ⟨i, hi⟩
  split
  · rename_i hi0
    have hP : P = [] := by
      have : P.length = 0 := by rw [← hi]; scalar_tac
      exact List.length_eq_zero_iff.mp this
    simp only [WP.spec_ok]
    have hMF : M = F := by rw [hF, hP, List.append_nil]
    constructor
    · intro h0
      have hv : input.val = [] := by simpa [Slice.length] using h0
      rw [hv, List.append_nil]
      exact ⟨c, P, hR, ⟨F, hF, hFl⟩, hPl, hMl, hinv, hmerged, hempty⟩
    · intro hpos
      refine ⟨M, c, by rw [← hP]; exact hR, rfl, by rw [hMF, hFl], htot, hinv, ?_, fun h0 => by simp only at h0; omega⟩
      rcases hempty hP with ⟨hc0, hv0⟩ | hpp
      · left; unfold Merged; rw [hv0, hc0]; simp [HasherProof.stackCvs]
      · right; exact pendingPos_pending key mode abs M _ _ hpp
  · rename_i hi0
    have hPpos : 0 < P.length := by
      have : i.val ≠ 0 := by scalar_tac
      omega
    have hPl' : P.length ≤ 1024 := hPl
    step as ⟨i1, hi1⟩
    apply WP.spec_bind (Pₘ := fun take : Std.Usize => take.val = min (1024 - P.length) input.length)
    · split
      · rename_i hlt
        step as ⟨t, ht⟩
        have : i1.val < input.len.val := hlt
        rw [ht, hC, hi]; simp only [Slice.length] at *; scalar_tac
      · rename_i hge
        simp only [WP.spec_ok]
        have : ¬ i1.val < input.len.val := hge
        simp only [Slice.length] at *; scalar_tac
    · intro take htake
      step*
      have hsl : s.length = take.val := by assumption
      have hsv : s.val = input.val.take take.val := by rw [s_post, List.slice_zero_j]
      step with hK.update ch c P s hR (by rw [hsl, htake]; omega) as ⟨ch1, hR1⟩
      step as ⟨rest, hrest, hrestl⟩
      step as ⟨b, hb⟩
      have hinput : input.val = s.val ++ rest.val := by
        rw [hsv, hrest]; simp [List.take_append_drop]
      have hMF : M ++ s.val = F ++ (P ++ s.val) := by rw [hF, List.append_assoc]
      have hst : Merged key mode abs (M ++ s.val) (StackProof.vals st) c := by
        exact merged_append key mode abs M _ _ _ (by rw [hF, List.length_append]; omega) (hmerged hPpos)
      split
      · rename_i hbt
        have hr0 : rest.val = [] := by
          have : rest.length = 0 := by rw [← hb]; exact hbt
          simpa [Slice.length] using this
        simp only [WP.spec_ok]
        refine ⟨fun _ => ?_, fun hpos => by simp [Slice.length, hr0] at hpos⟩
        rw [hinput, hr0, List.append_nil]
        refine ⟨c, P ++ s.val, hR1, ⟨F, hMF, hFl⟩, ?_, ?_, hinv, fun _ => hst, ?_⟩
        · rw [List.length_append, show s.val.length = s.length from rfl, hsl, htake]; omega
        · have htot' := htot
          rw [hinput, hr0, List.append_nil] at htot'
          exact htot'
        · intro he
          have := congrArg List.length he
          simp only [List.length_append, List.length_nil] at this; omega
      · rename_i hbf
        have hrpos : 0 < rest.length := by
          have : ¬ rest.length = 0 := by rw [← hb]; exact hbf
          omega
        have htk : take.val = 1024 - P.length := by omega
        have hP1 : (P ++ s.val).length = 1024 := by
          rw [List.length_append, show s.val.length = s.length from rfl, hsl, htk]; omega
        step with hK.counter ch1 c _ hR1 as ⟨cnt, hcnt⟩
        step with hK.chunk_cv ch1 c _ hR1 hP1 as ⟨a, ha⟩
        have hc1 : c = c := rfl
        have hFP : (F ++ (P ++ s.val)).length = 1024 * (c + 1) := by
          rw [List.length_append, hFl, hP1]; ring
        have hx : abs a = (goIdx (leafN key mode (M ++ s.val) 0) (nodeOp key mode) c (2 ^ 0)).cv := by
          rw [ha, pow_zero, goIdx, if_pos (le_refl 1), leafN, hMF, hc1]
          simp only [chunkOf, Nat.sub_zero]
          rw [← hFl, List.drop_left, List.take_of_length_le (by omega)]
        have hle2 : (F ++ (P ++ s.val)).length ≤ (M ++ input.val).length := by
          rw [← hMF, hinput, ← List.append_assoc]; simp only [List.length_append]; omega
        step with push_spec' key mode abs CI FI k hK.parent (M ++ s.val) st hinv
          c (by omega) (Or.inl hst) a 0 (by simp) hx cnt (by rw [hcnt, hc1])
          as ⟨st1, hinv1, hv1⟩
        step as ⟨i3, hi3⟩
        step with hK.new_chunk i3 as ⟨ch2, hR2⟩
        refine ⟨fun h0 => by simp only [Slice.length] at h0 hrpos; omega, fun _ => ?_⟩
        have hi3v : i3.val = c + 1 := by rw [hi3, hcnt]
        rw [hi3v] at hR2
        refine ⟨M ++ s.val, c + 1, hR2, by rw [List.append_assoc, ← hinput], ?_, htot, hinv1, ?_, ?_⟩
        · rw [hMF, hFP]
        · right; exact ⟨c, 0, by simp, rfl, by rw [pow_zero] at hv1 ⊢; exact hv1⟩
        · intro h0; simp only [Slice.length] at h0 hrpos; omega

/-- The specification's root node over the bytes `M`. -/
def RootNode (M : List Std.U8) : Blake3.Node :=
  Blake3.tree key mode ((Array.range (max 1 (((toBA M).size + 1023) / 1024))).map
    fun i => Blake3.chunkNode key mode ((toBA M).extract (1024 * i) (1024 * (i + 1))) i)

/-- At most a chunk: the root is the chunk's node. -/
theorem root_short (M : List Std.U8) (hl : M.length ≤ 1024) :
    RootNode key mode M = Blake3.chunkNode key mode (toBA M) 0 := by
  have hcount : max 1 (((toBA M).size + 1023) / 1024) = 1 := by rw [toBA_size]; omega
  simp only [RootNode, hcount, Blake3.tree]
  rw [Blake3.tree.go]
  simp only [Array.size_map, Array.size_range, Nat.le_refl, ↓reduceDIte]
  rw [getElem!_pos _ 0 (by simp)]
  simp only [Array.getElem_map, Array.getElem_range, Nat.mul_zero, Nat.zero_add, toBA_extract, List.drop_zero,
    Nat.sub_zero, Nat.mul_one]
  rw [List.take_of_length_le hl]

/-- More than nothing: the root is the tree's over all the chunks. -/
theorem root_long (M : List Std.U8) (hne : M ≠ []) :
    RootNode key mode M = goIdx (leafN key mode M 0) (nodeOp key mode) 0 (chunks M.length) :=
  (goIdx_leafN_root key mode M hne).symm

open hashercore in
/-- `final_node`: the root's node over all the bytes. -/
theorem final_node_spec {C K N : Type} (CI : Chunk C) (NI : Nodes K C N) (k : K)
    (R : C → Nat → List Std.U8 → Prop) (RN : N → Blake3.Node → Prop)
    (hN : NodeContracts CI NI k key mode abs R RN)
    (M : List Std.U8) (ch : C) (st : CvStack) (h : HInv key mode abs R M ch st) :
    final_node CI NI k ch st ⦃ n => RN n (RootNode key mode M) ⦄ := by
  obtain ⟨c, P, hR, ⟨F, hF, hFl⟩, hPl, hMl, hinv, hmerged, hempty⟩ := h
  have hvl := vals_length st hinv
  unfold final_node
  simp only [CvStack.impl.len, Std.bind_ok]
  split
  · rename_i hl0
    have hl0' : st.len.val = 0 := by scalar_tac
    have hv : StackProof.vals st = [] := List.length_eq_zero_iff.mp (by omega)
    have hc0 : c = 0 := by
      by_cases hP : P = []
      · rcases hempty hP with ⟨h0, _⟩ | ⟨c', j, hc', _, _, hvm⟩
        · exact h0
        · rw [hv] at hvm; simp at hvm
      · have hm := hmerged (by
          cases h' : P with
          | nil => exact absurd h' hP
          | cons _ _ => simp)
        unfold Merged at hm
        rw [hv] at hm
        have := congrArg List.length hm
        simp only [List.map_nil, List.length_nil, List.length_map, HasherProof.stackCvs_length] at this
        by_contra hne
        have := HasherProof.ones_pos _ (Nat.pos_of_ne_zero hne); omega
    have hF0 : F = [] := List.length_eq_zero_iff.mp (by rw [hFl, hc0])
    apply WP.spec_mono (hN.chunk_node ch c P hR)
    intro n hn
    refine cast (congrArg (RN n) ?_) hn
    rw [root_short key mode M (by rw [hF, hF0]; simpa using hPl), hF, hF0, hc0, List.nil_append]
  · rename_i hl0
    have hlpos : 0 < st.len.val := by scalar_tac
    step with hN.len ch c P hR as ⟨j, hj⟩
    split
    · rename_i hjpos
      have hP : 0 < P.length := by have : 0 < j.val := (by scalar_tac); omega
      have hm := hmerged hP
      step with hN.chunk_node ch c P hR as ⟨out0, hout0⟩
      have hSl : (HasherProof.stackCvs (leafN key mode M 0) (nodeOp key mode) c).length = st.len.val := by
        rw [← hvl, ← List.length_map (f := abs), hm, List.length_map]
      step with final_loop_spec key mode abs CI NI k R RN hN st hinv _ hm st.len (le_refl _) out0 _ hout0
        as ⟨out, hout⟩
      refine cast (congrArg (RN out) ?_) hout
      rw [List.take_of_length_le (by omega)]
      have hMne : M ≠ [] := by
        intro h0; rw [h0] at hF; have := congrArg List.length hF; simp only [List.length_append, List.length_nil] at this; omega
      have hML : M.length = 1024 * c + P.length := by rw [hF, List.length_append, hFl]
      have hleaf : Blake3.chunkNode key mode (toBA P) c = leafN key mode M 0 c := by
        simp only [leafN, chunkOf, Nat.sub_zero]
        rw [hF, ← hFl, List.drop_left, List.take_of_length_le hPl]
      rw [hleaf, root_long key mode M hMne, ← List.foldl_reverse,
        HasherProof.final_output_partial]
      congr 1; unfold chunks; omega
    · rename_i hjz
      have hP : P = [] := by
        have : P.length = 0 := by have : ¬ 0 < j.val := (by scalar_tac); omega
        exact List.length_eq_zero_iff.mp this
      rcases hempty hP with ⟨_, hv0⟩ | ⟨c', jj, hc'pos, hjj, hcsum, hvm⟩
      · rw [hv0] at hvl; simp at hvl; omega
      · have hSne : HasherProof.stackCvs (leafN key mode M 0) (nodeOp key mode) c' ≠ [] := by
          intro h0
          have := congrArg List.length h0
          rw [HasherProof.stackCvs_length] at this
          have h1 := HasherProof.ones_pos c' hc'pos; simp only [List.length_nil] at this; omega
        obtain ⟨A, z, hAz⟩ : ∃ A z, HasherProof.stackCvs (leafN key mode M 0) (nodeOp key mode) c' = A ++ [z] :=
          ⟨_, _, (List.dropLast_append_getLast hSne).symm⟩
        set X := goIdx (leafN key mode M 0) (nodeOp key mode) c' (2 ^ jj) with hX
        rw [hAz] at hvm
        have hvm' : (StackProof.vals st).map abs = (A ++ [z] ++ [X]).map Blake3.Node.cv := by
          rw [hvm]; simp
        have hlen : st.len.val = A.length + 2 := by
          rw [← hvl, ← List.length_map (f := abs), hvm']; simp
        step as ⟨n1, hn1⟩
        step with get_spec st hinv n1 (by omega) as ⟨a, ha⟩
        step as ⟨i2, hi2⟩
        step with get_spec st hinv i2 (by omega) as ⟨a1, ha1⟩
        step with hN.parent_node a a1 as ⟨out0, hout0⟩
        have hval : ∀ m (hm : m < (StackProof.vals st).length),
            abs ((StackProof.vals st)[m]!) = ((A ++ [z] ++ [X]).map Blake3.Node.cv)[m]'(by
              rw [← hvm', List.length_map]; exact hm) := by
          intro m hm
          rw [getElem!_pos (StackProof.vals st) m hm]
          have := congrArg (fun l : List (Vector Blake3.Word 8) => l[m]?) hvm'
          simp only [List.getElem?_map, List.getElem?_eq_getElem hm] at this
          rw [List.getElem_map]
          simp only [Option.map_some] at this
          rw [List.getElem?_eq_getElem (by simp; rw [vals_length st hinv] at hm; omega)] at this
          simpa using this
        have han : abs a = z.cv := by
          rw [ha, hval n1 (by rw [vals_length st hinv]; omega)]
          simp [List.getElem_append, hn1, hlen]
        have ha1n : abs a1 = X.cv := by
          rw [ha1, hval i2 (by rw [vals_length st hinv]; omega)]
          simp [List.getElem_append, hi2, hn1, hlen]
        have hbase : RN out0 (nodeOp key mode z X) :=
          cast (congrArg (RN out0) (by rw [han, ha1n]; rfl)) hout0
        step with final_loop_spec key mode abs CI NI k R RN hN st hinv _ hvm' n1 (by omega) out0 _ hbase
          as ⟨out, hout⟩
        have hn1A : n1.val = A.length := by omega
        refine cast (congrArg (RN out) ?_) hout
        rw [hn1A, List.append_assoc, List.take_left]
        have hfold : A.foldr (fun s acc => nodeOp key mode s acc) (nodeOp key mode z X) =
            (A ++ [z]).foldr (fun s acc => nodeOp key mode s acc) X := by simp
        have hMne : M ≠ [] := by
          intro h0; rw [h0] at hF; have := congrArg List.length hF
          simp only [List.length_append, List.length_nil, hP] at this; omega
        have hML : M.length = 1024 * c := by rw [hF, hP, List.append_nil, hFl]
        rw [hfold, ← hAz, root_long key mode M hMne, ← List.foldl_reverse,
          HasherProof.final_output_whole _ _ c' jj hjj, hcsum]
        congr 1; unfold chunks; omega

/-! ## Updates, and the result -/

open hashercore in
/-- A new Hasher: an empty chunk numbered 0 and an empty stack. -/
theorem init_spec {C : Type} (R : C → Nat → List Std.U8 → Prop) (ch : C) (hch : R ch 0 []) :
    HInv key mode abs R [] ch ⟨none, 0#usize⟩ :=
  ⟨0, [], hch, ⟨[], rfl, rfl⟩, by simp, by simp, ⟨by simp, fun _ => rfl⟩, fun h => by simp at h,
    fun _ => Or.inl ⟨rfl, rfl⟩⟩

open hashercore in
/-- One update, as the library's `update_pooled` makes it: `fill`, and when
input is left, `feed` (on kernels of its own: an SME2 turn's). -/
def update {C K : Type} (CI : Chunk C) (FI₁ FI₂ : Feed K C) (k₁ k₂ : K) (ch : C) (st : CvStack)
    (input : Slice Std.U8) : Result (C × CvStack) := do
  let (rest, ch1, st1) ← fill CI FI₁ k₁ ch st 0#u64 input
  if rest.len = 0#usize then ok (ch1, st1) else feed CI FI₂ k₂ ch1 st1 0#u64 rest

open hashercore in
/-- An update keeps the Hasher's state: after it, the state after all the
bytes so far and the update's. -/
theorem update_spec {C K : Type} (CI : Chunk C) (FI₁ FI₂ : Feed K C) (k₁ k₂ : K)
    (R : C → Nat → List Std.U8 → Prop)
    (hK₁ : Contracts CI FI₁ k₁ key mode abs R) (hK₂ : Contracts CI FI₂ k₂ key mode abs R)
    (M : List Std.U8) (ch : C) (st : CvStack) (h : HInv key mode abs R M ch st) (input : Slice Std.U8)
    (hbound : M.length + input.length < 1024 * 2 ^ 54) :
    update CI FI₁ FI₂ k₁ k₂ ch st input ⦃ r => HInv key mode abs R (M ++ input.val) r.1 r.2 ⦄ := by
  unfold update
  step with fill_spec key mode abs CI FI₁ k₁ R hK₁ M ch st h input hbound as ⟨rest, ch1, st1, h0, hpos⟩
  split
  · rename_i hz
    simp only [WP.spec_ok]
    exact h0 (by simp only [Slice.length]; scalar_tac)
  · rename_i hnz
    exact feed_spec key mode abs CI FI₂ k₂ R hK₂ _ ch1 st1 rest
      (hpos (by have : rest.len.val ≠ 0 := by scalar_tac
                simp only [Slice.length]; scalar_tac))

open hashercore in
/-- Updates with each piece in turn. -/
def updates {C K : Type} (CI : Chunk C) (FI₁ FI₂ : Feed K C) (k₁ k₂ : K) :
    C → CvStack → List (Slice Std.U8) → Result (C × CvStack)
  | ch, st, [] => ok (ch, st)
  | ch, st, x :: xs => do
    let (ch1, st1) ← update CI FI₁ FI₂ k₁ k₂ ch st x
    updates CI FI₁ FI₂ k₁ k₂ ch1 st1 xs

open hashercore in
theorem updates_spec {C K : Type} (CI : Chunk C) (FI₁ FI₂ : Feed K C) (k₁ k₂ : K)
    (R : C → Nat → List Std.U8 → Prop)
    (hK₁ : Contracts CI FI₁ k₁ key mode abs R) (hK₂ : Contracts CI FI₂ k₂ key mode abs R)
    (pieces : List (Slice Std.U8)) (M : List Std.U8) (ch : C) (st : CvStack) (h : HInv key mode abs R M ch st)
    (hbound : M.length + (pieces.map (fun x => x.length)).sum < 1024 * 2 ^ 54) :
    updates CI FI₁ FI₂ k₁ k₂ ch st pieces ⦃ r =>
      HInv key mode abs R (M ++ (pieces.map (fun x => x.val)).flatten) r.1 r.2 ⦄ := by
  induction pieces generalizing M ch st with
  | nil => simp only [updates, WP.spec_ok, List.map_nil, List.flatten_nil, List.append_nil]; exact h
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons] at hbound
    unfold updates
    step with update_spec key mode abs CI FI₁ FI₂ k₁ k₂ R hK₁ hK₂ M ch st h x (by omega)
      as ⟨ch1, st1, h1⟩
    have := ih (M ++ x.val) ch1 st1 h1 (by rw [List.length_append]; simp only [Slice.length] at hbound ⊢; omega)
    simpa [List.append_assoc] using this

open hashercore in
/-- The Hasher: a new one, any updates, then its root's node, given kernels
that meet their contracts: the specification's root over all the updates'
bytes, whose 32-byte output is `Blake3.blake3 key mode` of them
(`blake3_root`). -/
theorem hasher_spec {C K N : Type} (CI : Chunk C) (FI₁ FI₂ : Feed K C) (NI : Nodes K C N) (k₁ k₂ k : K)
    (R : C → Nat → List Std.U8 → Prop) (RN : N → Blake3.Node → Prop)
    (hK₁ : Contracts CI FI₁ k₁ key mode abs R) (hK₂ : Contracts CI FI₂ k₂ key mode abs R)
    (hN : NodeContracts CI NI k key mode abs R RN)
    (ch0 : C) (hch0 : R ch0 0 []) (pieces : List (Slice Std.U8))
    (hbound : (pieces.map (fun x => x.length)).sum < 1024 * 2 ^ 54) :
    (do let (ch, st) ← updates CI FI₁ FI₂ k₁ k₂ ch0 ⟨none, 0#usize⟩ pieces
        final_node CI NI k ch st) ⦃ n =>
      RN n (RootNode key mode (pieces.map (fun x => x.val)).flatten) ⦄ := by
  step with updates_spec key mode abs CI FI₁ FI₂ k₁ k₂ R hK₁ hK₂ pieces [] ch0 _
    (init_spec key mode abs R ch0 hch0) (by simpa using hbound) as ⟨ch, st, h⟩
  simp only [List.nil_append] at h
  exact final_node_spec key mode abs CI NI k R RN hN _ ch st h

/-- The specification's 32-byte hash of the bytes `M`: the output of its root. -/
theorem blake3_root (M : List Std.U8) :
    Blake3.blake3 key mode (toBA M) 32 = Blake3.output (RootNode key mode M) 32 := rfl

end

end HasherCoreProof

#print axioms HasherCoreProof.feed_loop_spec
#print axioms HasherCoreProof.feed_spec
#print axioms HasherCoreProof.fill_spec
#print axioms HasherCoreProof.final_node_spec
#print axioms HasherCoreProof.update_spec
#print axioms HasherCoreProof.init_spec
#print axioms HasherCoreProof.hasher_spec

