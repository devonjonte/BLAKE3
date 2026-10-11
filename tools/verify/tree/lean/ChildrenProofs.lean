import WideProofs
open Aeneas Aeneas.Std Result
open Bridge WideBridge

/-! # The root's two children

`children` (src/tree_core.rs) walks the input (`wide`), then condenses its
chaining values a layer of parents at a time until two are left: the
chaining values of the root's two children. Here the walk's values are
followed as the specification's nodes, whose chaining values they are; the
two left are the children of the specification's root node. -/

namespace ChildrenProof

/-- A layer commutes with a map that commutes with the node operation. -/
theorem layerL_map {α β : Type} (f : α → β) (node : α → α → α) (node' : β → β → β)
    (hf : ∀ a b, f (node a b) = node' (f a) (f b)) (l : List α) :
    (layerL node l).map f = layerL node' (l.map f) := by
  induction l using layerL.induct with
  | case1 a b rest ih => simp [layerL, ih, hf]
  | case2 l h => cases l with
    | nil => simp [layerL]
    | cons a t => cases t with
      | nil => simp [layerL]
      | cons b r => exact absurd rfl (h a b r)

/-- The walk's model commutes with such a map too. -/
theorem wideI_map {α β : Type} (f : α → β) (node : α → α → α) (node' : β → β → β)
    (hf : ∀ a b, f (node a b) = node' (f a) (f b)) (D : Nat) (leaf : Nat → α) (start n : Nat) :
    (wideI D leaf node start n).map f = wideI D (fun i => f (leaf i)) node' start n := by
  induction n using Nat.strong_induction_on generalizing start with
  | _ n ih =>
  rw [wideI, wideI]
  split
  · simp
  · split
    · simp
    · have := Nat.log2_self_le (n := n - 1) (by omega)
      have := Nat.one_le_two_pow (n := (n - 1).log2)
      simp only
      rw [← ih _ (by omega), ← ih _ (by omega)]
      simp only [List.length_map]
      split
      · simp
      · rw [layerL_map f node node' hf, List.map_append]

/-- The tree over two values is their parent. -/
theorem treeL_pair {α : Type} [Inhabited α] (node : α → α → α) (a b : α) :
    treeL node [a, b] = node a b := by
  simp [treeL, goIdx]

/-- The node operation: the specification's parent of two nodes. -/
def nodeOp (key : Vector Blake3.Word 8) (mode : Blake3.Word) (a b : Blake3.Node) : Blake3.Node :=
  Blake3.parentNode key mode a.cv b.cv

/-- The specification's tree is goIdx over its nodes, as nodes. -/
theorem goIdx_tree_node (key : Vector Blake3.Word 8) (mode : Blake3.Word) (chunks : Array Blake3.Node)
    (start n : Nat) :
    Blake3.tree.go key mode chunks start n = goIdx (fun i => chunks[i]!) (nodeOp key mode) start n := by
  induction n using Nat.strong_induction_on generalizing start with
  | _ n ih =>
  rw [Blake3.tree.go, goIdx]
  by_cases h : n ≤ 1
  · simp [h]
  · have := Nat.log2_self_le (n := n - 1) (by omega)
    have := Nat.one_le_two_pow (n := (n - 1).log2)
    simp only [h, ↓reduceDIte, ↓reduceIte, Blake3.leftCount, nodeOp]
    rw [ih _ (by omega), ih _ (by omega)]

/-- The walk's model returns at least two values for two chunks or more. -/
theorem wideI_two {α : Type} [Inhabited α] (D d : Nat) (hD : D = 2 ^ d) (leaf : Nat → α) (node : α → α → α)
    (n : Nat) (hn : 2 ≤ n) (start : Nat) : 2 ≤ (wideI D leaf node start n).length := by
  have hD1 : 1 ≤ D := by rw [hD]; exact Nat.one_le_two_pow
  rw [wideI]
  split
  · simp; omega
  · split
    · omega
    · have := Nat.log2_self_le (n := n - 1) (by omega)
      have := Nat.one_le_two_pow (n := (n - 1).log2)
      have hk2 : 2 ^ (n - 1).log2 < n := by omega
      have ha := (wideI_spec D d hD leaf node (2 ^ (n - 1).log2) (by omega) start).2.1
      have hb := (wideI_spec D d hD leaf node (n - 2 ^ (n - 1).log2) (by omega) (start + 2 ^ (n - 1).log2)).2.1
      simp only
      split
      · simp; omega
      · rename_i hne
        rw [layerL_length, List.length_append]
        omega

/-- The chaining values of a parent, as the specification computes them. -/
def cvOp (key : Vector Blake3.Word 8) (mode : Blake3.Word) (a b : Vector Blake3.Word 8) : Vector Blake3.Word 8 :=
  (Blake3.parentNode key mode a b).cv

/-- The condensing loop: while more than two values are left, a layer of
parents. Its invariant: the values left are the chaining values of a list
of the specification's nodes whose tree is `R`. -/
theorem children_loop_spec {K : Type} (KI : widecore.Kernels K) (k : K)
    (key : Vector Blake3.Word 8) (mode : Blake3.Word) (abs : Cv → Vector Blake3.Word 8)
    (parentf : Cv → Cv → Cv)
    (hparents : ∀ (children out : Slice Cv),
      2 ≤ children.length → children.length ≤ 256 → (children.length + 1) / 2 ≤ out.length →
      KI.parents k children out ⦃ r => r.1.val = (children.length + 1) / 2 ∧ r.2.length = out.length ∧
        r.2.val.take r.1.val = layerL parentf children.val ⦄)
    (hparent_spec : ∀ a b, abs (parentf a b) = cvOp key mode (abs a) (abs b))
    (R : Blake3.Node) (cvs next : Slice Cv) (n : Std.Usize)
    (hn2 : 2 ≤ n.val) (hn : n.val ≤ cvs.length) (hcap : cvs.length ≤ 256) (hnext : cvs.length ≤ 2 * next.length)
    (N : List Blake3.Node) (hN : N.length = n.val) (hmap : (cvs.val.take n.val).map abs = N.map Blake3.Node.cv)
    (htree : treeL (nodeOp key mode) N = R) :
    widecore.children_loop KI k cvs next n ⦃ r => ∃ M : List Blake3.Node, M.length = 2 ∧
      (r.1.val.take 2).map abs = M.map Blake3.Node.cv ∧ treeL (nodeOp key mode) M = R ⦄ := by
  unfold widecore.children_loop
  apply loop.spec_decr_nat (fun st : Slice Cv × Slice Cv × Std.Usize => st.2.2.val)
    (fun st : Slice Cv × Slice Cv × Std.Usize => 2 ≤ st.2.2.val ∧ st.2.2.val ≤ st.1.length ∧
      st.1.length = cvs.length ∧ st.2.1.length = next.length ∧
      ∃ N : List Blake3.Node, N.length = st.2.2.val ∧
        (st.1.val.take st.2.2.val).map abs = N.map Blake3.Node.cv ∧ treeL (nodeOp key mode) N = R)
  · rintro ⟨c, x, m⟩ ⟨hm2, hmc, hcl, hxl, N, hNl, hNmap, hNtree⟩
    unfold widecore.children_loop.body
    by_cases hgt : m > 2#usize
    · simp only [hgt, ↓reduceIte]
      step*
      have hm3 : 3 ≤ m.val := by scalar_tac
      have hsl : s.length = m.val := s_post1
      have hc' : (index_mut_back s3).val = c.val.setSlice! 0 s3.val := s1_post2 s3
      have hs3 : s3.val = next1.val.take n1.val := by rw [s3_post, s2_post, List.slice_zero_j]
      have hs3l : s3.val.length = n1.val := by rw [s3_post]; simpa [Slice.length] using s2_post1
      have hcl' : (index_mut_back s3).length = c.length := by
        simp only [Slice.length, hc', List.length_setSlice!]
      have hn1 : n1.val = (m.val + 1) / 2 := by rw [n1_post, hsl]
      have hsv : s.val = c.val.take m.val := by rw [s_post, List.slice_zero_j]
      have htake : (index_mut_back s3).val.take n1.val = layerL parentf (c.val.take m.val) := by
        rw [hc', ← hsv, ← n1_post2, ← hs3]
        simp only [List.setSlice!, List.take_zero, List.nil_append, Nat.sub_zero, Nat.zero_add]
        have : min s3.val.length c.val.length = n1.val := by
          rw [hs3l]; simp [Slice.length] at hmc; omega
        rw [this, List.take_append_of_le_length (by rw [List.length_take, hs3l]; omega),
          List.take_of_length_le (by rw [List.length_take, hs3l]; omega),
          List.take_of_length_le (by rw [hs3l])]
      refine ⟨by omega, by rw [hcl']; simp [Slice.length] at hmc ⊢; omega, by rw [hcl', hcl],
        by rw [n1_post1, hxl], ⟨layerL (nodeOp key mode) N, ?_, ?_, ?_⟩, by omega⟩
      · rw [layerL_length, hNl, hn1]
      · rw [htake, layerL_map abs parentf (cvOp key mode) hparent_spec, hNmap,
          ← layerL_map Blake3.Node.cv (nodeOp key mode) (cvOp key mode) (fun a b => rfl)]
      · rw [treeL_layerL _ _ (by omega), hNtree]
    · have hm : m.val = 2 := by scalar_tac
      simp only [hgt, ↓reduceIte, WP.spec_ok]
      exact ⟨N, by simp only at hNl; omega, by rw [← hm]; exact hNmap, hNtree⟩
  · exact ⟨hn2, hn, rfl, rfl, N, hN, hmap, htree⟩

/-- The specification's chunk node `i` of bytes whose first chunk is chunk `c`. -/
def leafN (key : Vector Blake3.Word 8) (mode : Blake3.Word) (bytes : List Std.U8) (c i : Nat) : Blake3.Node :=
  Blake3.chunkNode key mode (toBA (chunkOf bytes c i)) i

/-- `children` returns the chaining values of two nodes whose parent is the
specification's tree node over the input's chunks: the root's children. -/
theorem children_spec {K : Type} (KI : widecore.Kernels K) (k : K) (D d : Nat) (hD : D = 2 ^ d) (hDmax : D ≤ 128)
    (key : Vector Blake3.Word 8) (mode : Blake3.Word) (abs : Cv → Vector Blake3.Word 8)
    (chunkf : List Std.U8 → Nat → Cv) (parentf : Cv → Cv → Cv)
    (degU : Std.Usize) (hdegU : degU.val = D) (hdeg : KI.degree k = ok degU)
    (hchunks : ∀ (input : Slice Std.U8) (counter : Std.U64) (out : Slice Cv),
      1 ≤ input.length → input.length ≤ D * 1024 → chunks input.length ≤ out.length →
      KI.chunks k input counter out ⦃ r => r.1.val = chunks input.length ∧ r.2.length = out.length ∧
        r.2.val.take r.1.val = (List.range (chunks input.length)).map
          fun i => leafOf chunkf input.val counter.val (counter.val + i) ⦄)
    (hparents : ∀ (children out : Slice Cv),
      2 ≤ children.length → children.length ≤ 256 → (children.length + 1) / 2 ≤ out.length →
      KI.parents k children out ⦃ r => r.1.val = (children.length + 1) / 2 ∧ r.2.length = out.length ∧
        r.2.val.take r.1.val = layerL parentf children.val ⦄)
    (hsubtree : ∀ (input : Slice Std.U8) (ahead : Std.Usize) (counter : Std.U64) (out : Slice Cv),
      D * 1024 < input.length → max D 2 ≤ out.length →
      KI.subtree k input ahead counter out ⦃ r => r.2.length = out.length ∧
        ∀ n, r.1 = some n → n.val = (wideI D (leafOf chunkf input.val counter.val) parentf counter.val
          (chunks input.length)).length ∧
        r.2.val.take n.val = wideI D (leafOf chunkf input.val counter.val) parentf counter.val (chunks input.length) ⦄)
    (hchunk_spec : ∀ b i, abs (chunkf b i) = (Blake3.chunkNode key mode (toBA b) i).cv)
    (hparent_spec : ∀ a b, abs (parentf a b) = cvOp key mode (abs a) (abs b))
    (input : Slice Std.U8) (ahead : Std.Usize) (counter : Std.U64) (cvs next : Slice Cv)
    (h2 : 1024 < input.length) (hfit : counter.val + input.length / 1024 + 1 ≤ Std.U64.max)
    (hahead : input.length + ahead.val ≤ Std.Usize.max)
    (hcvs : max D 2 ≤ cvs.length) (hcap : cvs.length ≤ 256) (hnext : cvs.length ≤ 2 * next.length) :
    widecore.children KI k input ahead counter cvs next ⦃ r => ∃ L R : Blake3.Node,
      nodeOp key mode L R = goIdx (leafN key mode input.val counter.val) (nodeOp key mode) counter.val
        (chunks input.length) ∧
      r.1.val.map abs = [L.cv, R.cv] ⦄ := by
  have hc2 : 2 ≤ chunks input.length := by unfold chunks; omega
  have hspecC := wideI_spec D d hD (leafOf chunkf input.val counter.val) parentf (chunks input.length)
    (by omega) counter.val
  have hspecN := wideI_spec D d hD (leafN key mode input.val counter.val) (nodeOp key mode)
    (chunks input.length) (by omega) counter.val
  unfold widecore.children
  step with wide_spec KI k D d hD hDmax chunkf parentf degU hdegU hdeg hchunks hparents hsubtree
    input ahead counter cvs (by omega) hfit hahead (by omega) as ⟨n, cvs1, hn, hcl, htake⟩
  have hlenC := wideI_two D d hD (leafOf chunkf input.val counter.val) parentf (chunks input.length) hc2 counter.val
  have hmap : (cvs1.val.take n.val).map abs =
      (wideI D (leafN key mode input.val counter.val) (nodeOp key mode) counter.val (chunks input.length)).map
        Blake3.Node.cv := by
    rw [htake, wideI_map abs parentf (cvOp key mode) hparent_spec,
      wideI_map Blake3.Node.cv (nodeOp key mode) (cvOp key mode) (fun a b => rfl)]
    apply wideI_congr
    intro i _ _
    simp [leafOf, leafN, hchunk_spec]
  have hNl : (wideI D (leafN key mode input.val counter.val) (nodeOp key mode) counter.val
      (chunks input.length)).length = n.val := by
    have hle : n.val ≤ cvs1.val.length := by
      have := hspecC.2.2.1; simp only [Slice.length] at hcl hcvs; omega
    rw [← List.length_map (f := Blake3.Node.cv), ← hmap, List.length_map, List.length_take]
    omega
  step with children_loop_spec KI k key mode abs parentf hparents hparent_spec
    (goIdx (leafN key mode input.val counter.val) (nodeOp key mode) counter.val (chunks input.length))
    cvs1 next n (by omega) (by omega) (by omega) (by omega) _ hNl hmap hspecN.1 as ⟨cvs2, next1, M, hM2, hMmap, hMtree⟩
  obtain ⟨L, R, rfl⟩ : ∃ L R, M = [L, R] := by
    match M, hM2 with
    | [L, R], _ => exact ⟨L, R, rfl⟩
  have hc2l : 2 ≤ cvs2.val.length := by
    have := congrArg List.length hMmap
    simp only [List.length_map, List.length_take, List.length_cons, List.length_nil] at this; omega
  step*
  refine ⟨L, R, by rw [← hMtree, treeL_pair], ?_⟩
  obtain ⟨x, y, rest, hxy⟩ : ∃ x y rest, cvs2.val = x :: y :: rest := by
    match h : cvs2.val, hc2l with
    | x :: y :: rest, _ => exact ⟨x, y, rest, rfl⟩
  simp only [hxy, List.take, List.map] at hMmap
  simp_all [Std.Array.make]

/-- For a whole input (its first chunk numbered 0), the tree node over its
chunks is the specification's root node. -/
theorem goIdx_leafN_root (key : Vector Blake3.Word 8) (mode : Blake3.Word) (bytes : List Std.U8)
    (hne : bytes ≠ []) :
    goIdx (leafN key mode bytes 0) (nodeOp key mode) 0 (chunks bytes.length) =
      Blake3.tree key mode ((Array.range (max 1 (((toBA bytes).size + 1023) / 1024))).map
        fun i => Blake3.chunkNode key mode ((toBA bytes).extract (1024 * i) (1024 * (i + 1))) i) := by
  have hl : 1 ≤ bytes.length := List.length_pos_iff.mpr hne
  have hsize : max 1 (((toBA bytes).size + 1023) / 1024) = chunks bytes.length := by
    rw [toBA_size]; unfold chunks; omega
  rw [Blake3.tree, goIdx_tree_node, Array.size_map, Array.size_range, hsize]
  apply goIdx_congr
  intro i _ hi
  simp only [leafN, chunkOf, Nat.sub_zero]
  rw [getElem!_pos _ i (by simp; omega)]
  simp only [Array.getElem_map, Array.getElem_range, toBA_extract]
  congr 3
  omega
  · unfold chunks; omega

#print axioms ChildrenProof.goIdx_leafN_root
#print axioms ChildrenProof.children_spec

end ChildrenProof

#print axioms ChildrenProof.children_loop_spec
