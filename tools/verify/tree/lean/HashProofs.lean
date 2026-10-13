import ChildrenProofs
open Aeneas Aeneas.Std Result
open Bridge WideBridge ChildrenProof

/-! # The hash

`hash` (src/tree_core.rs) hashes an input of one chunk or less with
`chunk_root`, and otherwise finds the root's two children (`root_children`:
the SME2 kernels' `children` where they have one, else `children` over
arrays sized for the input) and hashes their parent with `parent_root`.
Given kernels that meet their contracts, it returns the specification's
32-byte output: `Blake3.blake3 key mode input 32`. -/

namespace HashProof

/-- The root's children. -/
theorem root_children_spec {K : Type} (KI : widecore.Kernels K) (k : K) (D d : Nat) (hD : D = 2 ^ d) (hDmax : D ≤ 128)
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
    (hchildren : ∀ (input : Slice Std.U8) (ahead : Std.Usize) (counter : Std.U64),
      1024 < input.length →
      KI.children k input ahead counter ⦃ o => ∀ c, o = some c → ∃ L R : Blake3.Node,
        nodeOp key mode L R = goIdx (leafN key mode input.val counter.val) (nodeOp key mode) counter.val
          (chunks input.length) ∧ c.val.map abs = [L.cv, R.cv] ⦄)
    (hchunk_spec : ∀ b i, abs (chunkf b i) = (Blake3.chunkNode key mode (toBA b) i).cv)
    (hparent_spec : ∀ a b, abs (parentf a b) = cvOp key mode (abs a) (abs b))
    (input : Slice Std.U8) (ahead : Std.Usize) (counter : Std.U64)
    (h2 : 1024 < input.length) (hfit : counter.val + input.length / 1024 + 1 ≤ Std.U64.max)
    (hahead : input.length + ahead.val ≤ Std.Usize.max) :
    widecore.root_children KI k input ahead counter ⦃ r => ∃ L R : Blake3.Node,
      nodeOp key mode L R = goIdx (leafN key mode input.val counter.val) (nodeOp key mode) counter.val
        (chunks input.length) ∧
      r.val.map abs = [L.cv, R.cv] ⦄ := by
  unfold widecore.root_children
  step with hchildren input ahead counter h2 as ⟨o, ho⟩
  cases o with
  | some c => simp only [WP.spec_ok]; exact ho c rfl
  | none =>
    simp only
    step as ⟨i1, i1_post⟩
    · simp [widecore.SMALL, widecore.CHUNK_LEN]; scalar_tac
    have hi1 : i1.val = 16 * 1024 := by simp [i1_post, widecore.SMALL, widecore.CHUNK_LEN]
    have hchunks16 : ∀ m : Nat, m ≤ 16 * 1024 → chunks m ≤ 16 := by intro m hm; unfold chunks; omega
    step*
    all_goals
      have hsl := congrArg List.length s_post
      have hs1l := congrArg List.length s1_post
      simp at hsl hs1l
      step with children_spec KI k D d hD hDmax key mode abs chunkf parentf degU hdegU hdeg hchunks hparents
        hsubtree hchunk_spec hparent_spec input ahead counter s s1 h2 hfit hahead
        (by
          first
          | (simp only [Slice.length] at *; omega)
          | (have hb : input.len ≤ i1 := by assumption
             have hl : input.length ≤ 16 * 1024 := by simp only [Slice.length]; scalar_tac
             have := hchunks16 _ hl
             simp only [Slice.length] at *
             omega))
        (by simp only [Slice.length] at *; omega)
        as ⟨c, cv1, nx1, L, R, hLR, hmap⟩
      exact ⟨L, R, hLR, hmap⟩

/-- The hash: given kernels that meet their contracts, `hash` returns the
specification's 32-byte output of the input, `Blake3.blake3 key mode input 32`. -/
theorem hash_spec {K : Type} (KI : widecore.Kernels K) (k : K) (D d : Nat) (hD : D = 2 ^ d) (hDmax : D ≤ 128)
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
    (hchildren : ∀ (input : Slice Std.U8) (ahead : Std.Usize) (counter : Std.U64),
      1024 < input.length →
      KI.children k input ahead counter ⦃ o => ∀ c, o = some c → ∃ L R : Blake3.Node,
        nodeOp key mode L R = goIdx (leafN key mode input.val counter.val) (nodeOp key mode) counter.val
          (chunks input.length) ∧ c.val.map abs = [L.cv, R.cv] ⦄)
    (hchunk_root : ∀ input : Slice Std.U8, input.length ≤ 1024 →
      KI.chunk_root k input ⦃ r => toBA r.val = Blake3.output (Blake3.chunkNode key mode (toBA input.val) 0) 32 ⦄)
    (hparent_root : ∀ c : Std.Array Cv 2#usize,
      KI.parent_root k c ⦃ r => toBA r.val =
        Blake3.output (Blake3.parentNode key mode (abs c.val[0]!) (abs c.val[1]!)) 32 ⦄)
    (hchunk_spec : ∀ b i, abs (chunkf b i) = (Blake3.chunkNode key mode (toBA b) i).cv)
    (hparent_spec : ∀ a b, abs (parentf a b) = cvOp key mode (abs a) (abs b))
    (input : Slice Std.U8) (hfit : input.length / 1024 + 1 ≤ Std.U64.max) :
    widecore.hash KI k input ⦃ r => toBA r.val = Blake3.blake3 key mode (toBA input.val) 32 ⦄ := by
  unfold widecore.hash
  simp only
  split
  next hle =>
    have hl : input.length ≤ 1024 := by simp only [Slice.length]; simp [widecore.CHUNK_LEN] at hle; scalar_tac
    step with hchunk_root input hl as ⟨r, hr⟩
    rw [hr, Blake3.blake3]
    have hcount : max 1 (((toBA input.val).size + 1023) / 1024) = 1 := by
      rw [toBA_size]; simp only [Slice.length] at hl; omega
    simp only [hcount, Blake3.tree]
    congr 1
    rw [Blake3.tree.go]
    simp only [Array.size_map, Array.size_range, Nat.le_refl, ↓reduceDIte]
    rw [getElem!_pos _ 0 (by simp)]
    simp only [Array.getElem_map, Array.getElem_range, Nat.mul_zero, Nat.zero_add, toBA_extract, List.drop_zero,
      Nat.sub_zero, Nat.mul_one]
    rw [List.take_of_length_le (by simp only [Slice.length] at hl; omega)]
  next hgt =>
    have h2 : 1024 < input.length := by simp only [Slice.length]; simp [widecore.CHUNK_LEN] at hgt; scalar_tac
    have hne : input.val ≠ [] := by
      intro h; simp only [Slice.length, h, List.length_nil] at h2; omega
    step with root_children_spec KI k D d hD hDmax key mode abs chunkf parentf degU hdegU hdeg hchunks hparents
      hsubtree hchildren hchunk_spec hparent_spec input 0#usize 0#u64 h2 (by simpa using hfit)
      (by simp) as ⟨c, L, R, hLR, hmap⟩
    step with hparent_root c as ⟨r, hr⟩
    rw [hr, Blake3.blake3]
    obtain ⟨x, y, hxy⟩ : ∃ x y, c.val = [x, y] := by
      have hl2 : c.val.length = 2 := by simp
      match h : c.val, hl2 with
      | [x, y], _ => exact ⟨x, y, rfl⟩
    rw [hxy] at hmap ⊢
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hmap
    obtain ⟨hx, hy⟩ := hmap
    show Blake3.output (Blake3.parentNode key mode (abs x) (abs y)) 32 = _
    rw [hx, hy, ← goIdx_leafN_root key mode input.val hne]
    have hLR' := hLR
    simp only [Slice.length] at hLR'
    rw [← hLR']
    rfl

#print axioms HashProof.hash_spec

end HashProof

#print axioms HashProof.root_children_spec
