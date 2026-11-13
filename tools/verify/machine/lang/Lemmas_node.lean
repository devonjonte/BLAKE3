import Lemmas_merge
import Spec_nodeout
open X86 Cells

/-! # A node in memory, and `node_out`: lemmas for the prover

Written by hand; the source names them. Checked by Lean; not to be read. -/

unseal Kernels.out in
/-- **What a one-block kernel leaves, for any chaining value, block, counter, length and flags, is the first
eight words of the specification's compression of them.** -/
theorem Kernels.out_is (k0 k1 b0 b1 b2 b3 : V) (t : UInt64) (len fl : UInt32) (c : BitVec 64) (L F : BitVec 32)
    (hc : c = t.toBitVec) (hL : L = bv len) (hF : F = bv fl) :
    words8 (Kernels.out k0 k1 b0 b1 b2 b3 c L F).1 (Kernels.out k0 k1 b0 b1 b2 b3 c L F).2
      = Blake3.first8 (Blake3.BLAKE3_COMPRESS (words8 k0 k1) (words8 b0 b1 ++ words8 b2 b3) t len fl) := by
  have h := specCv_is_the_specifications (words8 k0 k1) (words8 b0 b1 ++ words8 b2 b3) t len fl
  rw [words8_bv, block_bv] at h
  subst hc hL hF
  simp only [Kernels.out, h, words8, dw_mk4_0, dw_mk4_1, dw_mk4_2, dw_mk4_3]
  ext i hi
  match i, hi with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ => simp [bv]

theorem Block.At.frame {m m' : Mem} {a : BitVec 64} {b : Vector Blake3.Word 16} (h : Block.At m a b)
    (same : ∀ x : BitVec 64, x - a < 64#64 → m' x = m x) : Block.At m' a b := by
  obtain ⟨v0, v1, v2, v3, h0, h1, h2, h3, hw⟩ := h
  exact ⟨v0, v1, v2, v3, vec_congr (fun x hx => same x (by bv_omega)) h0, vec_congr (fun x hx => same x (by bv_omega)) h1,
    vec_congr (fun x hx => same x (by bv_omega)) h2, vec_congr (fun x hx => same x (by bv_omega)) h3, hw⟩

/-- A node's tail is in its own 88 bytes. -/
theorem Node.Tail.frame {m m' : Mem} {a : BitVec 64} {n : Blake3.Node} (h : Node.Tail m a n)
    (same : ∀ x : BitVec 64, x - a < 88#64 → m' x = m x) : Node.Tail m' a n := by
  obtain ⟨hm, ht, hl, hf, bl, bf⟩ := h
  exact ⟨Block.At.frame hm (fun x hx => same x (by bv_omega)), quad_congr (fun x hx => same x (by bv_omega)) ht,
    quad_congr (fun x hx => same x (by bv_omega)) hl, quad_congr (fun x hx => same x (by bv_omega)) hf, bl, bf⟩

/-- The node is in its own 120 bytes: a memory that agrees on them holds it too. -/
theorem Node.At.frame {m m' : Mem} {a : BitVec 64} {n : Blake3.Node} (h : Node.At m a n)
    (same : ∀ x : BitVec 64, x - a < 120#64 → m' x = m x) : Node.At m' a n :=
  ⟨Cv.At.frame h.1 (fun x hx => same x (by bv_omega)), Node.Tail.frame h.2 (fun x hx => same x (by bv_omega))⟩

/-- What a holder of a node may read at once: its three words, and their bounds. -/
theorem Node.At.cells {m : Mem} {a : BitVec 64} {n : Blake3.Node} (h : Node.At m a n) :
    Quad m (a + 96#64) n.t.toBitVec ∧ Quad m (a + 104#64) (n.len.toBitVec.setWidth 64) ∧
    Quad m (a + 112#64) (n.flags.toBitVec.setWidth 64) ∧ n.len.toBitVec ≤ 64#32 ∧ n.flags.toBitVec < 256#32 := by
  obtain ⟨_, _, ht, hl, hf, bl, bf⟩ := h
  refine ⟨?_, ?_, ?_, bl, bf⟩
  · rw [show a + 96#64 = a + 32#64 + 64#64 by bv_decide]; exact ht
  · rw [show a + 104#64 = a + 32#64 + 72#64 by bv_decide]; exact hl
  · rw [show a + 112#64 = a + 32#64 + 80#64 by bv_decide]; exact hf

/-- A node's `h` and block, as the six vectors a kernel reads. -/
theorem Node.At.vectors {m : Mem} {a : BitVec 64} {n : Blake3.Node} (h : Node.At m a n) :
    ∃ h0 h1 b0 b1 b2 b3 : V, Vec m a h0 ∧ Vec m (a + 16#64) h1 ∧ Vec m (a + 32#64) b0 ∧ Vec m (a + 48#64) b1 ∧
      Vec m (a + 64#64) b2 ∧ Vec m (a + 80#64) b3 ∧ words8 h0 h1 = n.h ∧ words8 b0 b1 ++ words8 b2 b3 = n.m := by
  obtain ⟨⟨h0, h1, hh0, hh1, hw⟩, ⟨b0, b1, b2, b3, hb0, hb1, hb2, hb3, hb⟩, _⟩ := h
  refine ⟨h0, h1, b0, b1, b2, b3, hh0, hh1, hb0, ?_, ?_, ?_, hw, hb⟩
  · rw [show a + 48#64 = a + 32#64 + 16#64 by bv_decide]; exact hb1
  · rw [show a + 64#64 = a + 32#64 + 32#64 by bv_decide]; exact hb2
  · rw [show a + 80#64 = a + 32#64 + 48#64 by bv_decide]; exact hb3

/-- **At the return:** what the kernel left at `out` is the node's compression with the flag asked for. -/
theorem NodeOut.exit {m' : Mem} {out root : BitVec 64} {n : Blake3.Node} {h0 h1 b0 b1 b2 b3 : V} {L F : BitVec 32}
    (hw : words8 h0 h1 = n.h) (hb : words8 b0 b1 ++ words8 b2 b3 = n.m)
    (hp0 : Vec m' out (Kernels.out h0 h1 b0 b1 b2 b3 n.t.toBitVec L F).1)
    (hp1 : Vec m' (out + 16#64) (Kernels.out h0 h1 b0 b1 b2 b3 n.t.toBitVec L F).2)
    (hL : L = n.len.toBitVec) (hF : F = n.flags.toBitVec ||| root.setWidth 32) :
    True ∧ Cv.At m' out (Node.out n ⟨root.setWidth 32⟩) := by
  refine ⟨trivial, _, _, hp0, hp1, ?_⟩
  rw [Kernels.out_is h0 h1 b0 b1 b2 b3 n.t n.len (n.flags ||| ⟨root.setWidth 32⟩) _ L F rfl hL (by rw [hF]; rfl), hw, hb]
  rfl
