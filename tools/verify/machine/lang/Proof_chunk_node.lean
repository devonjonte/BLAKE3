import Cells
import Kernels
import AbiProof
import AbiCall
import Spec_chunknode
import Lemmas_chunk
import Proof_pad
import Code_chunk_node
open X86 Cells

/-! # `chunk_node`, as assembled, meets `ChunkNode.contract`

Written by prove_fn.py from levels.ode and the compiler's layout; not edited by hand, and not to be read
but for its last theorem's statement: Lean checks the rest. The frame: 160 bytes below the stack pointer at entry
(`fb` is its lowest address), the caller's rbx, rbp, r12, r13, r14, r15 at its top.
-/

namespace Proof_chunk_node

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option linter.unusedVariables false

/-- What holds each time the loop's head is reached: the source's `invariant` clauses, each variable where the
compiler keeps it, and the frame as the compiler keeps it. -/
def Inv (fb nd input len counter flags plat ra : BitVec 64) (sv : Abi.Saved) (k : Blake3.CV) (bytes : List (BitVec 8)) (m0 : Mem) (s : State) : Prop :=
  s.pc = 0xF003E ∧
  s.rsp = (fb + 72#64) ∧
  s.r13 = nd ∧
  s.r14 = counter ∧
  s.r15 = plat ∧
  Region s.mem fb 160#64 ∧
  Quad s.mem (fb + 160#64) ra ∧
  Quad s.mem (fb + 152#64) sv.rbx ∧
  Quad s.mem (fb + 144#64) sv.rbp ∧
  Quad s.mem (fb + 136#64) sv.r12 ∧
  Quad s.mem (fb + 128#64) sv.r13 ∧
  Quad s.mem (fb + 120#64) sv.r14 ∧
  Quad s.mem (fb + 112#64) sv.r15 ∧
  Quad s.mem (fb + 72#64) input ∧
  Quad s.mem (fb + 80#64) len ∧
  Quad s.mem (fb + 88#64) flags ∧
  Abi.AllApart ((fb, (Abi.Contract.framed (ChunkNode.contract nd input len counter flags plat k bytes) 160#64).stack + 8#64) :: (Abi.Contract.framed (ChunkNode.contract nd input len counter flags plat k bytes) 160#64).regions) ∧
  (∀ x : BitVec 64, (Abi.Contract.framed (ChunkNode.contract nd input len counter flags plat k bytes) 160#64).stack + 8#64 ≤ x - fb → (∀ r ∈ (Abi.Contract.framed (ChunkNode.contract nd input len counter flags plat k bytes) 160#64).modifies, r.2 ≤ x - r.1) → s.mem x = m0 x) ∧
  (Abi.Contract.framed (ChunkNode.contract nd input len counter flags plat k bytes) 160#64).accepts ∧
  (Abi.Contract.framed (ChunkNode.contract nd input len counter flags plat k bytes) 160#64).requires m0 ∧
  Chunk.Mid s.mem nd input len counter flags k bytes s.rbx s.rbp s.r12

theorem enter (fb nd input len counter flags plat ra : BitVec 64) (sv : Abi.Saved) (k : Blake3.CV) (bytes : List (BitVec 8)) (m0 : Mem)
    (s : State) (hP : Abi.Pre 0xF0000 (Abi.Contract.framed (ChunkNode.contract nd input len counter flags plat k bytes) 160#64) fb ra sv m0 s) : ∃ n_ s', steps Code_chunk_node.prog n_ s = some s' ∧ Inv fb nd input len counter flags plat ra sv k bytes m0 s' := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r12, r13, r14, r15, zf, cf, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, mem, pc⟩ := s
  obtain ⟨hpc, hsp, hargs, hbx, hbp, h12, h13, h14, h15, hmem, hF, hRa, hAp, hAcc, hReq⟩ := hP
  simp only [ChunkNode.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true] at hpc hsp hargs hbx hbp h12 h13 h14 h15 hmem hF hRa
  simp only [List.length_cons, List.length_nil, List.take, List.cons.injEq, and_true] at hargs
  obtain ⟨ha0, ha1, ha2, ha3, ha4, ha5⟩ := hargs
  subst pc rsp rdi rsi rdx rcx r8 r9 rbx rbp r12 r13 r14 r15 mem
  have hAp0 := hAp
  simp only [ChunkNode.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, Abi.AllApart, Abi.Apart, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, BitVec.reduceAdd] at hAp
  split_ands hAp
  have hAcc0 := hAcc
  try (simp only [ChunkNode.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true] at hAcc; split_ands hAcc)
  have hReq0 := hReq
  simp only [ChunkNode.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true] at hReq
  split_ands hReq
  try (have hK0 := Chunk.Mid.cells (m := m0) (by assumption); split_ands hK0)
  refine runs_then (a := 19) (s1 := ?_) ?_ ?_
  case refine_2 => run_fn []; rfl
  refine runs_done ⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try dsimp only
  · mem_region
  · mem_fact
  · mem_fact
  · mem_fact
  · mem_fact
  · mem_fact
  · mem_fact
  · mem_fact
  · mem_fact
  · mem_fact
  · mem_fact
  · exact hAp0
  · intro x hx hmod
    have hx' := hx
    have hmod' := hmod
    simp only [ChunkNode.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, BitVec.reduceAdd] at hx' hmod'
    first | rfl | mem_away
  · exact hAcc0
  · exact hReq0
  · skip
    · apply Chunk.Mid.start <;> mem_auto

theorem turn (fb nd input len counter flags plat ra : BitVec 64) (sv : Abi.Saved) (k : Blake3.CV) (bytes : List (BitVec 8)) (m0 : Mem)
    (s : State) (hI : Inv fb nd input len counter flags plat ra sv k bytes m0 s) (hc : 64#64 < s.rbp) :
    ∃ n_ s', steps Code_chunk_node.prog n_ s = some s' ∧ (Inv fb nd input len counter flags plat ra sv k bytes m0 s' ∧ s'.rbp.toNat < s.rbp.toNat) := by
  obtain ⟨rax, rcx, rdx, p, rsp, rem, rsi, rdi, r8, r9, first, r13, r14, r15, zf, cf, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, mem, pc⟩ := s
  obtain ⟨hpc, hsp, hp0, hp1, hp2, hF, hRa, hS0, hS1, hS2, hS3, hS4, hS5, hPs0, hPs1, hPs2, hAp, hOut, hAcc, hReq, hI0⟩ := hI
  simp only at hpc hsp hp0 hp1 hp2 hF hRa hS0 hS1 hS2 hS3 hS4 hS5 hPs0 hPs1 hPs2 hOut hI0 hc
  subst pc rsp r13 r14 r15
  have hAp0 := hAp
  simp only [ChunkNode.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, Abi.AllApart, Abi.Apart, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, BitVec.reduceAdd] at hAp
  split_ands hAp
  have hAcc0 := hAcc
  try (simp only [ChunkNode.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true] at hAcc; split_ands hAcc)
  have hReq0 := hReq
  simp only [ChunkNode.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true] at hReq
  split_ands hReq
  forget_about m0 except hOut hReq0
  try (have hK0 := Chunk.Mid.cells (m := mem) (by assumption); split_ands hK0)
  have_by hO0 := Chunk.Mid.block (m := mem)
  obtain ⟨h0, h1, b0, b1, b2, b3, hO0⟩ := hO0
  try norm_addr at hO0
  split_ands hO0
  by_cases hs1 : plat = 5#64
  · have c0 : (64#64).ult (rem) = true := by bv_decide
    have c1 : (plat - 5#64 == 0#64) = true := by bv_decide
    refine runs_then (a := 17) (s1 := ?_) ?_ ?_
    case refine_2 => run_fn [c0, c1]; rfl
    refine Kernels.call_avx_runs Code_chunk_node.has_kernels (by mem_auto) (by mem_auto) (by mem_auto) (by mem_auto) (by mem_auto) (by mem_auto) (by mem_auto) (by mem_auto) ?_
    intro rax' rcx' rdx' rsi' rdi' r8' r9' zf' cf' y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15
    refine runs_then (a := 10) (s1 := ?_) ?_ ?_
    case refine_2 => run_fn [c0, c1]; rfl
    refine runs_done ⟨⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    all_goals try dsimp only
    · mem_region
    · mem_fact
    · mem_fact
    · mem_fact
    · mem_fact
    · mem_fact
    · mem_fact
    · mem_fact
    · mem_fact
    · mem_fact
    · mem_fact
    · exact hAp0
    · intro x hx hmod
      refine Eq.trans ?_ (hOut x hx hmod)
      have hx' := hx
      have hmod' := hmod
      simp only [ChunkNode.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, BitVec.reduceAdd] at hx' hmod'
      first | rfl | mem_away
    · exact hAcc0
    · exact hReq0
    · skip
      · apply Chunk.Mid.step <;> mem_auto
    · exact BitVec.lt_def.mp (by bv_decide)
  · have c0 : (64#64).ult (rem) = true := by bv_decide
    have c1 : (plat - 5#64 == 0#64) = false := by bv_decide
    refine runs_then (a := 17) (s1 := ?_) ?_ ?_
    case refine_2 => run_fn [c0, c1]; rfl
    refine Kernels.call_sse_runs Code_chunk_node.has_kernels (by mem_auto) (by mem_auto) (by mem_auto) (by mem_auto) (by mem_auto) (by mem_auto) (by mem_auto) (by mem_auto) (by mem_auto) (by mem_auto) ?_
    intro rax' rcx' rdx' rsi' rdi' r8' r9' zf' cf' y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15
    refine runs_then (a := 9) (s1 := ?_) ?_ ?_
    case refine_2 => run_fn [c0, c1]; rfl
    refine runs_done ⟨⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    all_goals try dsimp only
    · mem_region
    · mem_fact
    · mem_fact
    · mem_fact
    · mem_fact
    · mem_fact
    · mem_fact
    · mem_fact
    · mem_fact
    · mem_fact
    · mem_fact
    · exact hAp0
    · intro x hx hmod
      refine Eq.trans ?_ (hOut x hx hmod)
      have hx' := hx
      have hmod' := hmod
      simp only [ChunkNode.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, BitVec.reduceAdd] at hx' hmod'
      first | rfl | mem_away
    · exact hAcc0
    · exact hReq0
    · skip
      · apply Chunk.Mid.step <;> mem_auto
    · exact BitVec.lt_def.mp (by bv_decide)

theorem leave (fb nd input len counter flags plat ra : BitVec 64) (sv : Abi.Saved) (k : Blake3.CV) (bytes : List (BitVec 8)) (m0 : Mem)
    (s : State) (hI : Inv fb nd input len counter flags plat ra sv k bytes m0 s) (hc : ¬ 64#64 < s.rbp) :
    ∃ n_ s', steps Code_chunk_node.prog n_ s = some s' ∧ Abi.Post (Abi.Contract.framed (ChunkNode.contract nd input len counter flags plat k bytes) 160#64) fb ra sv m0 s' := by
  obtain ⟨rax, rcx, rdx, p, rsp, rem, rsi, rdi, r8, r9, first, r13, r14, r15, zf, cf, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, mem, pc⟩ := s
  obtain ⟨hpc, hsp, hp0, hp1, hp2, hF, hRa, hS0, hS1, hS2, hS3, hS4, hS5, hPs0, hPs1, hPs2, hAp, hOut, hAcc, hReq, hI0⟩ := hI
  simp only at hpc hsp hp0 hp1 hp2 hF hRa hS0 hS1 hS2 hS3 hS4 hS5 hPs0 hPs1 hPs2 hOut hI0 hc
  subst pc rsp r13 r14 r15
  have hAp0 := hAp
  simp only [ChunkNode.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, Abi.AllApart, Abi.Apart, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, BitVec.reduceAdd] at hAp
  split_ands hAp
  have hAcc0 := hAcc
  try (simp only [ChunkNode.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true] at hAcc; split_ands hAcc)
  have hReq0 := hReq
  simp only [ChunkNode.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true] at hReq
  split_ands hReq
  forget_about m0 except hOut hReq0
  try (have hK0 := Chunk.Mid.cells (m := mem) (by assumption); split_ands hK0)
  have_by hO0 := Chunk.Mid.last (m := mem)
  obtain ⟨_u, hO0⟩ := hO0
  try norm_addr at hO0
  split_ands hO0
  have c0 : (64#64).ult (rem) = false := by bv_decide
  refine runs_then (a := 11) (s1 := ?_) ?_ ?_
  case refine_2 => run_fn [c0]; rfl
  refine Abi.call_meets (c := Pad.contract (nd + 32#64) p rem (Chunk.rest bytes)) (ra := 983262#64)
    (Abi.Meets.mono Code_chunk_node.has_pad (Proof_pad.pad_meets (nd + 32#64) p rem (Chunk.rest bytes))) rfl rfl ?_ ?_ ?_ ?_ ?_ ?_
  · dsimp only; mem_fact
  · dsimp only [Pad.contract]; mem_subregion
  · dsimp only
    simp only [Pad.contract, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, Abi.AllApart, Abi.Apart, BitVec.reduceAdd]
    try simp only [add_sub_lit, BitVec.add_assoc, BitVec.add_zero, BitVec.reduceAdd, BitVec.reduceSub]
    repeat' (with_reducible apply And.intro)
    all_goals bv_decide
  · simp only [Pad.contract]
    repeat' (with_reducible apply And.intro)
    all_goals (first | assumption | bv_decide)
  · dsimp only
    simp only [Pad.contract, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
    repeat' (with_reducible apply And.intro)
    all_goals (first | mem_auto | (apply_frame <;> mem_auto))
  · intro s1 hpc1 hsp1 hbx1 hbp1 h12_1 h13_1 h14_1 h15_1 hens1 hout1 hown1
    obtain ⟨rax_1, rcx_1, rdx_1, rbx_1, rsp_1, rbp_1, rsi_1, rdi_1, r8_1, r9_1, r12_1, r13_1, r14_1, r15_1, zf_1, cf_1, y1_0, y1_1, y1_2, y1_3, y1_4, y1_5, y1_6, y1_7, y1_8, y1_9, y1_10, y1_11, y1_12, y1_13, y1_14, y1_15, mem1, pc_1⟩ := s1
    dsimp only at hpc1 hsp1 hbx1 hbp1 h12_1 h13_1 h14_1 h15_1 hens1 hout1 hown1
    subst pc_1 rsp_1 rbx_1 rbp_1 r12_1 r13_1 r14_1 r15_1
    simp only [Pad.contract, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true] at hens1
    split_ands hens1
    simp only [Pad.contract, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, add_sub_lit, BitVec.add_assoc, BitVec.add_zero, BitVec.reduceAdd, BitVec.reduceSub] at hout1
    have hF1 : Region mem1 fb 160#64 := hown1 fb 160#64 (by mem_region)
    have hS1_0 : Quad mem1 (fb + 160#64) ra := X86.Quad.frame (by mem_fact) (fun x hx => hout1 x (by bv_decide) (by bv_decide))
    have hS1_1 : Quad mem1 (fb + 152#64) sv.rbx := X86.Quad.frame (by mem_fact) (fun x hx => hout1 x (by bv_decide) (by bv_decide))
    have hS1_2 : Quad mem1 (fb + 144#64) sv.rbp := X86.Quad.frame (by mem_fact) (fun x hx => hout1 x (by bv_decide) (by bv_decide))
    have hS1_3 : Quad mem1 (fb + 136#64) sv.r12 := X86.Quad.frame (by mem_fact) (fun x hx => hout1 x (by bv_decide) (by bv_decide))
    have hS1_4 : Quad mem1 (fb + 128#64) sv.r13 := X86.Quad.frame (by mem_fact) (fun x hx => hout1 x (by bv_decide) (by bv_decide))
    have hS1_5 : Quad mem1 (fb + 120#64) sv.r14 := X86.Quad.frame (by mem_fact) (fun x hx => hout1 x (by bv_decide) (by bv_decide))
    have hS1_6 : Quad mem1 (fb + 112#64) sv.r15 := X86.Quad.frame (by mem_fact) (fun x hx => hout1 x (by bv_decide) (by bv_decide))
    have hS1_7 : Quad mem1 (fb + 72#64) input := X86.Quad.frame (by mem_fact) (fun x hx => hout1 x (by bv_decide) (by bv_decide))
    have hS1_8 : Quad mem1 (fb + 80#64) len := X86.Quad.frame (by mem_fact) (fun x hx => hout1 x (by bv_decide) (by bv_decide))
    have hS1_9 : Quad mem1 (fb + 88#64) flags := X86.Quad.frame (by mem_fact) (fun x hx => hout1 x (by bv_decide) (by bv_decide))
    have hK1_0 : Cv.At mem1 nd (Chunk.h k flags counter bytes) := Cv.At.frame (m := mem) (by assumption) (fun x hx => by rw [hout1 x (by bv_decide) (by bv_decide)]; first | rfl | mem_away)
    have hK1_1 : Region mem1 nd 120#64 := hown1 _ _ (by mem_region)
    have hOut : (∀ x : BitVec 64, (Abi.Contract.framed (ChunkNode.contract nd input len counter flags plat k bytes) 160#64).stack + 8#64 ≤ x - fb → (∀ r ∈ (Abi.Contract.framed (ChunkNode.contract nd input len counter flags plat k bytes) 160#64).modifies, r.2 ≤ x - r.1) → mem1 x = m0 x) := by
      intro x hx hmod
      have hx' := hx
      have hmod' := hmod
      simp only [ChunkNode.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, BitVec.reduceAdd] at hx' hmod'
      rw [hout1 x (by bv_decide) (by bv_decide)]
      refine Eq.trans ?_ (hOut x hx hmod); first | rfl | mem_away
    clear hout1 hown1
    refine runs_then (a := 22) (s1 := ?_) ?_ ?_
    case refine_2 => run_fn [c0]; rfl
    refine runs_done ⟨rfl, by simp only [ChunkNode.contract, Abi.Contract.framed]; bv_decide, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
    all_goals try dsimp only
    · intro x hx hmod
      refine Eq.trans ?_ (hOut x hx hmod)
      have hx' := hx
      have hmod' := hmod
      simp only [ChunkNode.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, BitVec.reduceAdd] at hx' hmod'
      first | rfl | mem_away
    · simp only [ChunkNode.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
      apply ChunkNode.exit <;> mem_auto

/-- **`chunk_node`, as assembled, meets its contract, whatever its arguments.** -/
theorem chunk_node_meets : ∀ (nd input len counter flags plat : BitVec 64) (k : Blake3.CV) (bytes : List (BitVec 8)),
    Abi.Meets Code_chunk_node.prog 0xF0000 (ChunkNode.contract nd input len counter flags plat k bytes) := by
  intro nd input len counter flags plat k bytes
  refine Abi.meets_of_triple 160#64 (by dsimp only [ChunkNode.contract]; decide) (by dsimp only [ChunkNode.contract]; decide) (fun fb ra sv m0 => ?_)
  refine Hoare.seq (Q := Inv fb nd input len counter flags plat ra sv k bytes m0) ?_ ?_
  · intro s hP
    exact enter fb nd input len counter flags plat ra sv k bytes m0 s hP
  · refine Hoare.loop (fun s => s.rbp.toNat) (fun s hI => ?_)
    by_cases hc : 64#64 < s.rbp
    · obtain ⟨n_, s', h, hi, hm⟩ := turn fb nd input len counter flags plat ra sv k bytes m0 s hI hc
      exact ⟨n_, s', h, Or.inl ⟨hi, hm⟩⟩
    · obtain ⟨n_, s', h, hq⟩ := leave fb nd input len counter flags plat ra sv k bytes m0 s hI hc
      exact ⟨n_, s', h, Or.inr hq⟩

#print axioms chunk_node_meets

end Proof_chunk_node
