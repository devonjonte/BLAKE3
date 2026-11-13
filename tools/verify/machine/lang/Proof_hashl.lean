import Cells
import Kernels
import AbiProof
import AbiCall
import Spec_hashl
import Lemmas_hashl
import Proof_chunk_node
import Proof_node_out
import Proof_ladd
import Proof_lroot
import Code_hashl
open X86 Cells

/-! # `hashl`, as assembled, meets `Hashl.contract`

Written by prove_fn.py from levels.ode and the compiler's layout; not edited by hand, and not to be read
but for its last theorem's statement: Lean checks the rest. The frame: 4016 bytes below the stack pointer at entry
(`fb` is its lowest address), the caller's rbx, rbp, r12, r13, r14, r15 at its top.
-/

namespace Proof_hashl

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option linter.unusedVariables false

/-- What holds each time the loop's head is reached: the source's `invariant` clauses, each variable where the
compiler keeps it, and the frame as the compiler keeps it. -/
def Inv (fb out input len key flags plat ra : BitVec 64) (sv : Abi.Saved) (k : Blake3.CV) (bytes : List (BitVec 8)) (m0 : Mem) (s : State) : Prop :=
  s.pc = 0x40060 ∧
  s.rsp = (fb + 264#64) ∧
  s.r13 = key ∧
  s.r14 = flags ∧
  s.r15 = plat ∧
  Region s.mem fb 4016#64 ∧
  Quad s.mem (fb + 4016#64) ra ∧
  Quad s.mem (fb + 4008#64) sv.rbx ∧
  Quad s.mem (fb + 4000#64) sv.rbp ∧
  Quad s.mem (fb + 3992#64) sv.r12 ∧
  Quad s.mem (fb + 3984#64) sv.r13 ∧
  Quad s.mem (fb + 3976#64) sv.r14 ∧
  Quad s.mem (fb + 3968#64) sv.r15 ∧
  Quad s.mem (fb + 3944#64) out ∧
  Quad s.mem (fb + 3952#64) input ∧
  Quad s.mem (fb + 3960#64) len ∧
  Abi.AllApart ((fb, (Abi.Contract.framed (Hashl.contract out input len key flags plat k bytes) 4016#64).stack + 8#64) :: (Abi.Contract.framed (Hashl.contract out input len key flags plat k bytes) 4016#64).regions) ∧
  (∀ x : BitVec 64, (Abi.Contract.framed (Hashl.contract out input len key flags plat k bytes) 4016#64).stack + 8#64 ≤ x - fb → (∀ r ∈ (Abi.Contract.framed (Hashl.contract out input len key flags plat k bytes) 4016#64).modifies, r.2 ≤ x - r.1) → s.mem x = m0 x) ∧
  (Abi.Contract.framed (Hashl.contract out input len key flags plat k bytes) 4016#64).accepts ∧
  (Abi.Contract.framed (Hashl.contract out input len key flags plat k bytes) 4016#64).requires m0 ∧
  Hash.In s.mem input len bytes s.rbx s.rbp s.r12 ∧
    Hash.Lv s.mem (fb + 264#64) k flags (Hash.nodes k flags bytes s.r12) ∧
    Cv.At s.mem key k ∧
    Region s.mem out 32#64

theorem enter (fb out input len key flags plat ra : BitVec 64) (sv : Abi.Saved) (k : Blake3.CV) (bytes : List (BitVec 8)) (m0 : Mem)
    (s : State) (hP : Abi.Pre 0x40000 (Abi.Contract.framed (Hashl.contract out input len key flags plat k bytes) 4016#64) fb ra sv m0 s) : ∃ n_ s', steps Code_hashl.prog n_ s = some s' ∧ Inv fb out input len key flags plat ra sv k bytes m0 s' := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r12, r13, r14, r15, zf, cf, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, mem, pc⟩ := s
  obtain ⟨hpc, hsp, hargs, hbx, hbp, h12, h13, h14, h15, hmem, hF, hRa, hAp, hAcc, hReq⟩ := hP
  simp only [Hashl.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true] at hpc hsp hargs hbx hbp h12 h13 h14 h15 hmem hF hRa
  simp only [List.length_cons, List.length_nil, List.take, List.cons.injEq, and_true] at hargs
  obtain ⟨ha0, ha1, ha2, ha3, ha4, ha5⟩ := hargs
  subst pc rsp rdi rsi rdx rcx r8 r9 rbx rbp r12 r13 r14 r15 mem
  have hAp0 := hAp
  simp only [Hashl.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, Abi.AllApart, Abi.Apart, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, BitVec.reduceAdd] at hAp
  split_ands hAp
  have hAcc0 := hAcc
  try (simp only [Hashl.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true] at hAcc; split_ands hAcc)
  have hReq0 := hReq
  simp only [Hashl.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true] at hReq
  split_ands hReq
  try (have hK0 := Hash.In.cells (m := m0) (by assumption); split_ands hK0)
  try (have hK1 := Hash.Lv.cells (m := m0) (by assumption); split_ands hK1)
  try (have hK2 := Cv.At.cells (m := m0) (by assumption); split_ands hK2)
  try (have hK3 := Region.cells (m := m0) (by assumption); split_ands hK3)
  refine runs_then (a := 22) (s1 := ?_) ?_ ?_
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
    simp only [Hashl.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, BitVec.reduceAdd] at hx' hmod'
    first | rfl | mem_away
  · exact hAcc0
  · exact hReq0
  · skip
    refine ⟨?_, ?_, ?_, ?_⟩
    · apply Hash.In.start <;> mem_auto
    · apply Hash.Lv.start <;> mem_auto
    · first | mem_auto | (apply Cv.At.frame <;> mem_auto)
    · first | mem_auto | (apply Region.frame <;> mem_auto)

theorem turn (fb out input len key flags plat ra : BitVec 64) (sv : Abi.Saved) (k : Blake3.CV) (bytes : List (BitVec 8)) (m0 : Mem)
    (s : State) (hI : Inv fb out input len key flags plat ra sv k bytes m0 s) (hc : 1024#64 < s.rbp) :
    ∃ n_ s', steps Code_hashl.prog n_ s = some s' ∧ (Inv fb out input len key flags plat ra sv k bytes m0 s' ∧ s'.rbp.toNat < s.rbp.toNat) := by
  obtain ⟨rax, rcx, rdx, p, rsp, rem, rsi, rdi, r8, r9, counter, r13, r14, r15, zf, cf, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, mem, pc⟩ := s
  obtain ⟨hpc, hsp, hp0, hp1, hp2, hF, hRa, hS0, hS1, hS2, hS3, hS4, hS5, hPs0, hPs1, hPs2, hAp, hOut, hAcc, hReq, hI0, hI1, hI2, hI3⟩ := hI
  simp only at hpc hsp hp0 hp1 hp2 hF hRa hS0 hS1 hS2 hS3 hS4 hS5 hPs0 hPs1 hPs2 hOut hI0 hI1 hI2 hI3 hc
  subst pc rsp r13 r14 r15
  have hAp0 := hAp
  simp only [Hashl.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, Abi.AllApart, Abi.Apart, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, BitVec.reduceAdd] at hAp
  split_ands hAp
  have hAcc0 := hAcc
  try (simp only [Hashl.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true] at hAcc; split_ands hAcc)
  have hReq0 := hReq
  simp only [Hashl.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true] at hReq
  split_ands hReq
  forget_about m0 except hOut hReq0
  try (have hK0 := Hash.In.cells (m := mem) (by assumption); split_ands hK0)
  try (have hK1 := Hash.Lv.cells (m := mem) (by assumption); split_ands hK1)
  try (have hK2 := Cv.At.cells (m := mem) (by assumption); split_ands hK2)
  try (have hK3 := Region.cells (m := mem) (by assumption); split_ands hK3)
  have_by hO0 := Hash.turn (m := mem)
  obtain ⟨_u, hO0⟩ := hO0
  try norm_addr at hO0
  split_ands hO0
  have_by hO1 := Cv.At.vectors (m := mem)
  obtain ⟨k0, k1, hO1⟩ := hO1
  try norm_addr at hO1
  split_ands hO1
  have c0 : (1024#64).ult (rem) = true := by bv_decide
  refine runs_then (a := 17) (s1 := ?_) ?_ ?_
  case refine_2 => run_fn [c0]; rfl
  refine Abi.call_meets (c := ChunkNode.contract (fb + 3784#64) p 1024#64 counter flags plat k (Hash.chunk bytes counter)) (ra := 262316#64)
    (Abi.Meets.mono Code_hashl.has_chunk_node (Proof_chunk_node.chunk_node_meets (fb + 3784#64) p 1024#64 counter flags plat k (Hash.chunk bytes counter))) rfl rfl ?_ ?_ ?_ ?_ ?_ ?_
  · dsimp only; mem_fact
  · dsimp only [ChunkNode.contract]; mem_subregion
  · dsimp only
    simp only [ChunkNode.contract, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, Abi.AllApart, Abi.Apart, BitVec.reduceAdd]
    try simp only [add_sub_lit, BitVec.add_assoc, BitVec.add_zero, BitVec.reduceAdd, BitVec.reduceSub]
    repeat' (with_reducible apply And.intro)
    all_goals bv_decide
  · simp only [ChunkNode.contract]
    repeat' (with_reducible apply And.intro)
    all_goals (first | assumption | bv_decide)
  · dsimp only
    simp only [ChunkNode.contract, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
    repeat' (with_reducible apply And.intro)
    all_goals (first | mem_auto | (apply_frame <;> mem_auto) | (apply_intro <;> first | mem_auto | (apply_frame <;> mem_auto)))
  · intro s1 hpc1 hsp1 hbx1 hbp1 h12_1 h13_1 h14_1 h15_1 hens1 hout1 hown1
    obtain ⟨rax_1, rcx_1, rdx_1, rbx_1, rsp_1, rbp_1, rsi_1, rdi_1, r8_1, r9_1, r12_1, r13_1, r14_1, r15_1, zf_1, cf_1, y1_0, y1_1, y1_2, y1_3, y1_4, y1_5, y1_6, y1_7, y1_8, y1_9, y1_10, y1_11, y1_12, y1_13, y1_14, y1_15, mem1, pc_1⟩ := s1
    dsimp only at hpc1 hsp1 hbx1 hbp1 h12_1 h13_1 h14_1 h15_1 hens1 hout1 hown1
    subst pc_1 rsp_1 rbx_1 rbp_1 r12_1 r13_1 r14_1 r15_1
    simp only [ChunkNode.contract, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true] at hens1
    split_ands hens1
    simp only [ChunkNode.contract, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, add_sub_lit, BitVec.add_assoc, BitVec.add_zero, BitVec.reduceAdd, BitVec.reduceSub] at hout1
    have hF1 : Region mem1 fb 4016#64 := hown1 fb 4016#64 (by mem_region)
    have hS1_0 : Quad mem1 (fb + 4016#64) ra := X86.Quad.frame (by mem_fact) (fun x hx => hout1 x (by bv_decide) (by bv_decide))
    have hS1_1 : Quad mem1 (fb + 4008#64) sv.rbx := X86.Quad.frame (by mem_fact) (fun x hx => hout1 x (by bv_decide) (by bv_decide))
    have hS1_2 : Quad mem1 (fb + 4000#64) sv.rbp := X86.Quad.frame (by mem_fact) (fun x hx => hout1 x (by bv_decide) (by bv_decide))
    have hS1_3 : Quad mem1 (fb + 3992#64) sv.r12 := X86.Quad.frame (by mem_fact) (fun x hx => hout1 x (by bv_decide) (by bv_decide))
    have hS1_4 : Quad mem1 (fb + 3984#64) sv.r13 := X86.Quad.frame (by mem_fact) (fun x hx => hout1 x (by bv_decide) (by bv_decide))
    have hS1_5 : Quad mem1 (fb + 3976#64) sv.r14 := X86.Quad.frame (by mem_fact) (fun x hx => hout1 x (by bv_decide) (by bv_decide))
    have hS1_6 : Quad mem1 (fb + 3968#64) sv.r15 := X86.Quad.frame (by mem_fact) (fun x hx => hout1 x (by bv_decide) (by bv_decide))
    have hS1_7 : Quad mem1 (fb + 3944#64) out := X86.Quad.frame (by mem_fact) (fun x hx => hout1 x (by bv_decide) (by bv_decide))
    have hS1_8 : Quad mem1 (fb + 3952#64) input := X86.Quad.frame (by mem_fact) (fun x hx => hout1 x (by bv_decide) (by bv_decide))
    have hS1_9 : Quad mem1 (fb + 3960#64) len := X86.Quad.frame (by mem_fact) (fun x hx => hout1 x (by bv_decide) (by bv_decide))
    have hK1_0 : Hash.In mem1 input len bytes p rem counter := Hash.In.frame (m := mem) (by assumption) (fun x hx => by rw [hout1 x (by bv_decide) (by bv_decide)]; first | rfl | mem_away)
    have hK1_1 : Hash.Lv mem1 (fb + 264#64) k flags (Hash.nodes k flags bytes counter) := Hash.Lv.frame (m := mem) (by assumption) (fun x hx => by rw [hout1 x (by bv_decide) (by bv_decide)]; first | rfl | mem_away)
    have hK1_2 : Cv.At mem1 key k := Cv.At.frame (m := mem) (by assumption) (fun x hx => by rw [hout1 x (by bv_decide) (by bv_decide)]; first | rfl | mem_away)
    have hK1_3 : Region mem1 out 32#64 := hown1 _ _ (by mem_region)
    have hOut : (∀ x : BitVec 64, (Abi.Contract.framed (Hashl.contract out input len key flags plat k bytes) 4016#64).stack + 8#64 ≤ x - fb → (∀ r ∈ (Abi.Contract.framed (Hashl.contract out input len key flags plat k bytes) 4016#64).modifies, r.2 ≤ x - r.1) → mem1 x = m0 x) := by
      intro x hx hmod
      have hx' := hx
      have hmod' := hmod
      simp only [Hashl.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, BitVec.reduceAdd] at hx' hmod'
      rw [hout1 x (by bv_decide) (by bv_decide)]
      refine Eq.trans ?_ (hOut x hx hmod); first | rfl | mem_away
    clear hout1 hown1
    refine runs_then (a := 5) (s1 := ?_) ?_ ?_
    case refine_2 => run_fn [c0]; rfl
    refine Abi.call_meets (c := NodeOut.contract (fb + 3912#64) (fb + 3784#64) 0#64 plat (Chunk.node k flags counter (Hash.chunk bytes counter))) (ra := 262347#64)
      (Abi.Meets.mono Code_hashl.has_node_out (Proof_node_out.node_out_meets (fb + 3912#64) (fb + 3784#64) 0#64 plat (Chunk.node k flags counter (Hash.chunk bytes counter)))) rfl rfl ?_ ?_ ?_ ?_ ?_ ?_
    · dsimp only; mem_fact
    · dsimp only [NodeOut.contract]; mem_subregion
    · dsimp only
      simp only [NodeOut.contract, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, Abi.AllApart, Abi.Apart, BitVec.reduceAdd]
      try simp only [add_sub_lit, BitVec.add_assoc, BitVec.add_zero, BitVec.reduceAdd, BitVec.reduceSub]
      repeat' (with_reducible apply And.intro)
      all_goals bv_decide
    · simp only [NodeOut.contract]
      repeat' (with_reducible apply And.intro)
      all_goals (first | assumption | bv_decide)
    · dsimp only
      simp only [NodeOut.contract, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
      repeat' (with_reducible apply And.intro)
      all_goals (first | mem_auto | (apply_frame <;> mem_auto) | (apply_intro <;> first | mem_auto | (apply_frame <;> mem_auto)))
    · intro s2 hpc2 hsp2 hbx2 hbp2 h12_2 h13_2 h14_2 h15_2 hens2 hout2 hown2
      obtain ⟨rax_2, rcx_2, rdx_2, rbx_2, rsp_2, rbp_2, rsi_2, rdi_2, r8_2, r9_2, r12_2, r13_2, r14_2, r15_2, zf_2, cf_2, y2_0, y2_1, y2_2, y2_3, y2_4, y2_5, y2_6, y2_7, y2_8, y2_9, y2_10, y2_11, y2_12, y2_13, y2_14, y2_15, mem2, pc_2⟩ := s2
      dsimp only at hpc2 hsp2 hbx2 hbp2 h12_2 h13_2 h14_2 h15_2 hens2 hout2 hown2
      subst pc_2 rsp_2 rbx_2 rbp_2 r12_2 r13_2 r14_2 r15_2
      simp only [NodeOut.contract, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true] at hens2
      split_ands hens2
      simp only [NodeOut.contract, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, add_sub_lit, BitVec.add_assoc, BitVec.add_zero, BitVec.reduceAdd, BitVec.reduceSub] at hout2
      have hF2 : Region mem2 fb 4016#64 := hown2 fb 4016#64 (by mem_region)
      have hS2_0 : Quad mem2 (fb + 4016#64) ra := X86.Quad.frame (by mem_fact) (fun x hx => hout2 x (by bv_decide) (by bv_decide))
      have hS2_1 : Quad mem2 (fb + 4008#64) sv.rbx := X86.Quad.frame (by mem_fact) (fun x hx => hout2 x (by bv_decide) (by bv_decide))
      have hS2_2 : Quad mem2 (fb + 4000#64) sv.rbp := X86.Quad.frame (by mem_fact) (fun x hx => hout2 x (by bv_decide) (by bv_decide))
      have hS2_3 : Quad mem2 (fb + 3992#64) sv.r12 := X86.Quad.frame (by mem_fact) (fun x hx => hout2 x (by bv_decide) (by bv_decide))
      have hS2_4 : Quad mem2 (fb + 3984#64) sv.r13 := X86.Quad.frame (by mem_fact) (fun x hx => hout2 x (by bv_decide) (by bv_decide))
      have hS2_5 : Quad mem2 (fb + 3976#64) sv.r14 := X86.Quad.frame (by mem_fact) (fun x hx => hout2 x (by bv_decide) (by bv_decide))
      have hS2_6 : Quad mem2 (fb + 3968#64) sv.r15 := X86.Quad.frame (by mem_fact) (fun x hx => hout2 x (by bv_decide) (by bv_decide))
      have hS2_7 : Quad mem2 (fb + 3944#64) out := X86.Quad.frame (by mem_fact) (fun x hx => hout2 x (by bv_decide) (by bv_decide))
      have hS2_8 : Quad mem2 (fb + 3952#64) input := X86.Quad.frame (by mem_fact) (fun x hx => hout2 x (by bv_decide) (by bv_decide))
      have hS2_9 : Quad mem2 (fb + 3960#64) len := X86.Quad.frame (by mem_fact) (fun x hx => hout2 x (by bv_decide) (by bv_decide))
      have hK2_0 : Hash.In mem2 input len bytes p rem counter := Hash.In.frame (m := mem1) (by assumption) (fun x hx => by rw [hout2 x (by bv_decide) (by bv_decide)]; first | rfl | mem_away)
      have hK2_1 : Hash.Lv mem2 (fb + 264#64) k flags (Hash.nodes k flags bytes counter) := Hash.Lv.frame (m := mem1) (by assumption) (fun x hx => by rw [hout2 x (by bv_decide) (by bv_decide)]; first | rfl | mem_away)
      have hK2_2 : Cv.At mem2 key k := Cv.At.frame (m := mem1) (by assumption) (fun x hx => by rw [hout2 x (by bv_decide) (by bv_decide)]; first | rfl | mem_away)
      have hK2_3 : Region mem2 out 32#64 := hown2 _ _ (by mem_region)
      have hOut : (∀ x : BitVec 64, (Abi.Contract.framed (Hashl.contract out input len key flags plat k bytes) 4016#64).stack + 8#64 ≤ x - fb → (∀ r ∈ (Abi.Contract.framed (Hashl.contract out input len key flags plat k bytes) 4016#64).modifies, r.2 ≤ x - r.1) → mem2 x = m0 x) := by
        intro x hx hmod
        have hx' := hx
        have hmod' := hmod
        simp only [Hashl.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, BitVec.reduceAdd] at hx' hmod'
        rw [hout2 x (by bv_decide) (by bv_decide)]
        refine Eq.trans ?_ (hOut x hx hmod); first | rfl | mem_away
      clear hout2 hown2
      refine runs_then (a := 6) (s1 := ?_) ?_ ?_
      case refine_2 => run_fn [c0]; rfl
      have_by hN3_0 := Hash.cv_of (m := mem2)
      try norm_addr at hN3_0
      split_ands hN3_0
      refine Abi.call_meets (c := Ladd.contract (fb + 264#64) key flags plat (fb + 3912#64) k (Hash.nodes k flags bytes counter) (Chunk.node k flags counter (Hash.chunk bytes counter))) (ra := 262373#64)
        (Abi.Meets.mono Code_hashl.has_ladd (Proof_ladd.ladd_meets (fb + 264#64) key flags plat (fb + 3912#64) k (Hash.nodes k flags bytes counter) (Chunk.node k flags counter (Hash.chunk bytes counter)))) rfl rfl ?_ ?_ ?_ ?_ ?_ ?_
      · dsimp only; mem_fact
      · dsimp only [Ladd.contract]; mem_subregion
      · dsimp only
        simp only [Ladd.contract, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, Abi.AllApart, Abi.Apart, BitVec.reduceAdd]
        try simp only [add_sub_lit, BitVec.add_assoc, BitVec.add_zero, BitVec.reduceAdd, BitVec.reduceSub]
        repeat' (with_reducible apply And.intro)
        all_goals bv_decide
      · simp only [Ladd.contract]
        repeat' (with_reducible apply And.intro)
        all_goals (first | assumption | bv_decide)
      · dsimp only
        simp only [Ladd.contract, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
        repeat' (with_reducible apply And.intro)
        all_goals (first | mem_auto | (apply_frame <;> mem_auto) | (apply_intro <;> first | mem_auto | (apply_frame <;> mem_auto)))
      · intro s3 hpc3 hsp3 hbx3 hbp3 h12_3 h13_3 h14_3 h15_3 hens3 hout3 hown3
        obtain ⟨rax_3, rcx_3, rdx_3, rbx_3, rsp_3, rbp_3, rsi_3, rdi_3, r8_3, r9_3, r12_3, r13_3, r14_3, r15_3, zf_3, cf_3, y3_0, y3_1, y3_2, y3_3, y3_4, y3_5, y3_6, y3_7, y3_8, y3_9, y3_10, y3_11, y3_12, y3_13, y3_14, y3_15, mem3, pc_3⟩ := s3
        dsimp only at hpc3 hsp3 hbx3 hbp3 h12_3 h13_3 h14_3 h15_3 hens3 hout3 hown3
        subst pc_3 rsp_3 rbx_3 rbp_3 r12_3 r13_3 r14_3 r15_3
        simp only [Ladd.contract, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true] at hens3
        split_ands hens3
        simp only [Ladd.contract, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, add_sub_lit, BitVec.add_assoc, BitVec.add_zero, BitVec.reduceAdd, BitVec.reduceSub] at hout3
        have hF3 : Region mem3 fb 4016#64 := hown3 fb 4016#64 (by mem_region)
        have hS3_0 : Quad mem3 (fb + 4016#64) ra := X86.Quad.frame (by mem_fact) (fun x hx => hout3 x (by bv_decide) (by bv_decide))
        have hS3_1 : Quad mem3 (fb + 4008#64) sv.rbx := X86.Quad.frame (by mem_fact) (fun x hx => hout3 x (by bv_decide) (by bv_decide))
        have hS3_2 : Quad mem3 (fb + 4000#64) sv.rbp := X86.Quad.frame (by mem_fact) (fun x hx => hout3 x (by bv_decide) (by bv_decide))
        have hS3_3 : Quad mem3 (fb + 3992#64) sv.r12 := X86.Quad.frame (by mem_fact) (fun x hx => hout3 x (by bv_decide) (by bv_decide))
        have hS3_4 : Quad mem3 (fb + 3984#64) sv.r13 := X86.Quad.frame (by mem_fact) (fun x hx => hout3 x (by bv_decide) (by bv_decide))
        have hS3_5 : Quad mem3 (fb + 3976#64) sv.r14 := X86.Quad.frame (by mem_fact) (fun x hx => hout3 x (by bv_decide) (by bv_decide))
        have hS3_6 : Quad mem3 (fb + 3968#64) sv.r15 := X86.Quad.frame (by mem_fact) (fun x hx => hout3 x (by bv_decide) (by bv_decide))
        have hS3_7 : Quad mem3 (fb + 3944#64) out := X86.Quad.frame (by mem_fact) (fun x hx => hout3 x (by bv_decide) (by bv_decide))
        have hS3_8 : Quad mem3 (fb + 3952#64) input := X86.Quad.frame (by mem_fact) (fun x hx => hout3 x (by bv_decide) (by bv_decide))
        have hS3_9 : Quad mem3 (fb + 3960#64) len := X86.Quad.frame (by mem_fact) (fun x hx => hout3 x (by bv_decide) (by bv_decide))
        have hK3_0 : Hash.In mem3 input len bytes p rem counter := Hash.In.frame (m := mem2) (by assumption) (fun x hx => by rw [hout3 x (by bv_decide) (by bv_decide)]; first | rfl | mem_away)
        have hK3_1 : Cv.At mem3 key k := Cv.At.frame (m := mem2) (by assumption) (fun x hx => by rw [hout3 x (by bv_decide) (by bv_decide)]; first | rfl | mem_away)
        have hK3_2 : Region mem3 out 32#64 := hown3 _ _ (by mem_region)
        have hOut : (∀ x : BitVec 64, (Abi.Contract.framed (Hashl.contract out input len key flags plat k bytes) 4016#64).stack + 8#64 ≤ x - fb → (∀ r ∈ (Abi.Contract.framed (Hashl.contract out input len key flags plat k bytes) 4016#64).modifies, r.2 ≤ x - r.1) → mem3 x = m0 x) := by
          intro x hx hmod
          have hx' := hx
          have hmod' := hmod
          simp only [Hashl.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, BitVec.reduceAdd] at hx' hmod'
          rw [hout3 x (by bv_decide) (by bv_decide)]
          refine Eq.trans ?_ (hOut x hx hmod); first | rfl | mem_away
        clear hout3 hown3
        refine runs_then (a := 10) (s1 := ?_) ?_ ?_
        case refine_2 => run_fn [c0]; rfl
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
          simp only [Hashl.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, BitVec.reduceAdd] at hx' hmod'
          first | rfl | mem_away
        · exact hAcc0
        · exact hReq0
        · skip
          refine ⟨?_, ?_, ?_, ?_⟩
          · apply Hash.In.step <;> mem_auto
          · apply Hash.Lv.step <;> mem_auto
          · first | mem_auto | (apply Cv.At.frame <;> mem_auto)
          · first | mem_auto | (apply Region.frame <;> mem_auto)
        · exact BitVec.lt_def.mp (by bv_decide)

theorem leave (fb out input len key flags plat ra : BitVec 64) (sv : Abi.Saved) (k : Blake3.CV) (bytes : List (BitVec 8)) (m0 : Mem)
    (s : State) (hI : Inv fb out input len key flags plat ra sv k bytes m0 s) (hc : ¬ 1024#64 < s.rbp) :
    ∃ n_ s', steps Code_hashl.prog n_ s = some s' ∧ Abi.Post (Abi.Contract.framed (Hashl.contract out input len key flags plat k bytes) 4016#64) fb ra sv m0 s' := by
  obtain ⟨rax, rcx, rdx, p, rsp, rem, rsi, rdi, r8, r9, counter, r13, r14, r15, zf, cf, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, mem, pc⟩ := s
  obtain ⟨hpc, hsp, hp0, hp1, hp2, hF, hRa, hS0, hS1, hS2, hS3, hS4, hS5, hPs0, hPs1, hPs2, hAp, hOut, hAcc, hReq, hI0, hI1, hI2, hI3⟩ := hI
  simp only at hpc hsp hp0 hp1 hp2 hF hRa hS0 hS1 hS2 hS3 hS4 hS5 hPs0 hPs1 hPs2 hOut hI0 hI1 hI2 hI3 hc
  subst pc rsp r13 r14 r15
  have hAp0 := hAp
  simp only [Hashl.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, Abi.AllApart, Abi.Apart, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, BitVec.reduceAdd] at hAp
  split_ands hAp
  have hAcc0 := hAcc
  try (simp only [Hashl.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true] at hAcc; split_ands hAcc)
  have hReq0 := hReq
  simp only [Hashl.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true] at hReq
  split_ands hReq
  forget_about m0 except hOut hReq0
  try (have hK0 := Hash.In.cells (m := mem) (by assumption); split_ands hK0)
  try (have hK1 := Hash.Lv.cells (m := mem) (by assumption); split_ands hK1)
  try (have hK2 := Cv.At.cells (m := mem) (by assumption); split_ands hK2)
  try (have hK3 := Region.cells (m := mem) (by assumption); split_ands hK3)
  have_by hO0 := Hash.last (m := mem)
  obtain ⟨_u, hO0⟩ := hO0
  try norm_addr at hO0
  split_ands hO0
  have_by hO1 := Cv.At.vectors (m := mem)
  obtain ⟨k0, k1, hO1⟩ := hO1
  try norm_addr at hO1
  split_ands hO1
  by_cases hs2 : counter = 0#64
  · have c0 : (1024#64).ult (rem) = false := by bv_decide
    have c1 : (counter - 0#64 == 0#64) = true := by bv_decide
    refine runs_then (a := 17) (s1 := ?_) ?_ ?_
    case refine_2 => run_fn [c0, c1]; rfl
    refine Abi.call_meets (c := ChunkNode.contract (fb + 3784#64) p rem counter flags plat k (Hash.chunk bytes counter)) (ra := 262465#64)
      (Abi.Meets.mono Code_hashl.has_chunk_node (Proof_chunk_node.chunk_node_meets (fb + 3784#64) p rem counter flags plat k (Hash.chunk bytes counter))) rfl rfl ?_ ?_ ?_ ?_ ?_ ?_
    · dsimp only; mem_fact
    · dsimp only [ChunkNode.contract]; mem_subregion
    · dsimp only
      simp only [ChunkNode.contract, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, Abi.AllApart, Abi.Apart, BitVec.reduceAdd]
      try simp only [add_sub_lit, BitVec.add_assoc, BitVec.add_zero, BitVec.reduceAdd, BitVec.reduceSub]
      repeat' (with_reducible apply And.intro)
      all_goals bv_decide
    · simp only [ChunkNode.contract]
      repeat' (with_reducible apply And.intro)
      all_goals (first | assumption | bv_decide)
    · dsimp only
      simp only [ChunkNode.contract, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
      repeat' (with_reducible apply And.intro)
      all_goals (first | mem_auto | (apply_frame <;> mem_auto) | (apply_intro <;> first | mem_auto | (apply_frame <;> mem_auto)))
    · intro s1 hpc1 hsp1 hbx1 hbp1 h12_1 h13_1 h14_1 h15_1 hens1 hout1 hown1
      obtain ⟨rax_1, rcx_1, rdx_1, rbx_1, rsp_1, rbp_1, rsi_1, rdi_1, r8_1, r9_1, r12_1, r13_1, r14_1, r15_1, zf_1, cf_1, y1_0, y1_1, y1_2, y1_3, y1_4, y1_5, y1_6, y1_7, y1_8, y1_9, y1_10, y1_11, y1_12, y1_13, y1_14, y1_15, mem1, pc_1⟩ := s1
      dsimp only at hpc1 hsp1 hbx1 hbp1 h12_1 h13_1 h14_1 h15_1 hens1 hout1 hown1
      subst pc_1 rsp_1 rbx_1 rbp_1 r12_1 r13_1 r14_1 r15_1
      simp only [ChunkNode.contract, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true] at hens1
      split_ands hens1
      simp only [ChunkNode.contract, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, add_sub_lit, BitVec.add_assoc, BitVec.add_zero, BitVec.reduceAdd, BitVec.reduceSub] at hout1
      have hF1 : Region mem1 fb 4016#64 := hown1 fb 4016#64 (by mem_region)
      have hS1_0 : Quad mem1 (fb + 4016#64) ra := X86.Quad.frame (by mem_fact) (fun x hx => hout1 x (by bv_decide) (by bv_decide))
      have hS1_1 : Quad mem1 (fb + 4008#64) sv.rbx := X86.Quad.frame (by mem_fact) (fun x hx => hout1 x (by bv_decide) (by bv_decide))
      have hS1_2 : Quad mem1 (fb + 4000#64) sv.rbp := X86.Quad.frame (by mem_fact) (fun x hx => hout1 x (by bv_decide) (by bv_decide))
      have hS1_3 : Quad mem1 (fb + 3992#64) sv.r12 := X86.Quad.frame (by mem_fact) (fun x hx => hout1 x (by bv_decide) (by bv_decide))
      have hS1_4 : Quad mem1 (fb + 3984#64) sv.r13 := X86.Quad.frame (by mem_fact) (fun x hx => hout1 x (by bv_decide) (by bv_decide))
      have hS1_5 : Quad mem1 (fb + 3976#64) sv.r14 := X86.Quad.frame (by mem_fact) (fun x hx => hout1 x (by bv_decide) (by bv_decide))
      have hS1_6 : Quad mem1 (fb + 3968#64) sv.r15 := X86.Quad.frame (by mem_fact) (fun x hx => hout1 x (by bv_decide) (by bv_decide))
      have hS1_7 : Quad mem1 (fb + 3944#64) out := X86.Quad.frame (by mem_fact) (fun x hx => hout1 x (by bv_decide) (by bv_decide))
      have hS1_8 : Quad mem1 (fb + 3952#64) input := X86.Quad.frame (by mem_fact) (fun x hx => hout1 x (by bv_decide) (by bv_decide))
      have hS1_9 : Quad mem1 (fb + 3960#64) len := X86.Quad.frame (by mem_fact) (fun x hx => hout1 x (by bv_decide) (by bv_decide))
      have hK1_0 : Hash.In mem1 input len bytes p rem counter := Hash.In.frame (m := mem) (by assumption) (fun x hx => by rw [hout1 x (by bv_decide) (by bv_decide)]; first | rfl | mem_away)
      have hK1_1 : Hash.Lv mem1 (fb + 264#64) k flags (Hash.nodes k flags bytes counter) := Hash.Lv.frame (m := mem) (by assumption) (fun x hx => by rw [hout1 x (by bv_decide) (by bv_decide)]; first | rfl | mem_away)
      have hK1_2 : Cv.At mem1 key k := Cv.At.frame (m := mem) (by assumption) (fun x hx => by rw [hout1 x (by bv_decide) (by bv_decide)]; first | rfl | mem_away)
      have hK1_3 : Region mem1 out 32#64 := hown1 _ _ (by mem_region)
      have hOut : (∀ x : BitVec 64, (Abi.Contract.framed (Hashl.contract out input len key flags plat k bytes) 4016#64).stack + 8#64 ≤ x - fb → (∀ r ∈ (Abi.Contract.framed (Hashl.contract out input len key flags plat k bytes) 4016#64).modifies, r.2 ≤ x - r.1) → mem1 x = m0 x) := by
        intro x hx hmod
        have hx' := hx
        have hmod' := hmod
        simp only [Hashl.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, BitVec.reduceAdd] at hx' hmod'
        rw [hout1 x (by bv_decide) (by bv_decide)]
        refine Eq.trans ?_ (hOut x hx hmod); first | rfl | mem_away
      clear hout1 hown1
      refine runs_then (a := 9) (s1 := ?_) ?_ ?_
      case refine_2 => run_fn [c0, c1]; rfl
      have_by hN2_0 := Hash.one (m := mem1)
      try norm_addr at hN2_0
      split_ands hN2_0
      refine Abi.call_meets (c := NodeOut.contract out (fb + 3784#64) 8#64 plat (Chunk.node k flags counter (Hash.chunk bytes counter))) (ra := 262511#64)
        (Abi.Meets.mono Code_hashl.has_node_out (Proof_node_out.node_out_meets out (fb + 3784#64) 8#64 plat (Chunk.node k flags counter (Hash.chunk bytes counter)))) rfl rfl ?_ ?_ ?_ ?_ ?_ ?_
      · dsimp only; mem_fact
      · dsimp only [NodeOut.contract]; mem_subregion
      · dsimp only
        simp only [NodeOut.contract, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, Abi.AllApart, Abi.Apart, BitVec.reduceAdd]
        try simp only [add_sub_lit, BitVec.add_assoc, BitVec.add_zero, BitVec.reduceAdd, BitVec.reduceSub]
        repeat' (with_reducible apply And.intro)
        all_goals bv_decide
      · simp only [NodeOut.contract]
        repeat' (with_reducible apply And.intro)
        all_goals (first | assumption | bv_decide)
      · dsimp only
        simp only [NodeOut.contract, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
        repeat' (with_reducible apply And.intro)
        all_goals (first | mem_auto | (apply_frame <;> mem_auto) | (apply_intro <;> first | mem_auto | (apply_frame <;> mem_auto)))
      · intro s2 hpc2 hsp2 hbx2 hbp2 h12_2 h13_2 h14_2 h15_2 hens2 hout2 hown2
        obtain ⟨rax_2, rcx_2, rdx_2, rbx_2, rsp_2, rbp_2, rsi_2, rdi_2, r8_2, r9_2, r12_2, r13_2, r14_2, r15_2, zf_2, cf_2, y2_0, y2_1, y2_2, y2_3, y2_4, y2_5, y2_6, y2_7, y2_8, y2_9, y2_10, y2_11, y2_12, y2_13, y2_14, y2_15, mem2, pc_2⟩ := s2
        dsimp only at hpc2 hsp2 hbx2 hbp2 h12_2 h13_2 h14_2 h15_2 hens2 hout2 hown2
        subst pc_2 rsp_2 rbx_2 rbp_2 r12_2 r13_2 r14_2 r15_2
        simp only [NodeOut.contract, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true] at hens2
        split_ands hens2
        simp only [NodeOut.contract, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, add_sub_lit, BitVec.add_assoc, BitVec.add_zero, BitVec.reduceAdd, BitVec.reduceSub] at hout2
        have hF2 : Region mem2 fb 4016#64 := hown2 fb 4016#64 (by mem_region)
        have hS2_0 : Quad mem2 (fb + 4016#64) ra := X86.Quad.frame (by mem_fact) (fun x hx => hout2 x (by bv_decide) (by bv_decide))
        have hS2_1 : Quad mem2 (fb + 4008#64) sv.rbx := X86.Quad.frame (by mem_fact) (fun x hx => hout2 x (by bv_decide) (by bv_decide))
        have hS2_2 : Quad mem2 (fb + 4000#64) sv.rbp := X86.Quad.frame (by mem_fact) (fun x hx => hout2 x (by bv_decide) (by bv_decide))
        have hS2_3 : Quad mem2 (fb + 3992#64) sv.r12 := X86.Quad.frame (by mem_fact) (fun x hx => hout2 x (by bv_decide) (by bv_decide))
        have hS2_4 : Quad mem2 (fb + 3984#64) sv.r13 := X86.Quad.frame (by mem_fact) (fun x hx => hout2 x (by bv_decide) (by bv_decide))
        have hS2_5 : Quad mem2 (fb + 3976#64) sv.r14 := X86.Quad.frame (by mem_fact) (fun x hx => hout2 x (by bv_decide) (by bv_decide))
        have hS2_6 : Quad mem2 (fb + 3968#64) sv.r15 := X86.Quad.frame (by mem_fact) (fun x hx => hout2 x (by bv_decide) (by bv_decide))
        have hS2_7 : Quad mem2 (fb + 3944#64) out := X86.Quad.frame (by mem_fact) (fun x hx => hout2 x (by bv_decide) (by bv_decide))
        have hS2_8 : Quad mem2 (fb + 3952#64) input := X86.Quad.frame (by mem_fact) (fun x hx => hout2 x (by bv_decide) (by bv_decide))
        have hS2_9 : Quad mem2 (fb + 3960#64) len := X86.Quad.frame (by mem_fact) (fun x hx => hout2 x (by bv_decide) (by bv_decide))
        have hOut : (∀ x : BitVec 64, (Abi.Contract.framed (Hashl.contract out input len key flags plat k bytes) 4016#64).stack + 8#64 ≤ x - fb → (∀ r ∈ (Abi.Contract.framed (Hashl.contract out input len key flags plat k bytes) 4016#64).modifies, r.2 ≤ x - r.1) → mem2 x = m0 x) := by
          intro x hx hmod
          have hx' := hx
          have hmod' := hmod
          simp only [Hashl.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, BitVec.reduceAdd] at hx' hmod'
          rw [hout2 x (by bv_decide) (by bv_decide)]
          refine Eq.trans ?_ (hOut x hx hmod); first | rfl | mem_away
        clear hout2 hown2
        refine runs_then (a := 9) (s1 := ?_) ?_ ?_
        case refine_2 => run_fn [c0, c1]; rfl
        refine runs_done ⟨rfl, by simp only [Hashl.contract, Abi.Contract.framed]; bv_decide, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
        all_goals try dsimp only
        · intro x hx hmod
          refine Eq.trans ?_ (hOut x hx hmod)
          have hx' := hx
          have hmod' := hmod
          simp only [Hashl.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, BitVec.reduceAdd] at hx' hmod'
          first | rfl | mem_away
        · simp only [Hashl.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
          apply Hashl.exit <;> mem_auto
  · have c0 : (1024#64).ult (rem) = false := by bv_decide
    have c1 : (counter - 0#64 == 0#64) = false := by bv_decide
    refine runs_then (a := 17) (s1 := ?_) ?_ ?_
    case refine_2 => run_fn [c0, c1]; rfl
    refine Abi.call_meets (c := ChunkNode.contract (fb + 3784#64) p rem counter flags plat k (Hash.chunk bytes counter)) (ra := 262465#64)
      (Abi.Meets.mono Code_hashl.has_chunk_node (Proof_chunk_node.chunk_node_meets (fb + 3784#64) p rem counter flags plat k (Hash.chunk bytes counter))) rfl rfl ?_ ?_ ?_ ?_ ?_ ?_
    · dsimp only; mem_fact
    · dsimp only [ChunkNode.contract]; mem_subregion
    · dsimp only
      simp only [ChunkNode.contract, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, Abi.AllApart, Abi.Apart, BitVec.reduceAdd]
      try simp only [add_sub_lit, BitVec.add_assoc, BitVec.add_zero, BitVec.reduceAdd, BitVec.reduceSub]
      repeat' (with_reducible apply And.intro)
      all_goals bv_decide
    · simp only [ChunkNode.contract]
      repeat' (with_reducible apply And.intro)
      all_goals (first | assumption | bv_decide)
    · dsimp only
      simp only [ChunkNode.contract, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
      repeat' (with_reducible apply And.intro)
      all_goals (first | mem_auto | (apply_frame <;> mem_auto) | (apply_intro <;> first | mem_auto | (apply_frame <;> mem_auto)))
    · intro s1 hpc1 hsp1 hbx1 hbp1 h12_1 h13_1 h14_1 h15_1 hens1 hout1 hown1
      obtain ⟨rax_1, rcx_1, rdx_1, rbx_1, rsp_1, rbp_1, rsi_1, rdi_1, r8_1, r9_1, r12_1, r13_1, r14_1, r15_1, zf_1, cf_1, y1_0, y1_1, y1_2, y1_3, y1_4, y1_5, y1_6, y1_7, y1_8, y1_9, y1_10, y1_11, y1_12, y1_13, y1_14, y1_15, mem1, pc_1⟩ := s1
      dsimp only at hpc1 hsp1 hbx1 hbp1 h12_1 h13_1 h14_1 h15_1 hens1 hout1 hown1
      subst pc_1 rsp_1 rbx_1 rbp_1 r12_1 r13_1 r14_1 r15_1
      simp only [ChunkNode.contract, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true] at hens1
      split_ands hens1
      simp only [ChunkNode.contract, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, add_sub_lit, BitVec.add_assoc, BitVec.add_zero, BitVec.reduceAdd, BitVec.reduceSub] at hout1
      have hF1 : Region mem1 fb 4016#64 := hown1 fb 4016#64 (by mem_region)
      have hS1_0 : Quad mem1 (fb + 4016#64) ra := X86.Quad.frame (by mem_fact) (fun x hx => hout1 x (by bv_decide) (by bv_decide))
      have hS1_1 : Quad mem1 (fb + 4008#64) sv.rbx := X86.Quad.frame (by mem_fact) (fun x hx => hout1 x (by bv_decide) (by bv_decide))
      have hS1_2 : Quad mem1 (fb + 4000#64) sv.rbp := X86.Quad.frame (by mem_fact) (fun x hx => hout1 x (by bv_decide) (by bv_decide))
      have hS1_3 : Quad mem1 (fb + 3992#64) sv.r12 := X86.Quad.frame (by mem_fact) (fun x hx => hout1 x (by bv_decide) (by bv_decide))
      have hS1_4 : Quad mem1 (fb + 3984#64) sv.r13 := X86.Quad.frame (by mem_fact) (fun x hx => hout1 x (by bv_decide) (by bv_decide))
      have hS1_5 : Quad mem1 (fb + 3976#64) sv.r14 := X86.Quad.frame (by mem_fact) (fun x hx => hout1 x (by bv_decide) (by bv_decide))
      have hS1_6 : Quad mem1 (fb + 3968#64) sv.r15 := X86.Quad.frame (by mem_fact) (fun x hx => hout1 x (by bv_decide) (by bv_decide))
      have hS1_7 : Quad mem1 (fb + 3944#64) out := X86.Quad.frame (by mem_fact) (fun x hx => hout1 x (by bv_decide) (by bv_decide))
      have hS1_8 : Quad mem1 (fb + 3952#64) input := X86.Quad.frame (by mem_fact) (fun x hx => hout1 x (by bv_decide) (by bv_decide))
      have hS1_9 : Quad mem1 (fb + 3960#64) len := X86.Quad.frame (by mem_fact) (fun x hx => hout1 x (by bv_decide) (by bv_decide))
      have hK1_0 : Hash.In mem1 input len bytes p rem counter := Hash.In.frame (m := mem) (by assumption) (fun x hx => by rw [hout1 x (by bv_decide) (by bv_decide)]; first | rfl | mem_away)
      have hK1_1 : Hash.Lv mem1 (fb + 264#64) k flags (Hash.nodes k flags bytes counter) := Hash.Lv.frame (m := mem) (by assumption) (fun x hx => by rw [hout1 x (by bv_decide) (by bv_decide)]; first | rfl | mem_away)
      have hK1_2 : Cv.At mem1 key k := Cv.At.frame (m := mem) (by assumption) (fun x hx => by rw [hout1 x (by bv_decide) (by bv_decide)]; first | rfl | mem_away)
      have hK1_3 : Region mem1 out 32#64 := hown1 _ _ (by mem_region)
      have hOut : (∀ x : BitVec 64, (Abi.Contract.framed (Hashl.contract out input len key flags plat k bytes) 4016#64).stack + 8#64 ≤ x - fb → (∀ r ∈ (Abi.Contract.framed (Hashl.contract out input len key flags plat k bytes) 4016#64).modifies, r.2 ≤ x - r.1) → mem1 x = m0 x) := by
        intro x hx hmod
        have hx' := hx
        have hmod' := hmod
        simp only [Hashl.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, BitVec.reduceAdd] at hx' hmod'
        rw [hout1 x (by bv_decide) (by bv_decide)]
        refine Eq.trans ?_ (hOut x hx hmod); first | rfl | mem_away
      clear hout1 hown1
      refine runs_then (a := 9) (s1 := ?_) ?_ ?_
      case refine_2 => run_fn [c0, c1]; rfl
      refine Abi.call_meets (c := NodeOut.contract (fb + 3912#64) (fb + 3784#64) 0#64 plat (Chunk.node k flags counter (Hash.chunk bytes counter))) (ra := 262544#64)
        (Abi.Meets.mono Code_hashl.has_node_out (Proof_node_out.node_out_meets (fb + 3912#64) (fb + 3784#64) 0#64 plat (Chunk.node k flags counter (Hash.chunk bytes counter)))) rfl rfl ?_ ?_ ?_ ?_ ?_ ?_
      · dsimp only; mem_fact
      · dsimp only [NodeOut.contract]; mem_subregion
      · dsimp only
        simp only [NodeOut.contract, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, Abi.AllApart, Abi.Apart, BitVec.reduceAdd]
        try simp only [add_sub_lit, BitVec.add_assoc, BitVec.add_zero, BitVec.reduceAdd, BitVec.reduceSub]
        repeat' (with_reducible apply And.intro)
        all_goals bv_decide
      · simp only [NodeOut.contract]
        repeat' (with_reducible apply And.intro)
        all_goals (first | assumption | bv_decide)
      · dsimp only
        simp only [NodeOut.contract, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
        repeat' (with_reducible apply And.intro)
        all_goals (first | mem_auto | (apply_frame <;> mem_auto) | (apply_intro <;> first | mem_auto | (apply_frame <;> mem_auto)))
      · intro s2 hpc2 hsp2 hbx2 hbp2 h12_2 h13_2 h14_2 h15_2 hens2 hout2 hown2
        obtain ⟨rax_2, rcx_2, rdx_2, rbx_2, rsp_2, rbp_2, rsi_2, rdi_2, r8_2, r9_2, r12_2, r13_2, r14_2, r15_2, zf_2, cf_2, y2_0, y2_1, y2_2, y2_3, y2_4, y2_5, y2_6, y2_7, y2_8, y2_9, y2_10, y2_11, y2_12, y2_13, y2_14, y2_15, mem2, pc_2⟩ := s2
        dsimp only at hpc2 hsp2 hbx2 hbp2 h12_2 h13_2 h14_2 h15_2 hens2 hout2 hown2
        subst pc_2 rsp_2 rbx_2 rbp_2 r12_2 r13_2 r14_2 r15_2
        simp only [NodeOut.contract, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true] at hens2
        split_ands hens2
        simp only [NodeOut.contract, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, add_sub_lit, BitVec.add_assoc, BitVec.add_zero, BitVec.reduceAdd, BitVec.reduceSub] at hout2
        have hF2 : Region mem2 fb 4016#64 := hown2 fb 4016#64 (by mem_region)
        have hS2_0 : Quad mem2 (fb + 4016#64) ra := X86.Quad.frame (by mem_fact) (fun x hx => hout2 x (by bv_decide) (by bv_decide))
        have hS2_1 : Quad mem2 (fb + 4008#64) sv.rbx := X86.Quad.frame (by mem_fact) (fun x hx => hout2 x (by bv_decide) (by bv_decide))
        have hS2_2 : Quad mem2 (fb + 4000#64) sv.rbp := X86.Quad.frame (by mem_fact) (fun x hx => hout2 x (by bv_decide) (by bv_decide))
        have hS2_3 : Quad mem2 (fb + 3992#64) sv.r12 := X86.Quad.frame (by mem_fact) (fun x hx => hout2 x (by bv_decide) (by bv_decide))
        have hS2_4 : Quad mem2 (fb + 3984#64) sv.r13 := X86.Quad.frame (by mem_fact) (fun x hx => hout2 x (by bv_decide) (by bv_decide))
        have hS2_5 : Quad mem2 (fb + 3976#64) sv.r14 := X86.Quad.frame (by mem_fact) (fun x hx => hout2 x (by bv_decide) (by bv_decide))
        have hS2_6 : Quad mem2 (fb + 3968#64) sv.r15 := X86.Quad.frame (by mem_fact) (fun x hx => hout2 x (by bv_decide) (by bv_decide))
        have hS2_7 : Quad mem2 (fb + 3944#64) out := X86.Quad.frame (by mem_fact) (fun x hx => hout2 x (by bv_decide) (by bv_decide))
        have hS2_8 : Quad mem2 (fb + 3952#64) input := X86.Quad.frame (by mem_fact) (fun x hx => hout2 x (by bv_decide) (by bv_decide))
        have hS2_9 : Quad mem2 (fb + 3960#64) len := X86.Quad.frame (by mem_fact) (fun x hx => hout2 x (by bv_decide) (by bv_decide))
        have hK2_0 : Hash.In mem2 input len bytes p rem counter := Hash.In.frame (m := mem1) (by assumption) (fun x hx => by rw [hout2 x (by bv_decide) (by bv_decide)]; first | rfl | mem_away)
        have hK2_1 : Hash.Lv mem2 (fb + 264#64) k flags (Hash.nodes k flags bytes counter) := Hash.Lv.frame (m := mem1) (by assumption) (fun x hx => by rw [hout2 x (by bv_decide) (by bv_decide)]; first | rfl | mem_away)
        have hK2_2 : Cv.At mem2 key k := Cv.At.frame (m := mem1) (by assumption) (fun x hx => by rw [hout2 x (by bv_decide) (by bv_decide)]; first | rfl | mem_away)
        have hK2_3 : Region mem2 out 32#64 := hown2 _ _ (by mem_region)
        have hOut : (∀ x : BitVec 64, (Abi.Contract.framed (Hashl.contract out input len key flags plat k bytes) 4016#64).stack + 8#64 ≤ x - fb → (∀ r ∈ (Abi.Contract.framed (Hashl.contract out input len key flags plat k bytes) 4016#64).modifies, r.2 ≤ x - r.1) → mem2 x = m0 x) := by
          intro x hx hmod
          have hx' := hx
          have hmod' := hmod
          simp only [Hashl.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, BitVec.reduceAdd] at hx' hmod'
          rw [hout2 x (by bv_decide) (by bv_decide)]
          refine Eq.trans ?_ (hOut x hx hmod); first | rfl | mem_away
        clear hout2 hown2
        refine runs_then (a := 6) (s1 := ?_) ?_ ?_
        case refine_2 => run_fn [c0, c1]; rfl
        have_by hN3_0 := Hash.cv_of (m := mem2)
        try norm_addr at hN3_0
        split_ands hN3_0
        have_by hN3_1 := Hash.room (m := mem2)
        try norm_addr at hN3_1
        split_ands hN3_1
        refine Abi.call_meets (c := Ladd.contract (fb + 264#64) key flags plat (fb + 3912#64) k (Hash.nodes k flags bytes counter) (Chunk.node k flags counter (Hash.chunk bytes counter))) (ra := 262570#64)
          (Abi.Meets.mono Code_hashl.has_ladd (Proof_ladd.ladd_meets (fb + 264#64) key flags plat (fb + 3912#64) k (Hash.nodes k flags bytes counter) (Chunk.node k flags counter (Hash.chunk bytes counter)))) rfl rfl ?_ ?_ ?_ ?_ ?_ ?_
        · dsimp only; mem_fact
        · dsimp only [Ladd.contract]; mem_subregion
        · dsimp only
          simp only [Ladd.contract, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, Abi.AllApart, Abi.Apart, BitVec.reduceAdd]
          try simp only [add_sub_lit, BitVec.add_assoc, BitVec.add_zero, BitVec.reduceAdd, BitVec.reduceSub]
          repeat' (with_reducible apply And.intro)
          all_goals bv_decide
        · simp only [Ladd.contract]
          repeat' (with_reducible apply And.intro)
          all_goals (first | assumption | bv_decide)
        · dsimp only
          simp only [Ladd.contract, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
          repeat' (with_reducible apply And.intro)
          all_goals (first | mem_auto | (apply_frame <;> mem_auto) | (apply_intro <;> first | mem_auto | (apply_frame <;> mem_auto)))
        · intro s3 hpc3 hsp3 hbx3 hbp3 h12_3 h13_3 h14_3 h15_3 hens3 hout3 hown3
          obtain ⟨rax_3, rcx_3, rdx_3, rbx_3, rsp_3, rbp_3, rsi_3, rdi_3, r8_3, r9_3, r12_3, r13_3, r14_3, r15_3, zf_3, cf_3, y3_0, y3_1, y3_2, y3_3, y3_4, y3_5, y3_6, y3_7, y3_8, y3_9, y3_10, y3_11, y3_12, y3_13, y3_14, y3_15, mem3, pc_3⟩ := s3
          dsimp only at hpc3 hsp3 hbx3 hbp3 h12_3 h13_3 h14_3 h15_3 hens3 hout3 hown3
          subst pc_3 rsp_3 rbx_3 rbp_3 r12_3 r13_3 r14_3 r15_3
          simp only [Ladd.contract, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true] at hens3
          split_ands hens3
          simp only [Ladd.contract, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, add_sub_lit, BitVec.add_assoc, BitVec.add_zero, BitVec.reduceAdd, BitVec.reduceSub] at hout3
          have hF3 : Region mem3 fb 4016#64 := hown3 fb 4016#64 (by mem_region)
          have hS3_0 : Quad mem3 (fb + 4016#64) ra := X86.Quad.frame (by mem_fact) (fun x hx => hout3 x (by bv_decide) (by bv_decide))
          have hS3_1 : Quad mem3 (fb + 4008#64) sv.rbx := X86.Quad.frame (by mem_fact) (fun x hx => hout3 x (by bv_decide) (by bv_decide))
          have hS3_2 : Quad mem3 (fb + 4000#64) sv.rbp := X86.Quad.frame (by mem_fact) (fun x hx => hout3 x (by bv_decide) (by bv_decide))
          have hS3_3 : Quad mem3 (fb + 3992#64) sv.r12 := X86.Quad.frame (by mem_fact) (fun x hx => hout3 x (by bv_decide) (by bv_decide))
          have hS3_4 : Quad mem3 (fb + 3984#64) sv.r13 := X86.Quad.frame (by mem_fact) (fun x hx => hout3 x (by bv_decide) (by bv_decide))
          have hS3_5 : Quad mem3 (fb + 3976#64) sv.r14 := X86.Quad.frame (by mem_fact) (fun x hx => hout3 x (by bv_decide) (by bv_decide))
          have hS3_6 : Quad mem3 (fb + 3968#64) sv.r15 := X86.Quad.frame (by mem_fact) (fun x hx => hout3 x (by bv_decide) (by bv_decide))
          have hS3_7 : Quad mem3 (fb + 3944#64) out := X86.Quad.frame (by mem_fact) (fun x hx => hout3 x (by bv_decide) (by bv_decide))
          have hS3_8 : Quad mem3 (fb + 3952#64) input := X86.Quad.frame (by mem_fact) (fun x hx => hout3 x (by bv_decide) (by bv_decide))
          have hS3_9 : Quad mem3 (fb + 3960#64) len := X86.Quad.frame (by mem_fact) (fun x hx => hout3 x (by bv_decide) (by bv_decide))
          have hK3_0 : Hash.In mem3 input len bytes p rem counter := Hash.In.frame (m := mem2) (by assumption) (fun x hx => by rw [hout3 x (by bv_decide) (by bv_decide)]; first | rfl | mem_away)
          have hK3_1 : Cv.At mem3 key k := Cv.At.frame (m := mem2) (by assumption) (fun x hx => by rw [hout3 x (by bv_decide) (by bv_decide)]; first | rfl | mem_away)
          have hK3_2 : Region mem3 out 32#64 := hown3 _ _ (by mem_region)
          have hOut : (∀ x : BitVec 64, (Abi.Contract.framed (Hashl.contract out input len key flags plat k bytes) 4016#64).stack + 8#64 ≤ x - fb → (∀ r ∈ (Abi.Contract.framed (Hashl.contract out input len key flags plat k bytes) 4016#64).modifies, r.2 ≤ x - r.1) → mem3 x = m0 x) := by
            intro x hx hmod
            have hx' := hx
            have hmod' := hmod
            simp only [Hashl.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, BitVec.reduceAdd] at hx' hmod'
            rw [hout3 x (by bv_decide) (by bv_decide)]
            refine Eq.trans ?_ (hOut x hx hmod); first | rfl | mem_away
          clear hout3 hown3
          refine runs_then (a := 6) (s1 := ?_) ?_ ?_
          case refine_2 => run_fn [c0, c1]; rfl
          have_by hN4_0 := Hash.many (m := mem3)
          try norm_addr at hN4_0
          split_ands hN4_0
          refine Abi.call_meets (c := Lroot.contract out (fb + 264#64) key flags plat k ((Hash.nodes k flags bytes counter).push (Chunk.node k flags counter (Hash.chunk bytes counter)))) (ra := 262596#64)
            (Abi.Meets.mono Code_hashl.has_lroot (Proof_lroot.lroot_meets out (fb + 264#64) key flags plat k ((Hash.nodes k flags bytes counter).push (Chunk.node k flags counter (Hash.chunk bytes counter))))) rfl rfl ?_ ?_ ?_ ?_ ?_ ?_
          · dsimp only; mem_fact
          · dsimp only [Lroot.contract]; mem_subregion
          · dsimp only
            simp only [Lroot.contract, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, Abi.AllApart, Abi.Apart, BitVec.reduceAdd]
            try simp only [add_sub_lit, BitVec.add_assoc, BitVec.add_zero, BitVec.reduceAdd, BitVec.reduceSub]
            repeat' (with_reducible apply And.intro)
            all_goals bv_decide
          · simp only [Lroot.contract]
            repeat' (with_reducible apply And.intro)
            all_goals (first | assumption | bv_decide)
          · dsimp only
            simp only [Lroot.contract, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
            repeat' (with_reducible apply And.intro)
            all_goals (first | mem_auto | (apply_frame <;> mem_auto) | (apply_intro <;> first | mem_auto | (apply_frame <;> mem_auto)))
          · intro s4 hpc4 hsp4 hbx4 hbp4 h12_4 h13_4 h14_4 h15_4 hens4 hout4 hown4
            obtain ⟨rax_4, rcx_4, rdx_4, rbx_4, rsp_4, rbp_4, rsi_4, rdi_4, r8_4, r9_4, r12_4, r13_4, r14_4, r15_4, zf_4, cf_4, y4_0, y4_1, y4_2, y4_3, y4_4, y4_5, y4_6, y4_7, y4_8, y4_9, y4_10, y4_11, y4_12, y4_13, y4_14, y4_15, mem4, pc_4⟩ := s4
            dsimp only at hpc4 hsp4 hbx4 hbp4 h12_4 h13_4 h14_4 h15_4 hens4 hout4 hown4
            subst pc_4 rsp_4 rbx_4 rbp_4 r12_4 r13_4 r14_4 r15_4
            simp only [Lroot.contract, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true] at hens4
            split_ands hens4
            simp only [Lroot.contract, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, add_sub_lit, BitVec.add_assoc, BitVec.add_zero, BitVec.reduceAdd, BitVec.reduceSub] at hout4
            have hF4 : Region mem4 fb 4016#64 := hown4 fb 4016#64 (by mem_region)
            have hS4_0 : Quad mem4 (fb + 4016#64) ra := X86.Quad.frame (by mem_fact) (fun x hx => hout4 x (by bv_decide) (by bv_decide))
            have hS4_1 : Quad mem4 (fb + 4008#64) sv.rbx := X86.Quad.frame (by mem_fact) (fun x hx => hout4 x (by bv_decide) (by bv_decide))
            have hS4_2 : Quad mem4 (fb + 4000#64) sv.rbp := X86.Quad.frame (by mem_fact) (fun x hx => hout4 x (by bv_decide) (by bv_decide))
            have hS4_3 : Quad mem4 (fb + 3992#64) sv.r12 := X86.Quad.frame (by mem_fact) (fun x hx => hout4 x (by bv_decide) (by bv_decide))
            have hS4_4 : Quad mem4 (fb + 3984#64) sv.r13 := X86.Quad.frame (by mem_fact) (fun x hx => hout4 x (by bv_decide) (by bv_decide))
            have hS4_5 : Quad mem4 (fb + 3976#64) sv.r14 := X86.Quad.frame (by mem_fact) (fun x hx => hout4 x (by bv_decide) (by bv_decide))
            have hS4_6 : Quad mem4 (fb + 3968#64) sv.r15 := X86.Quad.frame (by mem_fact) (fun x hx => hout4 x (by bv_decide) (by bv_decide))
            have hS4_7 : Quad mem4 (fb + 3944#64) out := X86.Quad.frame (by mem_fact) (fun x hx => hout4 x (by bv_decide) (by bv_decide))
            have hS4_8 : Quad mem4 (fb + 3952#64) input := X86.Quad.frame (by mem_fact) (fun x hx => hout4 x (by bv_decide) (by bv_decide))
            have hS4_9 : Quad mem4 (fb + 3960#64) len := X86.Quad.frame (by mem_fact) (fun x hx => hout4 x (by bv_decide) (by bv_decide))
            have hOut : (∀ x : BitVec 64, (Abi.Contract.framed (Hashl.contract out input len key flags plat k bytes) 4016#64).stack + 8#64 ≤ x - fb → (∀ r ∈ (Abi.Contract.framed (Hashl.contract out input len key flags plat k bytes) 4016#64).modifies, r.2 ≤ x - r.1) → mem4 x = m0 x) := by
              intro x hx hmod
              have hx' := hx
              have hmod' := hmod
              simp only [Hashl.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, BitVec.reduceAdd] at hx' hmod'
              rw [hout4 x (by bv_decide) (by bv_decide)]
              refine Eq.trans ?_ (hOut x hx hmod); first | rfl | mem_away
            clear hout4 hown4
            refine runs_then (a := 8) (s1 := ?_) ?_ ?_
            case refine_2 => run_fn [c0, c1]; rfl
            refine runs_done ⟨rfl, by simp only [Hashl.contract, Abi.Contract.framed]; bv_decide, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
            all_goals try dsimp only
            · intro x hx hmod
              refine Eq.trans ?_ (hOut x hx hmod)
              have hx' := hx
              have hmod' := hmod
              simp only [Hashl.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, BitVec.reduceAdd] at hx' hmod'
              first | rfl | mem_away
            · simp only [Hashl.contract, Abi.Contract.framed, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
              apply Hashl.exit <;> mem_auto

/-- **`hashl`, as assembled, meets its contract, whatever its arguments.** -/
theorem hashl_meets : ∀ (out input len key flags plat : BitVec 64) (k : Blake3.CV) (bytes : List (BitVec 8)),
    Abi.Meets Code_hashl.prog 0x40000 (Hashl.contract out input len key flags plat k bytes) := by
  intro out input len key flags plat k bytes
  refine Abi.meets_of_triple 4016#64 (by dsimp only [Hashl.contract]; decide) (by dsimp only [Hashl.contract]; decide) (fun fb ra sv m0 => ?_)
  refine Hoare.seq (Q := Inv fb out input len key flags plat ra sv k bytes m0) ?_ ?_
  · intro s hP
    exact enter fb out input len key flags plat ra sv k bytes m0 s hP
  · refine Hoare.loop (fun s => s.rbp.toNat) (fun s hI => ?_)
    by_cases hc : 1024#64 < s.rbp
    · obtain ⟨n_, s', h, hi, hm⟩ := turn fb out input len key flags plat ra sv k bytes m0 s hI hc
      exact ⟨n_, s', h, Or.inl ⟨hi, hm⟩⟩
    · obtain ⟨n_, s', h, hq⟩ := leave fb out input len key flags plat ra sv k bytes m0 s hI hc
      exact ⟨n_, s', h, Or.inr hq⟩

#print axioms hashl_meets

end Proof_hashl
