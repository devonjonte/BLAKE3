import Cells
import Kernels
import StackSpec
import Code_merge
open X86 Cells

namespace MergeOde

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

def Inv (fb st key flags plat target ra b0 bp0 s12 s13 s14 s15 : BitVec 64) (k0 k1 : V) (es0 : Stack.Cvs) (m0 : Mem) (s : State) : Prop :=
  s.pc = 0x60032 ∧ s.rsp = fb + 8#64 ∧ s.rbx = st ∧ s.rbp = key ∧ s.r12 = flags ∧ s.r13 = plat ∧ s.r14 = target ∧
  Region s.mem fb 176#64 ∧ Quad s.mem (fb + 176#64) ra ∧
  Quad s.mem (fb + 168#64) b0 ∧ Quad s.mem (fb + 160#64) bp0 ∧ Quad s.mem (fb + 152#64) s12 ∧ Quad s.mem (fb + 144#64) s13 ∧
  Quad s.mem (fb + 136#64) s14 ∧ Quad s.mem (fb + 128#64) s15 ∧
  (∀ x : BitVec 64, 184#64 ≤ x - fb → 1792#64 ≤ x - st → s.mem x = m0 x) ∧
  ∃ (pf : BitVec 64) (es : Stack.Cvs), Quad s.mem (fb + 104#64) pf ∧
    Stack.holds s.mem st s.r15 es ∧
    Stack.merged k0 k1 (pf.setWidth 8) target es = Stack.merged k0 k1 (pf.setWidth 8) target es0 ∧
    pf = flags ||| 4#64 ∧
    Vec s.mem key k0 ∧ Vec s.mem (key + 16#64) k1

theorem turn (fb st key flags plat target ra b0 bp0 s12 s13 s14 s15 : BitVec 64) (k0 k1 : V) (es0 : Stack.Cvs) (m0 : Mem)
    (hT1 : 1#64 ≤ target) (hfl : flags < 256#64)
    (aFS : 184#64 ≤ st - fb ∧ 1792#64 ≤ fb - st) (aFK : 184#64 ≤ key - fb ∧ 32#64 ≤ fb - key) (aSK : 1792#64 ≤ key - st ∧ 32#64 ≤ st - key)
    (s : State) (hI : Inv fb st key flags plat target ra b0 bp0 s12 s13 s14 s15 k0 k1 es0 m0 s) (hc : target < s.r15) :
    ∃ k s', steps Code_merge.prog k s = some s' ∧ (Inv fb st key flags plat target ra b0 bp0 s12 s13 s14 s15 k0 k1 es0 m0 s' ∧ s'.r15.toNat < s.r15.toNat) := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r12, r13, r14, len, zf, cf, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, mem, pc⟩ := s
  obtain ⟨hpc, hsp, hbx, hbp, h12, h13, h14, hF, hRa, hS0, hS1, hS2, hS3, hS4, hS5, hOut, pf, es, hPf, hH, hSpec, hpf, hK0, hK1⟩ := hI
  simp only at hpc hsp hbx hbp h12 h13 h14 hF hRa hS0 hS1 hS2 hS3 hS4 hS5 hOut hPf hH hSpec hK0 hK1 hc
  subst pc rsp rbx rbp r12 r13 r14 pf
  have hHc := Stack.cells hH
  split_ands hHc
  have h2 : 2#64 ≤ len := by bv_decide
  obtain ⟨r0, r1, l0, l1, rest, hes, hO⟩ := Stack.open2 hH h2
  subst hes
  norm_addr at hO
  split_ands hO
  have c1 : target.ult len = true := by bv_decide
  have c2 : len.ult 2#64 = false := by bv_decide
  by_cases hp : plat = 5#64
  · subst hp
    refine ⟨45 + (362 + (14 + 0)), ?_⟩
    refine run_then (s1 := ?_) ?_ ?_
    case refine_2 => run_fn [c1, c2]; rfl
    refine Kernels.call_avx_then Code_merge.has_kernels
      (by mem_fact) (by mem_fact) (by mem_fact) (by mem_fact) (by mem_fact) (by mem_fact) (by mem_fact) (by bv_decide) ?_
    intro rax' rcx' rdx' rsi' rdi' r8' r9' zf' cf' y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15
    refine run_then (s1 := ?_) ?_ ?_
    case refine_2 => run_fn []; rfl
    refine ⟨_, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    all_goals dsimp only
    · mem_region
    · mem_fact
    · mem_fact
    · mem_fact
    · mem_fact
    · mem_fact
    · mem_fact
    · mem_fact
    · intro x hx1 hx2
      refine Eq.trans ?_ (hOut x hx1 hx2)
      mem_away
    · apply Exists.intro; apply Exists.intro
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · mem_fact
      · apply Stack.close_merge hH h2
        · mem_fact
        · mem_fact
        · mem_fact
        · mem_region
        · intro x hx1 hx2 hx3
          mem_away
      · exact (Stack.merged_step k0 k1 _ target len r0 r1 l0 l1 rest hH.1 hc).symm.trans hSpec
      · rfl
      · mem_fact
      · mem_fact
    · exact BitVec.lt_def.mp (by bv_decide)
  · have c3 : (plat - 5#64 == 0#64) = false := by bv_decide
    have f32 : BitVec.setWidth 32 (flags ||| 4#64) = BitVec.setWidth 32 (BitVec.setWidth 8 (flags ||| 4#64)) := by bv_decide
    refine ⟨45 + (467 + (13 + 0)), ?_⟩
    refine run_then (s1 := ?_) ?_ ?_
    case refine_2 => run_fn [c1, c2, c3]; rfl
    refine Kernels.call_sse_then Code_merge.has_kernels
      (by mem_fact) (by mem_fact) (by mem_fact) (by mem_fact) (by mem_fact) (by mem_fact) (by bv_decide) (by mem_fact) (by bv_decide) ?_
    intro rax' rcx' rdx' rsi' rdi' r8' r9' zf' cf' y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15
    refine run_then (s1 := ?_) ?_ ?_
    case refine_2 => run_fn [f32]; rfl
    refine ⟨_, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    all_goals dsimp only
    · mem_region
    · mem_fact
    · mem_fact
    · mem_fact
    · mem_fact
    · mem_fact
    · mem_fact
    · mem_fact
    · intro x hx1 hx2
      refine Eq.trans ?_ (hOut x hx1 hx2)
      mem_away
    · apply Exists.intro; apply Exists.intro
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · mem_fact
      · apply Stack.close_merge hH h2
        · mem_fact
        · mem_fact
        · mem_fact
        · mem_region
        · intro x hx1 hx2 hx3
          mem_away
      · exact (Stack.merged_step k0 k1 _ target len r0 r1 l0 l1 rest hH.1 hc).symm.trans hSpec
      · rfl
      · mem_fact
      · mem_fact
    · exact BitVec.lt_def.mp (by bv_decide)

def Pre (fb st key flags plat target ra b0 bp0 s12 s13 s14 s15 len0 : BitVec 64) (k0 k1 : V) (es0 : Stack.Cvs) (m0 : Mem) (s : State) : Prop :=
  s.pc = 0x60000 ∧ s.rsp = fb + 176#64 ∧ s.rdi = st ∧ s.rsi = key ∧ s.rdx = flags ∧ s.rcx = plat ∧ s.r8 = target ∧
  s.rbx = b0 ∧ s.rbp = bp0 ∧ s.r12 = s12 ∧ s.r13 = s13 ∧ s.r14 = s14 ∧ s.r15 = s15 ∧ s.mem = m0 ∧
  Region m0 fb 176#64 ∧ Quad m0 (fb + 176#64) ra ∧
  Stack.holds m0 st len0 es0 ∧ Vec m0 key k0 ∧ Vec m0 (key + 16#64) k1

def Post (fb st flags target ra b0 bp0 s12 s13 s14 s15 : BitVec 64) (k0 k1 : V) (es0 : Stack.Cvs) (m0 : Mem) (s : State) : Prop :=
  s.pc = ra.toNat ∧ s.rsp = fb + 184#64 ∧ s.rbx = b0 ∧ s.rbp = bp0 ∧ s.r12 = s12 ∧ s.r13 = s13 ∧ s.r14 = s14 ∧ s.r15 = s15 ∧
  (∀ x : BitVec 64, 184#64 ≤ x - fb → 1792#64 ≤ x - st → s.mem x = m0 x) ∧
  Stack.holds s.mem st s.rax (Stack.merged k0 k1 ((flags ||| 4#64).setWidth 8) target es0)

theorem enter (fb st key flags plat target ra b0 bp0 s12 s13 s14 s15 len0 : BitVec 64) (k0 k1 : V) (es0 : Stack.Cvs) (m0 : Mem)
    (aFS : 184#64 ≤ st - fb ∧ 1792#64 ≤ fb - st) (aFK : 184#64 ≤ key - fb ∧ 32#64 ≤ fb - key) (aSK : 1792#64 ≤ key - st ∧ 32#64 ≤ st - key)
    (s : State) (hP : Pre fb st key flags plat target ra b0 bp0 s12 s13 s14 s15 len0 k0 k1 es0 m0 s) :
    ∃ k s', steps Code_merge.prog k s = some s' ∧ Inv fb st key flags plat target ra b0 bp0 s12 s13 s14 s15 k0 k1 es0 m0 s' := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r12, r13, r14, r15, zf, cf, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, mem, pc⟩ := s
  obtain ⟨hpc, hsp, hdi, hsi, hdx, hcx, h8, hbx, hbp, h12, h13, h14, h15, hmem, hF, hRa, hH, hK0, hK1⟩ := hP
  simp only at hpc hsp hdi hsi hdx hcx h8 hbx hbp h12 h13 h14 h15 hmem
  subst pc rsp rdi rsi rdx rcx r8 rbx rbp r12 r13 r14 r15 mem
  have hHc := Stack.cells hH
  split_ands hHc
  refine ⟨18 + 0, ?_⟩
  refine run_then (s1 := ?_) ?_ ?_
  case refine_2 => run_fn []; rfl
  refine ⟨_, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  all_goals dsimp only
  · mem_region
  · mem_fact
  · mem_fact
  · mem_fact
  · mem_fact
  · mem_fact
  · mem_fact
  · mem_fact
  · intro x hx1 hx2
    mem_away
  · apply Exists.intro; apply Exists.intro
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · mem_fact
    · apply Stack.frame hH
      intro x hx
      mem_away
    · rfl
    · rfl
    · mem_fact
    · mem_fact

theorem leave (fb st key flags plat target ra b0 bp0 s12 s13 s14 s15 : BitVec 64) (k0 k1 : V) (es0 : Stack.Cvs) (m0 : Mem)
    (aFS : 184#64 ≤ st - fb ∧ 1792#64 ≤ fb - st) (aFK : 184#64 ≤ key - fb ∧ 32#64 ≤ fb - key) (aSK : 1792#64 ≤ key - st ∧ 32#64 ≤ st - key)
    (s : State) (hI : Inv fb st key flags plat target ra b0 bp0 s12 s13 s14 s15 k0 k1 es0 m0 s) (hc : ¬ target < s.r15) :
    ∃ k s', steps Code_merge.prog k s = some s' ∧ Post fb st flags target ra b0 bp0 s12 s13 s14 s15 k0 k1 es0 m0 s' := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r12, r13, r14, len, zf, cf, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, mem, pc⟩ := s
  obtain ⟨hpc, hsp, hbx, hbp, h12, h13, h14, hF, hRa, hS0, hS1, hS2, hS3, hS4, hS5, hOut, pf, es, hPf, hH, hSpec, hpf, hK0, hK1⟩ := hI
  simp only at hpc hsp hbx hbp h12 h13 h14 hF hRa hS0 hS1 hS2 hS3 hS4 hS5 hOut hPf hH hSpec hK0 hK1 hc
  subst pc rsp rbx rbp r12 r13 r14 pf
  have c1 : target.ult len = false := by bv_decide
  refine ⟨13 + 0, ?_⟩
  refine run_then (s1 := ?_) ?_ ?_
  case refine_2 => run_fn [c1]; rfl
  refine ⟨_, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩⟩
  all_goals dsimp only
  · exact hOut
  · rw [← hSpec, Stack.merged_done k0 k1 _ target len es hH.1 hc]
    exact hH

/-- **`merge`, as assembled, meets its contract.** -/
theorem merge_meets_its_contract (fb st key flags plat target ra b0 bp0 s12 s13 s14 s15 len0 : BitVec 64) (k0 k1 : V) (es0 : Stack.Cvs) (m0 : Mem)
    (hT1 : 1#64 ≤ target) (hfl : flags < 256#64)
    (aFS : 184#64 ≤ st - fb ∧ 1792#64 ≤ fb - st) (aFK : 184#64 ≤ key - fb ∧ 32#64 ≤ fb - key) (aSK : 1792#64 ≤ key - st ∧ 32#64 ≤ st - key) :
    Hoare.Triple Code_merge.prog (Pre fb st key flags plat target ra b0 bp0 s12 s13 s14 s15 len0 k0 k1 es0 m0)
      (Post fb st flags target ra b0 bp0 s12 s13 s14 s15 k0 k1 es0 m0) := by
  refine Hoare.seq (Q := Inv fb st key flags plat target ra b0 bp0 s12 s13 s14 s15 k0 k1 es0 m0) ?_ ?_
  · intro s hP
    exact enter fb st key flags plat target ra b0 bp0 s12 s13 s14 s15 len0 k0 k1 es0 m0 aFS aFK aSK s hP
  · refine Hoare.loop (fun s => s.r15.toNat) (fun s hI => ?_)
    by_cases hc : target < s.r15
    · obtain ⟨k, s', h, hi, hm⟩ := turn fb st key flags plat target ra b0 bp0 s12 s13 s14 s15 k0 k1 es0 m0 hT1 hfl aFS aFK aSK s hI hc
      exact ⟨k, s', h, Or.inl ⟨hi, hm⟩⟩
    · obtain ⟨k, s', h, hq⟩ := leave fb st key flags plat target ra b0 bp0 s12 s13 s14 s15 k0 k1 es0 m0 aFS aFK aSK s hI hc
      exact ⟨k, s', h, Or.inr hq⟩

#print axioms merge_meets_its_contract

end MergeOde
