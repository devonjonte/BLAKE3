import Cells
import Code_push
open X86 Cells

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem push_lab (fb st cv ra len : BitVec 64) (c0 c1 : V) (m : Mem)
    (rax rcx rdx rbx rbp r8 r9 r12 r13 r14 r15 : BitVec 64) (zf cf : Option Bool) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : V)
    (hlen : len < 55#64)
    (hF : Region m fb 24#64) (hRet : Quad m (fb + 24#64) ra)
    (hLen : Quad m st len) (hS : Region m st 1792#64)
    (hC0 : Vec m cv c0) (hC1 : Vec m (cv + 16#64) c1)
    (aS : 1792#64 ≤ fb - st ∧ 32#64 ≤ st - fb)
    (aC : 32#64 ≤ fb - cv ∧ 32#64 ≤ cv - fb) (aSC : 1792#64 ≤ cv - st ∧ 32#64 ≤ st - cv) :
    ∃ s', steps Code_push.prog 32 ⟨rax, rcx, rdx, rbx, fb + 24#64, rbp, cv, st, r8, r9, r12, r13, r14, r15, zf, cf, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, m, 0x61000⟩ = some s' ∧
      s'.pc = ra.toNat := by
  have rLen := read_quad hLen
  have rRet := read_quad hRet
  have rC0 := read_vec hC0
  have rC1 := read_vec hC1
  have hj : len.ult 55#64 = true := by bv_decide
  run_fn [hj]
  trace_state
  sorry
