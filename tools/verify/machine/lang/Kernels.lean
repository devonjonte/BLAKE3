import Cells
import SseProof
import AvxProof
open X86 Cells

/-! # The kernels' contracts, as a caller written in the language uses them

`one/AvxProof.lean` and `one/SseProof.lean` prove what the two one-block compression kernels do, for
the program `Code.prog`. Here the same contracts are stated for any program that has the kernels'
instructions, on a state that is written out, with the result written out too: what a generated proof
needs at a call. -/

namespace Kernels

/-- What a one-block kernel leaves at its first argument: the first eight words of the specification's
compression, as the two vectors of a chaining value. -/
def out (cv0 cv1 b0 b1 b2 b3 : V) (counter : BitVec 64) (len flags : BitVec 32) : V × V :=
  let c := specCv (cvWords cv0 cv1) (blockWords b0 b1 b2 b3) counter len flags
  (mk4 c[0] c[1] c[2] c[3], mk4 c[4] c[5] c[6] c[7])

theorem apart_bytes {rsp rdi : BitVec 64} (h : 32#64 ≤ rsp - rdi ∧ 8#64 ≤ rdi - rsp) :
    ∀ x : BitVec 64, (x - rsp).toNat < 8 → 32 ≤ (x - rdi).toNat := by
  intro x hx; obtain ⟨h1, h2⟩ := h; bv_omega

/-- **A call of `blake3_servil_compress_in_place_avx512`**, in any program that has the kernels. -/
theorem call_avx {prog : Nat → Option (Instr × Nat)} (hk : ∀ pc x, Code.prog pc = some x → prog pc = some x)
    (cv0 cv1 b0 b1 b2 b3 : V) (ra : BitVec 64)
    (rax rcx rdx rbx rsp rbp rsi rdi r8 r9 r12 r13 r14 r15 : BitVec 64) (zf cf : Option Bool) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : V) (mem : Mem)
    (hc0 : Vec mem rdi cv0) (hc1 : Vec mem (rdi + 16#64) cv1)
    (hb0 : Vec mem rsi b0) (hb1 : Vec mem (rsi + 16#64) b1) (hb2 : Vec mem (rsi + 32#64) b2) (hb3 : Vec mem (rsi + 48#64) b3)
    (hret : Quad mem rsp ra) (hapart : 32#64 ≤ rsp - rdi ∧ 8#64 ≤ rdi - rsp) :
    ∃ (rax' rcx' rdx' rsi' rdi' r8' r9' : BitVec 64) (zf' cf' : Option Bool) (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 : V),
      steps prog 362 ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r12, r13, r14, r15, zf, cf, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, mem, 0x30000⟩ =
        some ⟨rax', rcx', rdx', rbx, rsp + 8#64, rbp, rsi', rdi', r8', r9', r12, r13, r14, r15, zf', cf', y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15,
          (mem.put128 rdi (out cv0 cv1 b0 b1 b2 b3 rcx ((rdx.setWidth 8).setWidth 32) ((r8.setWidth 8).setWidth 32)).1).put128 (rdi + 16#64)
            (out cv0 cv1 b0 b1 b2 b3 rcx ((rdx.setWidth 8).setWidth 32) ((r8.setWidth 8).setWidth 32)).2, ra.toNat⟩ := by
  obtain ⟨s', hs, hpc, hsp, hmem, hbx, hbp, h12, h13, h14, h15⟩ :=
    Avx.contract cv0 cv1 b0 b1 b2 b3 ra ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r12, r13, r14, r15, zf, cf, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, mem, 0x30000⟩
      rfl (by simpa using hc0) hc1 (by simpa using hb0) hb1 hb2 hb3 (read_quad hret) (apart_bytes hapart)
  obtain ⟨rax', rcx', rdx', rbx', rsp', rbp', rsi', rdi', r8', r9', r12', r13', r14', r15', zf', cf', y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, mem', pc'⟩ := s'
  simp only at hpc hsp hmem hbx hbp h12 h13 h14 h15
  subst hpc hsp hmem hbx hbp h12 h13 h14 h15
  refine ⟨rax', rcx', rdx', rsi', rdi', r8', r9', zf', cf', y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, ?_⟩
  rw [steps_mono hk _ _ _ hs]
  simp only [out, BitVec.add_zero, BitVec.ofNat_eq_ofNat]

/-- **A call of `blake3_servil_compress_in_place_sse41`**, in any program that has the kernels. It reads
the length from all of EDX and the flags from all of R8D. -/
theorem call_sse {prog : Nat → Option (Instr × Nat)} (hk : ∀ pc x, Code.prog pc = some x → prog pc = some x)
    (cv0 cv1 b0 b1 b2 b3 : V) (ra : BitVec 64)
    (rax rcx rdx rbx rsp rbp rsi rdi r8 r9 r12 r13 r14 r15 : BitVec 64) (zf cf : Option Bool) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : V) (mem : Mem)
    (hc0 : Vec mem rdi cv0) (hc1 : Vec mem (rdi + 16#64) cv1)
    (hb0 : Vec mem rsi b0) (hb1 : Vec mem (rsi + 16#64) b1) (hb2 : Vec mem (rsi + 32#64) b2) (hb3 : Vec mem (rsi + 48#64) b3)
    (hlen : rdx = (rdx.setWidth 32).setWidth 64)
    (hret : Quad mem rsp ra) (hapart : 32#64 ≤ rsp - rdi ∧ 8#64 ≤ rdi - rsp) :
    ∃ (rax' rcx' rdx' rsi' rdi' r8' r9' : BitVec 64) (zf' cf' : Option Bool) (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 : V),
      steps prog 467 ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r12, r13, r14, r15, zf, cf, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, mem, 0x20000⟩ =
        some ⟨rax', rcx', rdx', rbx, rsp + 8#64, rbp, rsi', rdi', r8', r9', r12, r13, r14, r15, zf', cf', y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15,
          (mem.put128 rdi (out cv0 cv1 b0 b1 b2 b3 rcx (rdx.setWidth 32) (r8.setWidth 32)).1).put128 (rdi + 16#64)
            (out cv0 cv1 b0 b1 b2 b3 rcx (rdx.setWidth 32) (r8.setWidth 32)).2, ra.toNat⟩ := by
  obtain ⟨s', hs, hpc, hsp, hmem, hbx, hbp, h12, h13, h14, h15⟩ :=
    Sse.contract cv0 cv1 b0 b1 b2 b3 (rdx.setWidth 32) ra ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r12, r13, r14, r15, zf, cf, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, mem, 0x20000⟩
      rfl (by simpa using hc0) hc1 (by simpa using hb0) hb1 hb2 hb3 hlen (read_quad hret) (apart_bytes hapart)
  obtain ⟨rax', rcx', rdx', rbx', rsp', rbp', rsi', rdi', r8', r9', r12', r13', r14', r15', zf', cf', y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, mem', pc'⟩ := s'
  simp only at hpc hsp hmem hbx hbp h12 h13 h14 h15
  subst hpc hsp hmem hbx hbp h12 h13 h14 h15
  refine ⟨rax', rcx', rdx', rsi', rdi', r8', r9', zf', cf', y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, ?_⟩
  rw [steps_mono hk _ _ _ hs]
  simp only [out, BitVec.add_zero, BitVec.ofNat_eq_ofNat]

/-- The call of the AVX kernel, then the rest of a run. -/
theorem call_avx_then {prog : Nat → Option (Instr × Nat)} (hk : ∀ pc x, Code.prog pc = some x → prog pc = some x)
    {cv0 cv1 b0 b1 b2 b3 : V} {ra : BitVec 64}
    {rax rcx rdx rbx rsp rbp rsi rdi r8 r9 r12 r13 r14 r15 : BitVec 64} {zf cf : Option Bool} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : V} {mem : Mem}
    {k : Nat} {Q : State → Prop}
    (hc0 : Vec mem rdi cv0) (hc1 : Vec mem (rdi + 16#64) cv1)
    (hb0 : Vec mem rsi b0) (hb1 : Vec mem (rsi + 16#64) b1) (hb2 : Vec mem (rsi + 32#64) b2) (hb3 : Vec mem (rsi + 48#64) b3)
    (hret : Quad mem rsp ra) (hapart : 32#64 ≤ rsp - rdi ∧ 8#64 ≤ rdi - rsp)
    (next : ∀ (rax' rcx' rdx' rsi' rdi' r8' r9' : BitVec 64) (zf' cf' : Option Bool) (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 : V),
      ∃ s', steps prog k ⟨rax', rcx', rdx', rbx, rsp + 8#64, rbp, rsi', rdi', r8', r9', r12, r13, r14, r15, zf', cf', y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15,
          (mem.put128 rdi (out cv0 cv1 b0 b1 b2 b3 rcx ((rdx.setWidth 8).setWidth 32) ((r8.setWidth 8).setWidth 32)).1).put128 (rdi + 16#64)
            (out cv0 cv1 b0 b1 b2 b3 rcx ((rdx.setWidth 8).setWidth 32) ((r8.setWidth 8).setWidth 32)).2, ra.toNat⟩ = some s' ∧ Q s') :
    ∃ s', steps prog (362 + k) ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r12, r13, r14, r15, zf, cf, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, mem, 0x30000⟩ = some s' ∧ Q s' := by
  obtain ⟨rax', rcx', rdx', rsi', rdi', r8', r9', zf', cf', y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, h⟩ :=
    call_avx hk cv0 cv1 b0 b1 b2 b3 ra rax rcx rdx rbx rsp rbp rsi rdi r8 r9 r12 r13 r14 r15 zf cf x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 mem
      hc0 hc1 hb0 hb1 hb2 hb3 hret hapart
  exact Cells.run_then h (next rax' rcx' rdx' rsi' rdi' r8' r9' zf' cf' y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15)

/-- The call of the SSE kernel, then the rest of a run. -/
theorem call_sse_then {prog : Nat → Option (Instr × Nat)} (hk : ∀ pc x, Code.prog pc = some x → prog pc = some x)
    {cv0 cv1 b0 b1 b2 b3 : V} {ra : BitVec 64}
    {rax rcx rdx rbx rsp rbp rsi rdi r8 r9 r12 r13 r14 r15 : BitVec 64} {zf cf : Option Bool} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : V} {mem : Mem}
    {k : Nat} {Q : State → Prop}
    (hc0 : Vec mem rdi cv0) (hc1 : Vec mem (rdi + 16#64) cv1)
    (hb0 : Vec mem rsi b0) (hb1 : Vec mem (rsi + 16#64) b1) (hb2 : Vec mem (rsi + 32#64) b2) (hb3 : Vec mem (rsi + 48#64) b3)
    (hlen : rdx = (rdx.setWidth 32).setWidth 64)
    (hret : Quad mem rsp ra) (hapart : 32#64 ≤ rsp - rdi ∧ 8#64 ≤ rdi - rsp)
    (next : ∀ (rax' rcx' rdx' rsi' rdi' r8' r9' : BitVec 64) (zf' cf' : Option Bool) (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 : V),
      ∃ s', steps prog k ⟨rax', rcx', rdx', rbx, rsp + 8#64, rbp, rsi', rdi', r8', r9', r12, r13, r14, r15, zf', cf', y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15,
          (mem.put128 rdi (out cv0 cv1 b0 b1 b2 b3 rcx (rdx.setWidth 32) (r8.setWidth 32)).1).put128 (rdi + 16#64)
            (out cv0 cv1 b0 b1 b2 b3 rcx (rdx.setWidth 32) (r8.setWidth 32)).2, ra.toNat⟩ = some s' ∧ Q s') :
    ∃ s', steps prog (467 + k) ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r12, r13, r14, r15, zf, cf, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, mem, 0x20000⟩ = some s' ∧ Q s' := by
  obtain ⟨rax', rcx', rdx', rsi', rdi', r8', r9', zf', cf', y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, h⟩ :=
    call_sse hk cv0 cv1 b0 b1 b2 b3 ra rax rcx rdx rbx rsp rbp rsi rdi r8 r9 r12 r13 r14 r15 zf cf x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 mem
      hc0 hc1 hb0 hb1 hb2 hb3 hlen hret hapart
  exact Cells.run_then h (next rax' rcx' rdx' rsi' rdi' r8' r9' zf' cf' y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15)

/-- The call of the AVX kernel in a run: its contract's facts, then the rest of the run from the state it returns in. -/
theorem call_avx_runs {prog : Nat → Option (Instr × Nat)} (hk : ∀ pc x, Code.prog pc = some x → prog pc = some x)
    {cv0 cv1 b0 b1 b2 b3 : V} {ra : BitVec 64}
    {rax rcx rdx rbx rsp rbp rsi rdi r8 r9 r12 r13 r14 r15 : BitVec 64} {zf cf : Option Bool} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : V} {mem : Mem}
    {Q : State → Prop}
    (hc0 : Vec mem rdi cv0) (hc1 : Vec mem (rdi + 16#64) cv1)
    (hb0 : Vec mem rsi b0) (hb1 : Vec mem (rsi + 16#64) b1) (hb2 : Vec mem (rsi + 32#64) b2) (hb3 : Vec mem (rsi + 48#64) b3)
    (hret : Quad mem rsp ra) (hapart : 32#64 ≤ rsp - rdi ∧ 8#64 ≤ rdi - rsp)
    (next : ∀ (rax' rcx' rdx' rsi' rdi' r8' r9' : BitVec 64) (zf' cf' : Option Bool) (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 : V),
      Runs prog ⟨rax', rcx', rdx', rbx, rsp + 8#64, rbp, rsi', rdi', r8', r9', r12, r13, r14, r15, zf', cf', y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15,
          (mem.put128 rdi (out cv0 cv1 b0 b1 b2 b3 rcx ((rdx.setWidth 8).setWidth 32) ((r8.setWidth 8).setWidth 32)).1).put128 (rdi + 16#64)
            (out cv0 cv1 b0 b1 b2 b3 rcx ((rdx.setWidth 8).setWidth 32) ((r8.setWidth 8).setWidth 32)).2, ra.toNat⟩ Q) :
    Runs prog ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r12, r13, r14, r15, zf, cf, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, mem, 0x30000⟩ Q := by
  obtain ⟨rax', rcx', rdx', rsi', rdi', r8', r9', zf', cf', y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, h⟩ :=
    call_avx hk cv0 cv1 b0 b1 b2 b3 ra rax rcx rdx rbx rsp rbp rsi rdi r8 r9 r12 r13 r14 r15 zf cf x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 mem
      hc0 hc1 hb0 hb1 hb2 hb3 hret hapart
  exact Cells.runs_then h (next rax' rcx' rdx' rsi' rdi' r8' r9' zf' cf' y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15)

/-- The call of the SSE kernel in a run: its contract's facts, then the rest of the run from the state it returns in. -/
theorem call_sse_runs {prog : Nat → Option (Instr × Nat)} (hk : ∀ pc x, Code.prog pc = some x → prog pc = some x)
    {cv0 cv1 b0 b1 b2 b3 : V} {ra : BitVec 64}
    {rax rcx rdx rbx rsp rbp rsi rdi r8 r9 r12 r13 r14 r15 : BitVec 64} {zf cf : Option Bool} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : V} {mem : Mem}
    {Q : State → Prop}
    (hc0 : Vec mem rdi cv0) (hc1 : Vec mem (rdi + 16#64) cv1)
    (hb0 : Vec mem rsi b0) (hb1 : Vec mem (rsi + 16#64) b1) (hb2 : Vec mem (rsi + 32#64) b2) (hb3 : Vec mem (rsi + 48#64) b3)
    (hlen : rdx = (rdx.setWidth 32).setWidth 64)
    (hret : Quad mem rsp ra) (hapart : 32#64 ≤ rsp - rdi ∧ 8#64 ≤ rdi - rsp)
    (next : ∀ (rax' rcx' rdx' rsi' rdi' r8' r9' : BitVec 64) (zf' cf' : Option Bool) (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 : V),
      Runs prog ⟨rax', rcx', rdx', rbx, rsp + 8#64, rbp, rsi', rdi', r8', r9', r12, r13, r14, r15, zf', cf', y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15,
          (mem.put128 rdi (out cv0 cv1 b0 b1 b2 b3 rcx (rdx.setWidth 32) (r8.setWidth 32)).1).put128 (rdi + 16#64)
            (out cv0 cv1 b0 b1 b2 b3 rcx (rdx.setWidth 32) (r8.setWidth 32)).2, ra.toNat⟩ Q) :
    Runs prog ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r12, r13, r14, r15, zf, cf, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, mem, 0x20000⟩ Q := by
  obtain ⟨rax', rcx', rdx', rsi', rdi', r8', r9', zf', cf', y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, h⟩ :=
    call_sse hk cv0 cv1 b0 b1 b2 b3 ra rax rcx rdx rbx rsp rbp rsi rdi r8 r9 r12 r13 r14 r15 zf cf x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 mem
      hc0 hc1 hb0 hb1 hb2 hb3 hlen hret hapart
  exact Cells.runs_then h (next rax' rcx' rdx' rsi' rdi' r8' r9' zf' cf' y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15)

end Kernels
