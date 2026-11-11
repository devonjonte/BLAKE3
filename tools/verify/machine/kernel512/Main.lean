import Final
open Simd Flat Blake3Generic

/-- A chaining value's eight words, as its two cells hold them. -/
def cvWords (cv0 cv1 : V) : Vector (BitVec 32) 8 :=
  #v[dw cv0 0, dw cv0 1, dw cv0 2, dw cv0 3, dw cv1 0, dw cv1 1, dw cv1 2, dw cv1 3]

/-- A block's sixteen words, as its four cells hold them. -/
def blockWords (b0 b1 b2 b3 : V) : Vector (BitVec 32) 16 :=
  #v[dw b0 0, dw b0 1, dw b0 2, dw b0 3, dw b1 0, dw b1 1, dw b1 2, dw b1 3,
    dw b2 0, dw b2 1, dw b2 2, dw b2 3, dw b3 0, dw b3 1, dw b3 2, dw b3 3]

theorem low8_0 (w : Vector (BitVec 32) 16) : (low8 w)[0] = w[0] ^^^ w[8] := rfl
theorem low8_1 (w : Vector (BitVec 32) 16) : (low8 w)[1] = w[1] ^^^ w[9] := rfl
theorem low8_2 (w : Vector (BitVec 32) 16) : (low8 w)[2] = w[2] ^^^ w[10] := rfl
theorem low8_3 (w : Vector (BitVec 32) 16) : (low8 w)[3] = w[3] ^^^ w[11] := rfl
theorem low8_4 (w : Vector (BitVec 32) 16) : (low8 w)[4] = w[4] ^^^ w[12] := rfl
theorem low8_5 (w : Vector (BitVec 32) 16) : (low8 w)[5] = w[5] ^^^ w[13] := rfl
theorem low8_6 (w : Vector (BitVec 32) 16) : (low8 w)[6] = w[6] ^^^ w[14] := rfl
theorem low8_7 (w : Vector (BitVec 32) 16) : (low8 w)[7] = w[7] ^^^ w[15] := rfl

set_option maxRecDepth 1000000 in
/-- **`blake3_servil_compress_in_place_avx512` is the specification's compression function.**
Called with a chaining value at RDI, a block at RSI, the block's length in DL, the counter in
RCX and the flags in R8B, the kernel's 362 instructions run to its return
and leave at RDI the first eight words of the specification's `BLAKE3_COMPRESS` of them
(sections 2.2 to 3.3 of C2SP's BLAKE3, `Generic.lean`, at 32-bit words); no other cell is changed. -/
theorem compress_in_place_avx512_is_the_compression (cv0 cv1 b0 b1 b2 b3 : V) (s : State)
    (hpc : s.pc = 0x3700)
    (hc0 : s.mem (s.rdi + 0) = some cv0) (hc1 : s.mem (s.rdi + 16) = some cv1)
    (hb0 : s.mem (s.rsi + 0) = some b0) (hb1 : s.mem (s.rsi + 16) = some b1)
    (hb2 : s.mem (s.rsi + 32) = some b2) (hb3 : s.mem (s.rsi + 48) = some b3) :
    ∃ s', steps Code.prog 362 s = some s' ∧ s'.pc = s.ra ∧ s'.rsp = s.rsp + 8 ∧
      s'.mem (s.rdi + 0) = some (mk4
        (specCv (cvWords cv0 cv1) (blockWords b0 b1 b2 b3) s.rcx ((s.rdx.setWidth 8).setWidth 32) ((s.r8.setWidth 8).setWidth 32))[0]
        (specCv (cvWords cv0 cv1) (blockWords b0 b1 b2 b3) s.rcx ((s.rdx.setWidth 8).setWidth 32) ((s.r8.setWidth 8).setWidth 32))[1]
        (specCv (cvWords cv0 cv1) (blockWords b0 b1 b2 b3) s.rcx ((s.rdx.setWidth 8).setWidth 32) ((s.r8.setWidth 8).setWidth 32))[2]
        (specCv (cvWords cv0 cv1) (blockWords b0 b1 b2 b3) s.rcx ((s.rdx.setWidth 8).setWidth 32) ((s.r8.setWidth 8).setWidth 32))[3]) ∧
      s'.mem (s.rdi + 16) = some (mk4
        (specCv (cvWords cv0 cv1) (blockWords b0 b1 b2 b3) s.rcx ((s.rdx.setWidth 8).setWidth 32) ((s.r8.setWidth 8).setWidth 32))[4]
        (specCv (cvWords cv0 cv1) (blockWords b0 b1 b2 b3) s.rcx ((s.rdx.setWidth 8).setWidth 32) ((s.r8.setWidth 8).setWidth 32))[5]
        (specCv (cvWords cv0 cv1) (blockWords b0 b1 b2 b3) s.rcx ((s.rdx.setWidth 8).setWidth 32) ((s.r8.setWidth 8).setWidth 32))[6]
        (specCv (cvWords cv0 cv1) (blockWords b0 b1 b2 b3) s.rcx ((s.rdx.setWidth 8).setWidth 32) ((s.r8.setWidth 8).setWidth 32))[7]) ∧
      ∀ a, a ≠ s.rdi + 0 → a ≠ s.rdi + 16 → s'.mem a = s.mem a := by
  obtain ⟨s1, e1, pc1, r1, m1, al1, di1, sp1, mem1, ra1⟩ :=
    start cv0 cv1 b0 b1 b2 b3 s hpc hc0 hc1 hb0 hb1 hb2 hb3
  have H1 : Head s1 _ _ 7 := ⟨pc1, r1, m1, al1⟩
  obtain ⟨s2, e2, H2, di2, sp2, mem2, ra2⟩ := iter _ _ 7 s1 H1 (by decide)
  have H2 : Head s2 _ _ 6 := H2
  have di2 := di2.trans di1; have sp2 := sp2.trans sp1; have mem2 := mem2.trans mem1; have ra2 := ra2.trans ra1
  obtain ⟨s3, e3, H3, di3, sp3, mem3, ra3⟩ := iter _ _ 6 s2 H2 (by decide)
  have H3 : Head s3 _ _ 5 := H3
  have di3 := di3.trans di2; have sp3 := sp3.trans sp2; have mem3 := mem3.trans mem2; have ra3 := ra3.trans ra2
  obtain ⟨s4, e4, H4, di4, sp4, mem4, ra4⟩ := iter _ _ 5 s3 H3 (by decide)
  have H4 : Head s4 _ _ 4 := H4
  have di4 := di4.trans di3; have sp4 := sp4.trans sp3; have mem4 := mem4.trans mem3; have ra4 := ra4.trans ra3
  obtain ⟨s5, e5, H5, di5, sp5, mem5, ra5⟩ := iter _ _ 4 s4 H4 (by decide)
  have H5 : Head s5 _ _ 3 := H5
  have di5 := di5.trans di4; have sp5 := sp5.trans sp4; have mem5 := mem5.trans mem4; have ra5 := ra5.trans ra4
  obtain ⟨s6, e6, H6, di6, sp6, mem6, ra6⟩ := iter _ _ 3 s5 H5 (by decide)
  have H6 : Head s6 _ _ 2 := H6
  have di6 := di6.trans di5; have sp6 := sp6.trans sp5; have mem6 := mem6.trans mem5; have ra6 := ra6.trans ra5
  obtain ⟨s7, e7, H7, di7, sp7, mem7, ra7⟩ := iter _ _ 2 s6 H6 (by decide)
  have H7 : Head s7 _ _ 1 := H7
  have di7 := di7.trans di6; have sp7 := sp7.trans sp6; have mem7 := mem7.trans mem6; have ra7 := ra7.trans ra6
  obtain ⟨s8, e8, pc8, sp8, o0, o1, fr⟩ := last _ _ s7 H7
    (by rw [mem7, di7, hc0]; rfl) (by rw [mem7, di7, hc1]; rfl)
  refine ⟨s8, ?_, by rw [pc8, ra7], by rw [sp8, sp7], ?_, ?_, ?_⟩
  · rw [show 362 = 21 + (50 + (50 + (50 + (50 + (50 + (50 + 41)))))) from rfl, steps_add, e1, Option.bind_some, steps_add, e2, Option.bind_some, steps_add, e3, Option.bind_some, steps_add, e4, Option.bind_some, steps_add, e5, Option.bind_some, steps_add, e6, Option.bind_some, steps_add, e7, Option.bind_some, e8]
  · rw [← di7, spec_eq, low8_0, low8_1, low8_2, low8_3]
    exact o0
  · rw [← di7, spec_eq, low8_4, low8_5, low8_6, low8_7]
    exact o1
  · intro a ha0 ha1
    rw [fr a (by rw [di7]; exact ha0) (by rw [di7]; exact ha1), mem7]

#print axioms compress_in_place_avx512_is_the_compression
