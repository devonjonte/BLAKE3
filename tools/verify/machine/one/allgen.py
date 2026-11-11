#!/usr/bin/env python3
"""Write MergeAll.lean: merge's loop and the whole function with the observer, from the statements and
proofs of MergeLoop.lean and MergeWhole.lean (the same steps, the trace carried along)."""
import re, pathlib
here = pathlib.Path(__file__).resolve().parent
loopf = (here / "MergeLoop.lean").read_text(); wholef = (here / "MergeWhole.lean").read_text()
M1 = "18446744073709551615#64"; M2 = "18446744073709551614#64"; N = lambda k: f"{2**64 - k}#64"
OL = f"((len + {M2}) <<< 5)"; OR = f"((len + {M1}) <<< 5)"
regs = "rax rcx rdx rbx rsp rbp rsi rdi r8 r9 r12 r13 r14 r15".split(); xs = [f"x{i}" for i in range(16)]
def state(pc, mem="m", **over):
    return "⟨" + ", ".join(over.get(r, r) for r in regs) + ", zf, cf, " + ", ".join(xs) + f", {mem}, {pc}⟩"
head = state("0x40094", rax="len", rbx="self", rsp="fp", r12="arr", r14="keyp", r15="nB")
free = "rcx rdx rbp rsi rdi r8 r9 r13"; X = " ".join(xs); ys = " ".join(f"y{i}" for i in range(16))

def stmt(text, name, opener):
    a = text.index(f"theorem {name} "); blk = text[a:]
    i = blk.index(opener); j = blk.index(":= by\n", i)
    return blk[len(f"theorem {name} "):i], blk[i:j]

# --- one turn, by whichever kernel
tb, tc = stmt(loopf, "turn", " :\n    ∃ K s', steps Code.prog K")
facts = tc[tc.index("= some s' ∧") + len("= some s' ∧"):].strip().replace("s'.", "S.core.")
turnL = f'''
/-- The instructions of one turn, by the platform's kernel. -/
def turnK (plat : BitVec 8) : Nat := if plat = 5#8 then 52 + (362 + 12) else 52 + (467 + 13)

/-- What one turn shows. -/
noncomputable def turnShows (plat : BitVec 8) (self arr keyp fp len : BitVec 64) (last : Bool) : List Obs :=
  if plat = 5#8 then turn_avx_shows self arr keyp fp len last else turn_sse_shows self arr keyp fp len last

set_option maxRecDepth 1000000 in
theorem turnL {tb} :
    ∃ S, stepsL Code.prog (turnK plat) ⟨{head}, []⟩ = some S ∧
      S.leak = turnShows plat self arr keyp fp len (decide (nB - 1#64 = 0#64)) ∧
      {facts} := by
  by_cases h : plat = 5#8
  · subst h
    simp only [turnK, turnShows, ↓reduceIte]
    exact both (turn_avx self arr keyp fp len nB l0 l1 r0 r1 k0 k1 fl m {free} zf cf {X}
        hlo hhi hfp hTag hLen hL0 hL1 hR0 hR1 hK0 hK1 hOwn hPlat hFl hF0 hF1 hF2 hF3 oSlot oKey oSelf hLS)
      (turn_avx_leak self arr keyp fp len nB l0 l1 r0 r1 k0 k1 fl m {free} zf cf {X}
        hlo hhi hfp hTag hLen hL0 hL1 hR0 hR1 hK0 hK1 hOwn hPlat hFl hF0 hF1 hF2 hF3 oSlot oKey oSelf hLS)
  · simp only [turnK, turnShows, h, ↓reduceIte]
    exact both (turn_sse self arr keyp fp len nB l0 l1 r0 r1 k0 k1 fl m {free} zf cf {X}
        hlo hhi hfp hTag hLen hL0 hL1 hR0 hR1 hK0 hK1 hOwn plat h hPlat hFl hF0 hF1 hF2 hF3 oSlot oKey oSelf hLS)
      (turn_sse_leak self arr keyp fp len nB l0 l1 r0 r1 k0 k1 fl m {free} zf cf {X}
        hlo hhi hfp hTag hLen hL0 hL1 hR0 hR1 hK0 hK1 hOwn plat h hPlat hFl hF0 hF1 hF2 hF3 oSlot oKey oSelf hLS)
'''
# --- the loop
loopL = f'''
/-- What `n` turns show, the newest on top: a function of where things are, the platform, the length and
the turns to go. No value of the stack, no byte of the key or the flags is among its arguments. -/
noncomputable def loopShows (plat : BitVec 8) (self arr keyp fp : BitVec 64) : Nat → BitVec 64 → BitVec 64 → List Obs
  | 0, _, _ => []
  | k + 1, len, nB => loopShows plat self arr keyp fp k (len - 1#64) (nB - 1#64) ++
      turnShows plat self arr keyp fp len (decide (nB - 1#64 = 0#64))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem loopL (self arr keyp fp : BitVec 64) (k0 k1 : V) (fl plat : BitVec 8) (P : Places self arr keyp fp) :
    ∀ (n : Nat) (es : List (V × V)) (len nB : BitVec 64) (m : Mem) ({free} : BitVec 64) (zf cf : Option Bool) ({X} : V),
      1 ≤ n → n + 1 ≤ es.length → len.toNat = es.length → es.length ≤ 55 → nB.toNat = n →
      Head self arr keyp fp k0 k1 fl plat m len es →
      ∃ S, stepsL Code.prog (n * turnK plat) ⟨{head}, []⟩ = some S ∧
        S.leak = loopShows plat self arr keyp fp n len nB ∧
        S.core.pc = 0x401AB ∧ S.core.rbx = self ∧ S.core.rsp = fp ∧ S.core.rbp = rbp ∧ S.core.r12 = arr ∧ S.core.r14 = keyp ∧
        Quad S.core.mem (self + 0#64) (len - nB) ∧
        Entries S.core.mem (arr + (len - nB + {M1}) <<< 5) (mergeN k0 k1 fl n es) ∧
        S.core.mem (self + 8#64) = some 1#8 ∧
        (∀ x : BitVec 64, inF (x - fp) = false → 1760 ≤ (x - arr).toNat → 9 ≤ (x - self).toNat → S.core.mem x = m x) := by
  obtain ⟨harr, hfp, hW, gArr, gKey, gSelf, gKeyArr, gKeySelf⟩ := P
  intro n
  induction n with
  | zero => intro es len nB m {free} zf cf {X} h1; omega
  | succ k ih =>
    intro es len nB m {free} zf cf {X} _ hlen2 hlen hmax hnB hH
    obtain ⟨hTag, hLen, hE, hK0, hK1, hOwn, hPlat, hFl, hF0, hF1, hF2, hF3⟩ := hH
    rcases es with _ | ⟨r, _ | ⟨l, rest⟩⟩
    · simp at hlen2
    · simp at hlen2
    simp only [List.length_cons] at hlen2 hlen hmax
    obtain ⟨hR0, hR1, hL0, hL1, hRest⟩ := hE
    have hlo : 2#64 ≤ len := by bv_omega
    have hhi : len ≤ 55#64 := by bv_omega
    have eOL : arr + {OR} - 32#64 = arr + {OL} := by bv_decide
    rw [eOL] at hL0 hL1 hRest
    have oSlot : ∀ x : BitVec 64, (x - (arr + {OL})).toNat < 64 → inF (x - fp) = false := fun x hx =>
      gArr x (by rw [shl5] at hx; bv_omega)
    have hLS : ∀ x : BitVec 64, (x - self).toNat < 8 → 32 ≤ (x - (arr + {OL})).toNat := fun x hx => by
      rw [harr, shl5]; bv_omega
    obtain ⟨⟨s1, lk1⟩, e1, hl1, pc1, ax1, r151, bx1, sp1, bp1, c12, c14, vM0, vM1, qLen1, own1, f58, f59, f60, f61, f62, f63, out1⟩ :=
      turnL self arr keyp fp len nB l.1 l.2 r.1 r.2 k0 k1 fl plat m {free} zf cf {X}
        hlo hhi hfp hTag hLen hL0 hL1 hR0 hR1 hK0 hK1 hOwn hPlat hFl hF0 hF1 hF2 hF3 oSlot gKey gSelf hLS
    simp only at hl1 pc1 ax1 r151 bx1 sp1 bp1 c12 c14 vM0 vM1 qLen1 own1 f58 f59 f60 f61 f62 f63 out1
    subst lk1
    have tag1 : s1.mem (self + 8#64) = some 1#8 := by
      rw [out1 _ (gSelf _ (by bv_omega)) (by rw [harr, shl5]; bv_omega) (by bv_omega)]; exact hTag
    have rest1 : Entries s1.mem (arr + {OL} - 32#64) rest :=
      entries_congr rest _ (fun x hx => out1 x (gArr x (by rw [shl5] at hx; bv_omega))
        (by rw [shl5] at hx ⊢; bv_omega) (by rw [shl5, harr] at hx; bv_omega)) hRest
    have key0 : Vec s1.mem (keyp + 0#64) k0 := vec_congr (fun x hx => out1 x (gKey x (by bv_omega))
      (by have := gKeyArr x (by bv_omega); rw [shl5]; bv_omega) (by have := gKeySelf x (by bv_omega); omega)) hK0
    have key1 : Vec s1.mem (keyp + 16#64) k1 := vec_congr (fun x hx => out1 x (gKey x (by bv_omega))
      (by have := gKeyArr x (by bv_omega); rw [shl5]; bv_omega) (by have := gKeySelf x (by bv_omega); omega)) hK1
    have eTop : arr + (len - 1#64 + {M1}) <<< 5 = arr + {OL} := by bv_decide
    by_cases hk : k = 0
    · subst hk
      have hnB1 : nB = 1#64 := by bv_omega
      rw [Nat.zero_add, Nat.one_mul]
      refine ⟨⟨s1, _⟩, e1, ?_, ?_, bx1, sp1, bp1, c12, c14, ?_, ?_, tag1, ?_⟩
      · simp only [loopShows, List.nil_append]
      · show s1.pc = 0x401AB; rw [pc1, hnB1]; rfl
      · show Quad s1.mem _ _; rw [hnB1]; exact qLen1
      · show Entries s1.mem _ _; rw [hnB1, eTop]; exact ⟨vM0, vM1, rest1⟩
      · intro x hx ha hs; exact out1 x hx (by rw [shl5]; bv_omega) (by omega)
    · have hne : nB - 1#64 ≠ 0#64 := by bv_omega
      have pc1' : s1.pc = 0x40094 := by rw [pc1, if_neg hne]
      obtain ⟨rax1, rcx1, rdx1, rbx1, rsp1, rbp1, rsi1, rdi1, r81, r91, r121, r131, r141, r151v, zf1, cf1, {", ".join(ys.split())}, m1, pcv⟩ := s1
      simp only at pc1' ax1 r151 bx1 sp1 bp1 c12 c14 vM0 vM1 qLen1 own1 f58 f59 f60 f61 f62 f63 out1 tag1 rest1 key0 key1
      subst pcv rax1 r151v rbx1 rsp1 rbp1 r121 r141
      have H1 : Head self arr keyp fp k0 k1 fl plat m1 (len - 1#64) (merged k0 k1 l.1 l.2 r.1 r.2 fl :: rest) :=
        ⟨tag1, qLen1, ⟨by rw [eTop]; exact vM0, by rw [eTop]; exact vM1, by rw [eTop]; exact rest1⟩, key0, key1, own1,
          f58, f59, f60, f61, f62, f63⟩
      obtain ⟨S2, e2, hl2, pc2, bx2, sp2, bp2, d12, d14, q2, E2, tag2, out2⟩ :=
        ih (merged k0 k1 l.1 l.2 r.1 r.2 fl :: rest) (len - 1#64) (nB - 1#64) m1 rcx1 rdx1 rbp rsi1 rdi1 r81 r91 r131 zf1 cf1 {ys}
          (by omega) (by simp only [List.length_cons]; omega) (by simp only [List.length_cons]; bv_omega)
          (by simp only [List.length_cons]; omega) (by bv_omega) H1
      have eD : len - nB = len - 1#64 - (nB - 1#64) := by bv_decide
      have hC := stepsL_chain Code.prog (turnK plat) (k * turnK plat) _ _ _ S2 e1 e2
      rw [show (k + 1) * turnK plat = turnK plat + k * turnK plat by rw [Nat.succ_mul, Nat.add_comm]]
      refine ⟨⟨S2.core, _⟩, hC, ?_, pc2, bx2, sp2, bp2, d12, d14, ?_, ?_, tag2, ?_⟩
      · simp only [loopShows, hl2]
      · show Quad S2.core.mem _ _; rw [eD]; exact q2
      · show Entries S2.core.mem _ _; rw [eD]; exact E2
      · intro x hx ha hs
        show S2.core.mem x = m x
        rw [out2 x hx ha hs]; exact out1 x hx (by rw [shl5]; bv_omega) (by omega)
'''
# --- the whole function
mb, mc = stmt(wholef, "merge_is_mergeN", " :\n    ∃ K s', steps Code.prog K")
entry = re.search(r"steps Code\.prog K (⟨.*?⟩) = some s'", mc, re.S).group(1)
mfacts = mc[mc.index("= some s' ∧") + len("= some s' ∧"):].strip().replace("s'.", "S.core.")
whole = f'''
/-- **What a whole call of `merge` shows**: a function of where its arguments, its stack and its caller
are, of the platform byte, and of the stack's length and the target. The stack's values, the key and the
flags are not among its arguments. -/
noncomputable def mergeShows (plat : BitVec 8) (self p keyp rsp0 fp ra len target : BitVec 64) : List Obs :=
  epilogue_shows rsp0 ra ++
    (loopShows plat self (self + 9#64) keyp fp (len - target).toNat len (len - target) ++ prologue_shows self p rsp0 fp)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- **`CvStack::merge`, as compiled: its result, its memory and what it shows, in one statement.** With
`merge_is_mergeN`'s hypotheses, the recorded run of the whole function (the kernels' instructions
included) ends with `merge_is_mergeN`'s result, and its trace is `mergeShows`. -/
theorem merge_whole {mb} :
    ∃ S, stepsL Code.prog (24 + ((len - target).toNat * turnK plat + 8)) ⟨{entry}, []⟩ = some S ∧
      S.leak = mergeShows plat self p keyp rsp0 fp ra len target ∧
      {mfacts} := by
  have hfpA : fp &&& 63#64 = 0#64 := by rw [← hfp]; bv_decide
  have pNotF : ∀ x : BitVec 64, inP (x - rsp0) = true → inF (x - fp) = false := by
    intro x hx; simp only [inP, inF] at hx ⊢; bv_decide
  obtain ⟨⟨s1, lk1⟩, e1, hl1, pc1, ax1, bx1, sp1, bp1, c12, c14, c15, s48, s40, s32, s24, s16, s8, sra, own1, f58, f59, f60, f61, f62, f63, out1⟩ :=
    both (prologue self p keyp rsp0 fp len target flags plat m rax rcx rbx rbp r8 r9 r12 r13 r14 r15 zf cf {X}
        hfp hsp hsp2 hlt hLen hKeyp hFlags hPlat hOwnP hOwnF (fun x hx => gSelf x (by bv_omega)) gP ra hRa)
      (prologue_leak self p keyp rsp0 fp len target flags plat m rax rcx rbx rbp r8 r9 r12 r13 r14 r15 zf cf {X}
        hfp hsp hsp2 hlt hLen hKeyp hFlags hPlat hOwnP hOwnF (fun x hx => gSelf x (by bv_omega)) gP ra hRa)
  simp only at hl1 pc1 ax1 bx1 sp1 bp1 c12 c14 c15 s48 s40 s32 s24 s16 s8 sra own1 f58 f59 f60 f61 f62 f63 out1
  subst lk1
  have P : Places self (self + 9#64) keyp fp := ⟨rfl, hfpA, hW, fun x hx => (gArr x hx).1, fun x hx => (gKey x hx).1,
    fun x hx => (gSelf x hx).1, gKeyArr, gKeySelf⟩
  have H1 : Head self (self + 9#64) keyp fp k0 k1 (flags ||| 4#8) plat s1.mem len es := by
    refine ⟨?_, ?_, ?_, ?_, ?_, own1, f58, f59, f60, f61, f62, f63⟩
    · rw [out1 _ (gSelf _ (by bv_omega)).1 (gSelf _ (by bv_omega)).2]; exact hTag
    · exact quad_congr (fun x hx => out1 x (gSelf x (by bv_omega)).1 (gSelf x (by bv_omega)).2) hLen
    · refine entries_congr es _ (fun x hx => ?_) hE
      have hx' : (x - (self + 9#64)).toNat < 1760 := by rw [shl5] at hx; bv_omega
      exact out1 x (gArr x hx').1 (gArr x hx').2
    · exact vec_congr (fun x hx => out1 x (gKey x (by bv_omega)).1 (gKey x (by bv_omega)).2) hK0
    · exact vec_congr (fun x hx => out1 x (gKey x (by bv_omega)).1 (gKey x (by bv_omega)).2) hK1
  obtain ⟨a1, b1, d1, bx1v, sp1v, bp1v, si1, di1, r81, r91, r121, r131, r141, r151, zf1, cf1, {", ".join(ys.split())}, m1, pcv⟩ := s1
  simp only at pc1 ax1 bx1 sp1 bp1 c12 c14 c15 s48 s40 s32 s24 s16 s8 sra own1 out1 H1
  subst pcv a1 bx1v sp1v bp1v r121 r141 r151
  obtain ⟨⟨s2, lk2⟩, e2, hl2, pc2, bx2, sp2, bp2, d12, d14, q2, E2, tag2, out2⟩ :=
    loopL self (self + 9#64) keyp fp k0 k1 (flags ||| 4#8) plat P (len - target).toNat es len (len - target) m1
      b1 d1 (rsp0 + {N(8)}) si1 di1 r81 r91 r131 zf1 cf1 {ys}
      (by bv_omega) (by bv_omega) hlen hmax rfl H1
  simp only at hl2 pc2 bx2 sp2 bp2 d12 d14 q2 E2 tag2 out2
  subst lk2
  obtain ⟨a2, b2, d2, bx2v, sp2v, bp2v, si2, di2, r82, r92, r122, r132, r142, r152, zf2, cf2,
    z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15, m2, pc2v⟩ := s2
  simp only at pc2 bx2 sp2 bp2 d12 d14 q2 E2 tag2 out2
  subst pc2v bp2v
  have keep : ∀ x : BitVec 64, inP (x - rsp0) = true → m2 x = m1 x := by
    intro x hx
    refine out2 x (pNotF x hx) (Nat.le_of_not_lt (fun h => ?_)) (Nat.le_of_not_lt (fun h => ?_))
    · have := (gArr x h).2; rw [hx] at this; exact absurd this (by decide)
    · have := (gSelf x h).2; rw [hx] at this; exact absurd this (by decide)
  have rd : ∀ (c v : BitVec 64), (c + 48#64).ult 49#64 = true → m1.read (rsp0 + c) 64 = some v → m2.read (rsp0 + c) 64 = some v := by
    intro c v hc hv
    rw [read_congr (m := m1) _ (fun x hx => keep x (by
      have h8 : x - (rsp0 + c) < 8#64 := BitVec.lt_def.mpr (by simpa using hx)
      simp only [inP]; bv_decide))]
    exact hv
  obtain ⟨⟨s3, lk3⟩, e3, hl3, pc3, sp3, bx3, bp3, f12, f13, f14, f15, mem3⟩ :=
    both (epilogue rsp0 m2 rbx r12 r13 r14 r15 rbp ra a2 b2 d2 bx2v sp2v si2 di2 r82 r92 r122 r132 r142 r152 zf2 cf2
        z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15
        (rd _ _ (by decide) s48) (rd _ _ (by decide) s40) (rd _ _ (by decide) s32) (rd _ _ (by decide) s24) (rd _ _ (by decide) s16)
        (rd _ _ (by decide) s8) (rd _ _ (by decide) sra))
      (epilogue_leak rsp0 m2 rbx r12 r13 r14 r15 rbp ra a2 b2 d2 bx2v sp2v si2 di2 r82 r92 r122 r132 r142 r152 zf2 cf2
        z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15
        (rd _ _ (by decide) s48) (rd _ _ (by decide) s40) (rd _ _ (by decide) s32) (rd _ _ (by decide) s24) (rd _ _ (by decide) s16)
        (rd _ _ (by decide) s8) (rd _ _ (by decide) sra))
  simp only at hl3 pc3 sp3 bx3 bp3 f12 f13 f14 f15 mem3
  subst lk3
  have hBC := stepsL_chain Code.prog ((len - target).toNat * turnK plat) 8 _ _ _ _ e2 e3
  have hABC := stepsL_chain Code.prog 24 ((len - target).toNat * turnK plat + 8) _ _ _ _ e1 hBC
  have eT : len - (len - target) = target := by bv_decide
  refine ⟨_, hABC, ?_, pc3, sp3, bx3, bp3, f12, f13, f14, f15, ?_, ?_, ?_, ?_⟩
  · simp only [mergeShows, List.append_assoc]
  · show Quad s3.mem _ _; rw [mem3, ← eT]; exact q2
  · show Entries s3.mem _ _; rw [mem3]; rw [eT] at E2; exact E2
  · show s3.mem _ = _; rw [mem3]; exact tag2
  · intro x hF hP hA hS
    show s3.mem x = m x
    rw [mem3, out2 x hF hA hS, out1 x hF hP]

#print axioms merge_whole
'''
out = "import MergeTrace\nopen X86\n\nnamespace MergeCode\n\n/-! `merge`'s loop and the whole function, with the observer. Written by allgen.py. -/\n" + turnL + loopL + whole + "\nend MergeCode\n"
(here / "MergeAll.lean").write_text(out)
print("wrote MergeAll.lean")
