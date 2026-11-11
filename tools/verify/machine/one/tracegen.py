#!/usr/bin/env python3
"""Write MergeTrace.lean: what a whole turn of merge's loop shows, from MergeTurn.lean's proofs of the
turn (their text up to the last part is reused, so the same facts are at hand) and the parts' traces."""
import re, pathlib
here = pathlib.Path(__file__).resolve().parent
t = (here / "MergeTurn.lean").read_text()
N8 = "18446744073709551608#64"; OL = "((len + 18446744073709551614#64) <<< 5)"
def turn(kind):
    a = t.index(f"theorem turn_{kind} ")
    blk = t[a:]
    i = blk.index(" :\n    ∃ s', steps Code.prog"); j = blk.index(":= by\n", i)
    binders = blk[len(f"theorem turn_{kind} "):i]
    concl = blk[i + 3:j]
    m = re.match(r"\s*∃ s', steps Code\.prog (\(.*?\)) (⟨.*?⟩) = some s' ∧", concl, re.S)
    count, state = m.group(1), m.group(2)
    body = blk[j + 6:]
    cut = body.index("  rw [over_none] at e3\n")
    head = body[:cut]
    # the arguments the proved turn gave to its first and last parts
    pre_args = re.search(rf"    pre_{kind} (self arr.*?)\n  rw \[over_none\] at e1", head, re.S).group(1)
    post_args = re.search(rf"    post_{kind} (self arr.*?)$", head.rstrip("\n"), re.S).group(1)
    K = 362 if kind == "avx" else 467
    P = 12 if kind == "avx" else 13
    ra = "262235#64" if kind == "avx" else "262566#64"
    kern = "avxShows" if kind == "avx" else "sseShows"
    extra = "" if kind == "avx" else ""
    return f'''
/-- What one turn by the {"AVX-512" if kind == "avx" else "SSE4.1"} kernel shows: its last part, the kernel, its first part. -/
noncomputable def turn_{kind}_shows (self arr keyp fp len : BitVec 64) (last : Bool) : List Obs :=
  post_{kind}_shows self arr fp {OL} last ++
    ({kern} (fp + 64#64) (fp + 128#64) (fp + {N8}) {ra} ++ pre_{kind}_shows self arr keyp fp len)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem turn_{kind}_leak {binders} :
    ∃ S, stepsL Code.prog {count} ⟨{state}, []⟩ = some S ∧
      S.leak = turn_{kind}_shows self arr keyp fp len (decide (n - 1#64 = 0#64)) := by
{head}  rw [over_none] at e3
  obtain ⟨SL1, hSL1, hL1⟩ :=
    pre_{kind}_leak {pre_args}
  rw [over_none] at hSL1
  obtain ⟨SLk, hSLk, hLk⟩ := {kern}_spec (fp + 64#64) (fp + 128#64) (fp + {N8}) {ra} S1 k0 k1 l0 l1 r0 r1
    pc1 di1 si1 sp1 hc0 hc1 hb0 hb1 hb2 hb3 hret hapart
  obtain ⟨SL3, hSL3, hL3⟩ :=
    post_{kind}_leak {post_args}
  rw [over_none] at hSL3
  have c1 : SL1.core = S1 := core_of hSL1 e1
  have ck := core_of hSLk e2
  have hA := hSL1; rw [lstate_eq SL1 _ _ c1 hL1] at hA
  have hB := hSLk; rw [lstate_eq SLk _ _ ck hLk] at hB
  have hBC := stepsL_chain Code.prog {K} {P} _ _ _ SL3 hB hSL3
  have hABC := stepsL_chain Code.prog 52 ({K} + {P}) _ _ _ _ hA hBC
  exact ⟨_, hABC, by simp only [turn_{kind}_shows, hL3, List.append_assoc]⟩
'''
out = f'''import MergeParts
open X86

namespace MergeCode

/-! What one whole turn of `merge`'s loop shows. Written by tracegen.py. -/

theorem stepsL_add (prog : Nat → Option (Instr × Nat)) (a b : Nat) (s : LState) :
    stepsL prog (a + b) s = (stepsL prog a s).bind (stepsL prog b) := by
  induction a generalizing s with
  | zero => simp [stepsL]
  | succ a ih =>
    rw [Nat.add_right_comm]
    simp only [stepsL]
    cases prog s.core.pc with
    | none => rfl
    | some x =>
      obtain ⟨i, next⟩ := x
      simp only []
      cases stepL i next s with
      | none => rfl
      | some s1 => simp only [Option.bind_some, ih]

theorem lstate_eq (S : LState) (c : State) (l : List Obs) (h1 : S.core = c) (h2 : S.leak = l) : S = ⟨c, l⟩ := by
  cases S; simp only at h1 h2; subst h1 h2; rfl

/-- The recorded run's state is the model's run's. -/
theorem core_of {{prog : Nat → Option (Instr × Nat)}} {{N : Nat}} {{c : State}} {{l : List Obs}} {{S : LState}} {{s' : State}}
    (hS : stepsL prog N ⟨c, l⟩ = some S) (hs : steps prog N c = some s') : S.core = s' := by
  have h := stepsL_core prog N ⟨c, l⟩
  rw [hS, hs] at h
  exact Option.some.inj h

/-- Two recorded runs, one after the other: the second's trace on top of the first's. -/
theorem stepsL_chain (prog : Nat → Option (Instr × Nat)) (a b : Nat) (c c1 : State) (l1 : List Obs) (S2 : LState)
    (h1 : stepsL prog a ⟨c, []⟩ = some ⟨c1, l1⟩) (h2 : stepsL prog b ⟨c1, []⟩ = some S2) :
    stepsL prog (a + b) ⟨c, []⟩ = some ⟨S2.core, S2.leak ++ l1⟩ := by
  rw [stepsL_add, h1, Option.bind_some]
  have h := stepsL_seen prog b c1 [] l1
  rw [List.nil_append] at h
  rw [h, h2]; rfl

/-- A result proved of the model's run holds of the recorded run's state. -/
theorem both {{prog : Nat → Option (Instr × Nat)}} {{N : Nat}} {{c : State}} {{L : List Obs}} {{P : State → Prop}}
    (hc : ∃ s', steps prog N c = some s' ∧ P s') (hl : ∃ S, stepsL prog N ⟨c, []⟩ = some S ∧ S.leak = L) :
    ∃ S, stepsL prog N ⟨c, []⟩ = some S ∧ S.leak = L ∧ P S.core := by
  obtain ⟨s', hs, hp⟩ := hc
  obtain ⟨S, hS, hL⟩ := hl
  have h := stepsL_core prog N ⟨c, []⟩
  rw [hS, hs] at h
  have e : S.core = s' := Option.some.inj h
  exact ⟨S, hS, hL, by rw [e]; exact hp⟩

/-- What each one-block kernel shows, as a function of the three addresses it is given and its return
address (`Leak.lean` proves there is one). -/
noncomputable def avxShows (rdi rsi rsp ra : BitVec 64) : List Obs :=
  Classical.choose (avx512_kernel_shows_only_addresses rdi rsi rsp ra)
noncomputable def sseShows (rdi rsi rsp ra : BitVec 64) : List Obs :=
  Classical.choose (sse41_kernel_shows_only_addresses rdi rsi rsp ra)
theorem avxShows_spec (rdi rsi rsp ra : BitVec 64) : ∀ (s : State) (cv0 cv1 b0 b1 b2 b3 : V),
    s.pc = 0x30000 → s.rdi = rdi → s.rsi = rsi → s.rsp = rsp →
    Vec s.mem (s.rdi + 0) cv0 → Vec s.mem (s.rdi + 16) cv1 →
    Vec s.mem (s.rsi + 0) b0 → Vec s.mem (s.rsi + 16) b1 → Vec s.mem (s.rsi + 32) b2 → Vec s.mem (s.rsi + 48) b3 →
    s.mem.read s.rsp 64 = some ra → (∀ x, (x - s.rsp).toNat < 8 → 32 ≤ (x - s.rdi).toNat) →
    ∃ S, stepsL Code.prog 362 ⟨s, []⟩ = some S ∧ S.leak = avxShows rdi rsi rsp ra :=
  Classical.choose_spec (avx512_kernel_shows_only_addresses rdi rsi rsp ra)
theorem sseShows_spec (rdi rsi rsp ra : BitVec 64) : ∀ (s : State) (cv0 cv1 b0 b1 b2 b3 : V),
    s.pc = 0x20000 → s.rdi = rdi → s.rsi = rsi → s.rsp = rsp →
    Vec s.mem (s.rdi + 0) cv0 → Vec s.mem (s.rdi + 16) cv1 →
    Vec s.mem (s.rsi + 0) b0 → Vec s.mem (s.rsi + 16) b1 → Vec s.mem (s.rsi + 32) b2 → Vec s.mem (s.rsi + 48) b3 →
    s.mem.read s.rsp 64 = some ra → (∀ x, (x - s.rsp).toNat < 8 → 32 ≤ (x - s.rdi).toNat) →
    ∃ S, stepsL Code.prog 467 ⟨s, []⟩ = some S ∧ S.leak = sseShows rdi rsi rsp ra :=
  Classical.choose_spec (sse41_kernel_shows_only_addresses rdi rsi rsp ra)
{turn("avx")}{turn("sse")}
end MergeCode
'''
(here / "MergeTrace.lean").write_text(out)
print("wrote MergeTrace.lean")
