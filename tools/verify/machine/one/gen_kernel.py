"""Write the proof of one one-block compression kernel on Machine.lean: SseProof.lean or AvxProof.lean.

The proof's shape is the same for both: a round's instructions are the specification's round
(bv_decide), the instructions between rounds permute the message, the first instructions load
the rows, the last store the result and return; then the seven rounds are composed."""
import sys
from pathlib import Path

which = sys.argv[1]
P = dict(
    Sse=dict(base=0x20000, head=0x6D, after=0x147, body=46, perm=19, start=24, rot=True, kernel="blake3_servil_compress_in_place_sse41",
             lenhyp="(hlen : s.rdx = len.setWidth 64)", lenarg="(len : BitVec 32) ", lenuse="len ", len="len", flags="s.r8.setWidth 32",
             lendoc="the block's length in RDX (its upper half clear), the counter in RCX and the flags in R8's low half"),
    Avx=dict(base=0x30000, head=0x64, after=0x11A, body=34, perm=16, start=21, rot=False, kernel="blake3_servil_compress_in_place_avx512",
             lenhyp="", lenarg="", lenuse="", len="(s.rdx.setWidth 8).setWidth 32", flags="(s.r8.setWidth 8).setWidth 32",
             lendoc="the block's length in DL, the counter in RCX and the flags in R8B"),
)[which]
base, head, after = P["base"], P["base"] + P["head"], P["base"] + P["after"]
B, PM, ST = P["body"], P["perm"], P["start"]
total = ST + 6 * (B + PM) + (B + 7)
G = "rax rcx rdx rbx rsp rbp rsi rdi r8 r9 r12 r13 r14 r15".split()
pat = ", ".join(G) + ", zf, cf, " + ", ".join(f"x{i}" for i in range(16)) + ", mem, pc"
de = f"obtain ⟨{pat}⟩ := s"
vs = " ".join(f"v{i}" for i in range(16)); ms = " ".join(f"m{i}" for i in range(16))
vv = "#v[" + ", ".join(f"v{i}" for i in range(16)) + "]"; mv = "#v[" + ", ".join(f"m{i}" for i in range(16)) + "]"
idx = lambda v: " ".join(f"{v}[{i}]" for i in range(16))
rot = P["rot"]
rothyp = " (h14 : s.x14 = ROT8) (h15 : s.x15 = ROT16)" if rot else ""
rotsimp = " h14 h15" if rot else ""
rotargs = " h14 h15" if rot else ""
same9 = "⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩"
iters = ""
for n, k in enumerate([7, 6, 5, 4, 3, 2]):
    i = n + 2
    iters += f"""  obtain ⟨s{i}, e{i}, H{i}, S{i}⟩ := iter _ _ {k} s{i-1} H{i-1} (by decide)
  have H{i} : Head s{i} _ _ {k-1} := H{i}
  have S{i} := S{i-1}.trans S{i}
"""
rws = ", ".join(f"steps_add, e{i}, Option.bind_some" for i in range(1, 8))
o = f"(specCv (cvWords cv0 cv1) (blockWords b0 b1 b2 b3) s.rcx ({P['len']}) ({P['flags']}))"

t = f'''import Run
import Flat
open X86 Blake3Generic

/-! # `{P["kernel"]}` is the specification's compression function

Written by gen_kernel.py. The theorem at the end is the kernel's contract: what a caller may
take from a call of it. -/

namespace {which}
'''
if rot:
    t += '''
def ROT8 : V := 0x0C0F0E0D080B0A090407060500030201#128
def ROT16 : V := 0x0D0C0F0E09080B0A0504070601000302#128
'''
t += f'''
/-- The state's four rows are the sixteen words of `v`. -/
def Rows (s : State) (v : Vector (BitVec 32) 16) : Prop :=
  s.x0 = mk4 v[0] v[1] v[2] v[3] ∧ s.x1 = mk4 v[4] v[5] v[6] v[7] ∧ s.x2 = mk4 v[8] v[9] v[10] v[11] ∧ s.x3 = mk4 v[12] v[13] v[14] v[15]

/-- The message words where the round's instructions expect them. -/
def Msgs (s : State) (m : Vector (BitVec 32) 16) : Prop :=
  s.x4 = mk4 m[0] m[2] m[4] m[6] ∧ s.x5 = mk4 m[1] m[3] m[5] m[7] ∧ s.x6 = mk4 m[14] m[8] m[10] m[12] ∧ s.x7 = mk4 m[15] m[9] m[11] m[13]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- **A round.** The {B} instructions from the loop's head are the specification's round on the rows. -/
theorem body ({vs} {ms} : BitVec 32) (s : State) (hpc : s.pc = 0x{head:X})
    (hv : Rows s {vv}) (hm : Msgs s {mv}){rothyp} :
    ∃ s', steps Code.prog {B} s = some s' ∧ s'.pc = 0x{after:X} ∧ Rows s' (rnd {vv} {mv}) ∧
      Msgs s' {mv} ∧ Same s s' ∧ s'.x14 = s.x14 ∧ s'.x15 = s.x15 ∧ s'.rax = s.rax := by
  {de}
  obtain ⟨hv0, hv1, hv2, hv3⟩ := hv
  obtain ⟨hm0, hm1, hm2, hm3⟩ := hm
  simp only at hpc hv0 hv1 hv2 hv3 hm0 hm1 hm2 hm3{rotsimp}
  subst hpc hv0 hv1 hv2 hv3 hm0 hm1 hm2 hm3{rotsimp}
  run_code []
  refine ⟨_, rfl, rfl, ⟨?_, ?_, ?_, ?_⟩, ⟨rfl, rfl, rfl, rfl⟩, {same9}, rfl, rfl, rfl⟩
  all_goals (eval_spec; {"simp only [ROT8, ROT16]; " if rot else ""}open_ops; bv_decide)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- **Between rounds.** The {PM} instructions after a round that is not the last count it and
permute the message words as the specification does. -/
theorem perm ({ms} : BitVec 32) (s : State) (hpc : s.pc = 0x{after:X})
    (hm : Msgs s {mv}) (hal : (s.rax.setWidth 8 - 1 == 0) = false) :
    ∃ s', steps Code.prog {PM} s = some s' ∧ s'.pc = 0x{head:X} ∧ Msgs s' (PERMUTE {mv}) ∧
      (s'.x0 = s.x0 ∧ s'.x1 = s.x1 ∧ s'.x2 = s.x2 ∧ s'.x3 = s.x3) ∧ Same s s' ∧ s'.x14 = s.x14 ∧ s'.x15 = s.x15 ∧
      s'.rax.setWidth 8 = s.rax.setWidth 8 - 1 := by
  {de}
  obtain ⟨hm0, hm1, hm2, hm3⟩ := hm
  simp only at hpc hm0 hm1 hm2 hm3 hal
  subst hpc hm0 hm1 hm2 hm3
  run_code [hal]
  refine ⟨_, rfl, rfl, ⟨?_, ?_, ?_, ?_⟩, ⟨rfl, rfl, rfl, rfl⟩, {same9}, rfl, rfl, ?_⟩
  · eval_spec; open_ops; bv_decide
  · eval_spec; open_ops; bv_decide
  · eval_spec; open_ops; bv_decide
  · eval_spec; open_ops; bv_decide
  · simp only []; bv_decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- **After the last round.** Seven instructions: the two halves are xored, stored where the
chaining value was, and the kernel returns to the address on the stack. -/
theorem finish ({vs} : BitVec 32) (ra : BitVec 64) (s : State) (hpc : s.pc = 0x{after:X})
    (hv : Rows s {vv}) (hal : (s.rax.setWidth 8 - 1 == 0) = true)
    (o0 : Owned16 s.mem (s.rdi + 0)) (o1 : Owned16 s.mem (s.rdi + 16))
    (hret : s.mem.read s.rsp 64 = some ra) (hapart : ∀ x, (x - s.rsp).toNat < 8 → 32 ≤ (x - s.rdi).toNat) :
    ∃ s', steps Code.prog 7 s = some s' ∧ s'.pc = ra.toNat ∧ s'.rsp = s.rsp + 8 ∧
      s'.mem = (s.mem.put128 (s.rdi + 0) (mk4 (v0 ^^^ v8) (v1 ^^^ v9) (v2 ^^^ v10) (v3 ^^^ v11))).put128 (s.rdi + 16)
        (mk4 (v4 ^^^ v12) (v5 ^^^ v13) (v6 ^^^ v14) (v7 ^^^ v15)) ∧
      s'.rbx = s.rbx ∧ s'.rbp = s.rbp ∧ s'.r12 = s.r12 ∧ s'.r13 = s.r13 ∧ s'.r14 = s.r14 ∧ s'.r15 = s.r15 := by
  {de}
  obtain ⟨hv0, hv1, hv2, hv3⟩ := hv
  simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero] at hpc hv0 hv1 hv2 hv3 hal o0 o1 hret hapart
  subst hpc hv0 hv1 hv2 hv3
  have w1 : ∀ (a b : V), (mem.put128 (rdi + 0) a).write128 (rdi + 16) b = some ((mem.put128 (rdi + 0) a).put128 (rdi + 16) b) :=
    fun a b => write_vec (owned16_put128 _ _ _ _ o1) b
  have r1 : ∀ (a b : V), ((mem.put128 (rdi + 0) a).put128 (rdi + 16) b).read rsp 64 = some ra := fun a b => by
    rw [read_congr (m := mem) _ (fun x hx => by
      have := hapart x hx
      rw [put128_other _ _ _ x (by bv_omega), put128_other _ _ _ x (by bv_omega)])]
    exact hret
  have e0 : mk4 v0 v1 v2 v3 ^^^ mk4 v8 v9 v10 v11 = mk4 (v0 ^^^ v8) (v1 ^^^ v9) (v2 ^^^ v10) (v3 ^^^ v11) := by
    open_ops; bv_decide
  have e1 : mk4 v4 v5 v6 v7 ^^^ mk4 v12 v13 v14 v15 = mk4 (v4 ^^^ v12) (v5 ^^^ v13) (v6 ^^^ v14) (v7 ^^^ v15) := by
    open_ops; bv_decide
  run_code [hal, write_vec o0, w1, r1, e0, e1]
  exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- **Before the first round.** {ST} instructions load the chaining value, the IV, the counter,
the length and the flags into the rows, and the block's words where the rounds take them. -/
theorem start (cv0 cv1 b0 b1 b2 b3 : V) {P["lenarg"]}(s : State) (hpc : s.pc = 0x{base:X})
    (hc0 : Vec s.mem (s.rdi + 0) cv0) (hc1 : Vec s.mem (s.rdi + 16) cv1)
    (hb0 : Vec s.mem (s.rsi + 0) b0) (hb1 : Vec s.mem (s.rsi + 16) b1)
    (hb2 : Vec s.mem (s.rsi + 32) b2) (hb3 : Vec s.mem (s.rsi + 48) b3) {P["lenhyp"]} :
    ∃ s', steps Code.prog {ST} s = some s' ∧ s'.pc = 0x{head:X} ∧
      Rows s' #v[dw cv0 0, dw cv0 1, dw cv0 2, dw cv0 3, dw cv1 0, dw cv1 1, dw cv1 2, dw cv1 3,
        0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, s.rcx.setWidth 32, (s.rcx >>> 32).setWidth 32, {P["len"]}, {P["flags"]}] ∧
      Msgs s' #v[dw b0 0, dw b0 1, dw b0 2, dw b0 3, dw b1 0, dw b1 1, dw b1 2, dw b1 3,
        dw b2 0, dw b2 1, dw b2 2, dw b2 3, dw b3 0, dw b3 1, dw b3 2, dw b3 3] ∧
      {"s'.x14 = ROT8 ∧ s'.x15 = ROT16 ∧ " if rot else ""}s'.rax.setWidth 8 = 7 ∧ Same s s' := by
  {de}
  simp only at hpc hc0 hc1 hb0 hb1 hb2 hb3{" hlen" if P["lenhyp"] else ""}
  subst hpc{" hlen" if P["lenhyp"] else ""}
  run_code [read_vec hc0, read_vec hc1, read_vec hb0, read_vec hb1, read_vec hb2, read_vec hb3]
  refine ⟨_, rfl, rfl, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, {"rfl, rfl, " if rot else ""}?_, {same9}⟩
  all_goals (try eval_spec)
  all_goals (try open_ops)
  all_goals bv_decide

theorem body' (v m : Vector (BitVec 32) 16) (s : State) (hpc : s.pc = 0x{head:X})
    (hv : Rows s v) (hm : Msgs s m){rothyp} :
    ∃ s', steps Code.prog {B} s = some s' ∧ s'.pc = 0x{after:X} ∧ Rows s' (rnd v m) ∧ Msgs s' m ∧ Same s s' ∧
      s'.x14 = s.x14 ∧ s'.x15 = s.x15 ∧ s'.rax = s.rax := by
  have h := body {idx("v")} {idx("m")} s hpc (by rw [eta16]; exact hv) (by rw [eta16]; exact hm){rotargs}
  rwa [eta16 v, eta16 m] at h

theorem perm' (m : Vector (BitVec 32) 16) (s : State) (hpc : s.pc = 0x{after:X})
    (hm : Msgs s m) (hal : (s.rax.setWidth 8 - 1 == 0) = false) :
    ∃ s', steps Code.prog {PM} s = some s' ∧ s'.pc = 0x{head:X} ∧ Msgs s' (PERMUTE m) ∧
      (s'.x0 = s.x0 ∧ s'.x1 = s.x1 ∧ s'.x2 = s.x2 ∧ s'.x3 = s.x3) ∧ Same s s' ∧ s'.x14 = s.x14 ∧ s'.x15 = s.x15 ∧
      s'.rax.setWidth 8 = s.rax.setWidth 8 - 1 := by
  have h := perm {idx("m")} s hpc (by rw [eta16]; exact hm) hal
  rwa [eta16 m] at h

theorem finish' (w : Vector (BitVec 32) 16) (ra : BitVec 64) (s : State) (hpc : s.pc = 0x{after:X})
    (hv : Rows s w) (hal : (s.rax.setWidth 8 - 1 == 0) = true)
    (o0 : Owned16 s.mem (s.rdi + 0)) (o1 : Owned16 s.mem (s.rdi + 16))
    (hret : s.mem.read s.rsp 64 = some ra) (hapart : ∀ x, (x - s.rsp).toNat < 8 → 32 ≤ (x - s.rdi).toNat) :
    ∃ s', steps Code.prog 7 s = some s' ∧ s'.pc = ra.toNat ∧ s'.rsp = s.rsp + 8 ∧
      s'.mem = (s.mem.put128 (s.rdi + 0) (mk4 (w[0] ^^^ w[8]) (w[1] ^^^ w[9]) (w[2] ^^^ w[10]) (w[3] ^^^ w[11]))).put128
        (s.rdi + 16) (mk4 (w[4] ^^^ w[12]) (w[5] ^^^ w[13]) (w[6] ^^^ w[14]) (w[7] ^^^ w[15])) ∧
      s'.rbx = s.rbx ∧ s'.rbp = s.rbp ∧ s'.r12 = s.r12 ∧ s'.r13 = s.r13 ∧ s'.r14 = s.r14 ∧ s'.r15 = s.r15 :=
  finish {idx("w")} ra s hpc (by rw [eta16]; exact hv) hal o0 o1 hret hapart

/-- What holds at the loop's head: the rows, the message, the rounds left in AL{", the two masks" if rot else ""}. -/
structure Head (s : State) (v m : Vector (BitVec 32) 16) (k : BitVec 8) : Prop where
  pc : s.pc = 0x{head:X}
  rows : Rows s v
  msgs : Msgs s m
  al : s.rax.setWidth 8 = k
'''
if rot:
    t += "  x14 : s.x14 = ROT8\n  x15 : s.x15 = ROT16\n"
t += f'''
/-- A round that is not the last, and the permutation after it: {B + PM} instructions. -/
theorem iter (v m : Vector (BitVec 32) 16) (k : BitVec 8) (s : State) (h : Head s v m k) (hk : (k - 1 == 0) = false) :
    ∃ s', steps Code.prog {B + PM} s = some s' ∧ Head s' (rnd v m) (PERMUTE m) (k - 1) ∧ Same s s' := by
  obtain ⟨s1, e1, pc1, r1, m1, S1, a14, a15, ax1⟩ := body' v m s h.pc h.rows h.msgs{" h.x14 h.x15" if rot else ""}
  obtain ⟨s2, e2, pc2, m2, ⟨q0, q1, q2, q3⟩, S2, b14, b15, ax2⟩ := perm' m s1 pc1 m1 (by rw [ax1, h.al]; exact hk)
  obtain ⟨c0, c1, c2, c3⟩ := r1
  refine ⟨s2, ?_, ⟨pc2, ⟨by rw [q0, c0], by rw [q1, c1], by rw [q2, c2], by rw [q3, c3]⟩, m2, by rw [ax2, ax1, h.al]{", by rw [b14, a14, h.x14], by rw [b15, a15, h.x15]" if rot else ""}⟩, S1.trans S2⟩
  rw [show {B + PM} = {B} + {PM} from rfl, steps_add, e1, Option.bind_some, e2]

/-- The last round and the return: {B + 7} instructions. -/
theorem last (v m : Vector (BitVec 32) 16) (ra : BitVec 64) (s : State) (h : Head s v m 1)
    (o0 : Owned16 s.mem (s.rdi + 0)) (o1 : Owned16 s.mem (s.rdi + 16))
    (hret : s.mem.read s.rsp 64 = some ra) (hapart : ∀ x, (x - s.rsp).toNat < 8 → 32 ≤ (x - s.rdi).toNat) :
    ∃ s', steps Code.prog {B + 7} s = some s' ∧ s'.pc = ra.toNat ∧ s'.rsp = s.rsp + 8 ∧
      s'.mem = (s.mem.put128 (s.rdi + 0) (mk4 ((rnd v m)[0] ^^^ (rnd v m)[8]) ((rnd v m)[1] ^^^ (rnd v m)[9])
        ((rnd v m)[2] ^^^ (rnd v m)[10]) ((rnd v m)[3] ^^^ (rnd v m)[11]))).put128 (s.rdi + 16)
        (mk4 ((rnd v m)[4] ^^^ (rnd v m)[12]) ((rnd v m)[5] ^^^ (rnd v m)[13]) ((rnd v m)[6] ^^^ (rnd v m)[14])
          ((rnd v m)[7] ^^^ (rnd v m)[15])) ∧
      s'.rbx = s.rbx ∧ s'.rbp = s.rbp ∧ s'.r12 = s.r12 ∧ s'.r13 = s.r13 ∧ s'.r14 = s.r14 ∧ s'.r15 = s.r15 := by
  obtain ⟨s1, e1, pc1, r1, m1, ⟨kbx, ksp, kbp, kdi, k12, k13, k14, k15, kmem⟩, _, _, ax1⟩ :=
    body' v m s h.pc h.rows h.msgs{" h.x14 h.x15" if rot else ""}
  obtain ⟨s2, e2, pc2, sp2, mem2, bx2, bp2, c12, c13, c14, c15⟩ := finish' (rnd v m) ra s1 pc1 r1 (by rw [ax1, h.al]; rfl)
    (by rw [kmem, kdi]; exact o0) (by rw [kmem, kdi]; exact o1) (by rw [kmem, ksp]; exact hret) (by rw [ksp, kdi]; exact hapart)
  refine ⟨s2, ?_, pc2, by rw [sp2, ksp], by rw [mem2, kmem, kdi], by rw [bx2, kbx], by rw [bp2, kbp], by rw [c12, k12],
    by rw [c13, k13], by rw [c14, k14], by rw [c15, k15]⟩
  rw [show {B + 7} = {B} + 7 from rfl, steps_add, e1, Option.bind_some, e2]

set_option maxRecDepth 1000000 in
/-- **The contract of `{P["kernel"]}`.** Called with a chaining value at RDI, a block at RSI,
{P["lendoc"]}, and a return address on the stack that is not in the
chaining value's 32 bytes: its {total} instructions run to that address with the stack pointer
popped, and memory is what it was but for the 32 bytes at RDI, which hold the first eight words
of the specification's `BLAKE3_COMPRESS` (sections 2.2 to 3.3 of C2SP's BLAKE3, `Generic.lean`,
at 32-bit words). RBX, RBP and R12 to R15 are as they were. -/
theorem contract (cv0 cv1 b0 b1 b2 b3 : V) {P["lenarg"]}(ra : BitVec 64) (s : State) (hpc : s.pc = 0x{base:X})
    (hc0 : Vec s.mem (s.rdi + 0) cv0) (hc1 : Vec s.mem (s.rdi + 16) cv1)
    (hb0 : Vec s.mem (s.rsi + 0) b0) (hb1 : Vec s.mem (s.rsi + 16) b1)
    (hb2 : Vec s.mem (s.rsi + 32) b2) (hb3 : Vec s.mem (s.rsi + 48) b3) {P["lenhyp"]}
    (hret : s.mem.read s.rsp 64 = some ra) (hapart : ∀ x, (x - s.rsp).toNat < 8 → 32 ≤ (x - s.rdi).toNat) :
    ∃ s', steps Code.prog {total} s = some s' ∧ s'.pc = ra.toNat ∧ s'.rsp = s.rsp + 8 ∧
      s'.mem = (s.mem.put128 (s.rdi + 0) (mk4 {o}[0] {o}[1]
          {o}[2] {o}[3])).put128 (s.rdi + 16)
        (mk4 {o}[4] {o}[5]
          {o}[6] {o}[7]) ∧
      s'.rbx = s.rbx ∧ s'.rbp = s.rbp ∧ s'.r12 = s.r12 ∧ s'.r13 = s.r13 ∧ s'.r14 = s.r14 ∧ s'.r15 = s.r15 := by
  obtain ⟨s1, e1, pc1, r1, m1, {"x14, x15, " if rot else ""}al1, S1⟩ := start cv0 cv1 b0 b1 b2 b3 {P["lenuse"]}s hpc hc0 hc1 hb0 hb1 hb2 hb3{" hlen" if P["lenhyp"] else ""}
  have H1 : Head s1 _ _ 7 := ⟨pc1, r1, m1, al1{", x14, x15" if rot else ""}⟩
{iters}  obtain ⟨kbx, ksp, kbp, kdi, k12, k13, k14, k15, kmem⟩ := S7
  obtain ⟨s8, e8, pc8, sp8, mem8, bx8, bp8, c12, c13, c14, c15⟩ := last _ _ ra s7 H7
    (by rw [kmem, kdi]; exact vec_owned hc0) (by rw [kmem, kdi]; exact vec_owned hc1) (by rw [kmem, ksp]; exact hret)
    (by rw [ksp, kdi]; exact hapart)
  refine ⟨s8, ?_, pc8, by rw [sp8, ksp], ?_, by rw [bx8, kbx], by rw [bp8, kbp], by rw [c12, k12], by rw [c13, k13],
    by rw [c14, k14], by rw [c15, k15]⟩
  · rw [show {total} = {ST} + ({B + PM} + ({B + PM} + ({B + PM} + ({B + PM} + ({B + PM} + ({B + PM} + {B + 7})))))) from rfl, {rws}, e8]
  · rw [mem8, kmem, kdi, spec_eq, low8_0, low8_1, low8_2, low8_3, low8_4, low8_5, low8_6, low8_7]
    rfl

end {which}
'''
Path(f"{which}Proof.lean").write_text(t)
print(which, "total", total)
