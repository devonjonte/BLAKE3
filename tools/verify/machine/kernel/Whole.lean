import Chain
open Simd Flat Blake3Generic

/-! # The whole kernel: `blake3_servil_compress_in_place_sse41` is the specification's compression -/

theorem eta16 (v : Vector (BitVec 32) 16) : #v[v[0], v[1], v[2], v[3], v[4], v[5], v[6], v[7], v[8], v[9], v[10], v[11], v[12], v[13], v[14], v[15]] = v := by
  ext i hi
  match i, hi with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | 6, _ => rfl
  | 7, _ => rfl
  | 8, _ => rfl
  | 9, _ => rfl
  | 10, _ => rfl
  | 11, _ => rfl
  | 12, _ => rfl
  | 13, _ => rfl
  | 14, _ => rfl
  | 15, _ => rfl
  | n + 16, h => exact absurd h (by omega)

theorem steps_add (prog : Nat → Option (Instr × Nat)) (a b : Nat) (s : State) :
    steps prog (a + b) s = (steps prog a s).bind (steps prog b) := by
  induction a generalizing s with
  | zero => simp [steps]
  | succ a ih =>
    rw [Nat.add_right_comm]
    simp only [steps]
    cases prog s.pc with
    | none => rfl
    | some x =>
      obtain ⟨i, next⟩ := x
      simp only []
      cases step i next s with
      | none => rfl
      | some s1 => simp only [Option.bind_some, ih]

theorem body' (v m : Vector (BitVec 32) 16) (s : State) (hpc : s.pc = 0x262D)
    (hv : Rows s v) (hm : Msgs s m) (h14 : s.x14 = ROT8) (h15 : s.x15 = ROT16) :
    ∃ s', steps Code.prog 46 s = some s' ∧ s'.pc = 0x2707 ∧ Rows s' (rnd v m) ∧ Msgs s' m ∧ Kept s s' ∧ s'.rax = s.rax := by
  have h := body v[0] v[1] v[2] v[3] v[4] v[5] v[6] v[7] v[8] v[9] v[10] v[11] v[12] v[13] v[14] v[15] m[0] m[1] m[2] m[3] m[4] m[5] m[6] m[7] m[8] m[9] m[10] m[11] m[12] m[13] m[14] m[15] s hpc (by rw [eta16]; exact hv) (by rw [eta16]; exact hm) h14 h15
  rwa [eta16 v, eta16 m] at h

theorem perm' (m : Vector (BitVec 32) 16) (s : State) (hpc : s.pc = 0x2707)
    (hm : Msgs s m) (hal : (s.rax.setWidth 8 - 1 == 0) = false) :
    ∃ s', steps Code.prog 19 s = some s' ∧ s'.pc = 0x262D ∧ Msgs s' (PERMUTE m) ∧
      (s'.x0 = s.x0 ∧ s'.x1 = s.x1 ∧ s'.x2 = s.x2 ∧ s'.x3 = s.x3) ∧ Kept s s' ∧
      s'.rax.setWidth 8 = s.rax.setWidth 8 - 1 := by
  have h := perm m[0] m[1] m[2] m[3] m[4] m[5] m[6] m[7] m[8] m[9] m[10] m[11] m[12] m[13] m[14] m[15] s hpc (by rw [eta16]; exact hm) hal
  rwa [eta16 m] at h

theorem finish' (w : Vector (BitVec 32) 16) (s : State) (hpc : s.pc = 0x2707)
    (hv : Rows s w) (hal : (s.rax.setWidth 8 - 1 == 0) = true)
    (h0 : (s.mem (s.rdi + 0)).isSome) (h1 : (s.mem (s.rdi + 16)).isSome) :
    ∃ s', steps Code.prog 7 s = some s' ∧ s'.pc = s.ra ∧ s'.rsp = s.rsp + 8 ∧
      s'.mem (s.rdi + 0) = some (mk4 (w[0] ^^^ w[8]) (w[1] ^^^ w[9]) (w[2] ^^^ w[10]) (w[3] ^^^ w[11])) ∧
      s'.mem (s.rdi + 16) = some (mk4 (w[4] ^^^ w[12]) (w[5] ^^^ w[13]) (w[6] ^^^ w[14]) (w[7] ^^^ w[15])) ∧
      ∀ a, a ≠ s.rdi + 0 → a ≠ s.rdi + 16 → s'.mem a = s.mem a :=
  finish w[0] w[1] w[2] w[3] w[4] w[5] w[6] w[7] w[8] w[9] w[10] w[11] w[12] w[13] w[14] w[15] s hpc (by rw [eta16]; exact hv) hal h0 h1

/-- What holds at the loop's head: the rows, the message, the two masks, the rounds left in AL. -/
structure Head (s : State) (v m : Vector (BitVec 32) 16) (k : BitVec 8) : Prop where
  pc : s.pc = 0x262D
  rows : Rows s v
  msgs : Msgs s m
  x14 : s.x14 = ROT8
  x15 : s.x15 = ROT16
  al : s.rax.setWidth 8 = k

/-- A round that is not the last, and the permutation after it: 65 instructions. -/
theorem iter (v m : Vector (BitVec 32) 16) (k : BitVec 8) (s : State) (h : Head s v m k) (hk : (k - 1 == 0) = false) :
    ∃ s', steps Code.prog 65 s = some s' ∧ Head s' (rnd v m) (PERMUTE m) (k - 1) ∧
      s'.rdi = s.rdi ∧ s'.rsp = s.rsp ∧ s'.mem = s.mem ∧ s'.ra = s.ra := by
  obtain ⟨s1, e1, pc1, r1, m1, ⟨kdi, ksp, kmem, kra, k14, k15⟩, ax1⟩ := body' v m s h.pc h.rows h.msgs h.x14 h.x15
  obtain ⟨s2, e2, pc2, m2, ⟨q0, q1, q2, q3⟩, ⟨ldi, lsp, lmem, lra, l14, l15⟩, ax2⟩ :=
    perm' m s1 pc1 m1 (by rw [ax1, h.al]; exact hk)
  refine ⟨s2, ?_, ⟨pc2, ?_, m2, by rw [l14, k14, h.x14], by rw [l15, k15, h.x15], by rw [ax2, ax1, h.al]⟩,
    by rw [ldi, kdi], by rw [lsp, ksp], by rw [lmem, kmem], by rw [lra, kra]⟩
  · rw [show 65 = 46 + 19 from rfl, steps_add, e1, Option.bind_some, e2]
  · obtain ⟨a0, a1, a2, a3⟩ := r1
    exact ⟨by rw [q0, a0], by rw [q1, a1], by rw [q2, a2], by rw [q3, a3]⟩

/-- The last round and the return: 53 instructions. -/
theorem last (v m : Vector (BitVec 32) 16) (s : State) (h : Head s v m 1)
    (h0 : (s.mem (s.rdi + 0)).isSome) (h1 : (s.mem (s.rdi + 16)).isSome) :
    ∃ s', steps Code.prog 53 s = some s' ∧ s'.pc = s.ra ∧ s'.rsp = s.rsp + 8 ∧
      s'.mem (s.rdi + 0) = some (mk4 ((rnd v m)[0] ^^^ (rnd v m)[8]) ((rnd v m)[1] ^^^ (rnd v m)[9])
        ((rnd v m)[2] ^^^ (rnd v m)[10]) ((rnd v m)[3] ^^^ (rnd v m)[11])) ∧
      s'.mem (s.rdi + 16) = some (mk4 ((rnd v m)[4] ^^^ (rnd v m)[12]) ((rnd v m)[5] ^^^ (rnd v m)[13])
        ((rnd v m)[6] ^^^ (rnd v m)[14]) ((rnd v m)[7] ^^^ (rnd v m)[15])) ∧
      ∀ a, a ≠ s.rdi + 0 → a ≠ s.rdi + 16 → s'.mem a = s.mem a := by
  obtain ⟨s1, e1, pc1, r1, m1, ⟨kdi, ksp, kmem, kra, k14, k15⟩, ax1⟩ := body' v m s h.pc h.rows h.msgs h.x14 h.x15
  obtain ⟨s2, e2, pc2, sp2, o0, o1, fr⟩ := finish' (rnd v m) s1 pc1 r1 (by rw [ax1, h.al]; rfl)
    (by rw [kmem, kdi]; exact h0) (by rw [kmem, kdi]; exact h1)
  refine ⟨s2, ?_, by rw [pc2, kra], by rw [sp2, ksp], by rw [← kdi]; exact o0, by rw [← kdi]; exact o1, ?_⟩
  · rw [show 53 = 46 + 7 from rfl, steps_add, e1, Option.bind_some, e2]
  · intro a ha0 ha1
    rw [fr a (by rw [kdi]; exact ha0) (by rw [kdi]; exact ha1), kmem]
