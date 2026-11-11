import Scan
open X86

/-! # `scan2`: a function that calls a proved one

`scan2` (two.rs) scans two slices, the second seeded by the first's fold. Its 15 instructions
save three registers, call `scan`, and jump to `scan` again. The proof runs those 15
instructions and takes `scan`'s two runs from `scan_is_the_scan`: the callee's theorem is its
contract, and its code is not looked at again. -/

theorem sub8_add8 (a : BitVec 64) : a - 8 + 8 = a := by bv_decide

theorem scan_length (a : BitVec 32) (ws : List (BitVec 32)) : (Spec.scan a ws).length = ws.length := by
  induction ws generalizing a with
  | nil => rfl
  | cons w ws ih => simp [Spec.scan, ih]

/-- The memory when `scan` is first entered: the caller's three saved registers and the return address. -/
abbrev frame4 (m : Mem) (rsp rbp r14 rbx : BitVec 64) : Mem :=
  (((m.put64 (rsp - 8) rbp).put64 (rsp - 8 - 8) r14).put64 (rsp - 8 - 8 - 8) rbx).put64 (rsp - 8 - 8 - 8 - 8)
    (BitVec.ofNat 64 0x103A)

/-- What a call of `scan2` lets an observer see: the two slices' addresses and lengths and the stack pointer decide it. -/
def scan2Leak (p1 p2 sp ra : BitVec 64) (n1 n2 : Nat) (seen : List Obs) : List Obs :=
  scanLeak p2 sp ra n2
    (.addr (sp - 8) :: .addr (sp - 8 - 8) :: .addr (sp - 8 - 8 - 8) ::
      scanLeak p1 (sp - 8 - 8 - 8 - 8) (BitVec.ofNat 64 0x103A) n1
        (.addr (sp - 8 - 8 - 8 - 8) :: .addr (sp - 8 - 8 - 8) :: .addr (sp - 8 - 8) :: .addr (sp - 8) :: seen))

set_option maxRecDepth 100000 in
/-- **The compiled `scan2` scans both slices, the second from the first's fold.** -/
theorem scan2_is_two_scans (ws1 ws2 : List (BitVec 32)) (seed : BitVec 32)
    (rax rcx rdx rbx rsp rbp rsi rdi r8 r14 ra : BitVec 64) (zf cf : Option Bool) (m : Mem) (leak : List Obs)
    (hlen1 : rsi = BitVec.ofNat 64 ws1.length) (hn1 : 4 * ws1.length < 2 ^ 63)
    (hlen2 : rcx = BitVec.ofNat 64 ws2.length) (hn2 : 4 * ws2.length < 2 ^ 63)
    (hseed : r8.setWidth 32 = seed)
    (h1 : Holds m rdi ws1) (h2 : Holds m rdx ws2)
    (hret : m.read rsp 64 = some ra)
    (hs1 : Owned8 m (rsp - 8)) (hs2 : Owned8 m (rsp - 8 - 8)) (hs3 : Owned8 m (rsp - 8 - 8 - 8))
    (hs4 : Owned8 m (rsp - 8 - 8 - 8 - 8)) (hs5 : Owned8 m (rsp - 8 - 8 - 8 - 8 - 8))
    (hapart1 : ∀ x, (x - rdi).toNat < 4 * ws1.length → 48 ≤ (x - (rsp - 40)).toNat)
    (hapart2 : ∀ x, (x - rdx).toNat < 4 * ws2.length → 48 ≤ (x - (rsp - 40)).toNat)
    (hdisj : ∀ x, (x - rdi).toNat < 4 * ws1.length → 4 * ws2.length ≤ (x - rdx).toNat) :
    ∃ k s', steps Code.prog k ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r14, zf, cf, m, 0x1025, leak⟩ = some s' ∧
      s'.pc = ra.toNat ∧ s'.rax.setWidth 32 = Spec.fold (Spec.fold seed ws1) ws2 ∧
      s'.rsp = rsp + 8 ∧ s'.rbx = rbx ∧ s'.rbp = rbp ∧ s'.r14 = r14 ∧
      Holds s'.mem rdi (Spec.scan seed ws1) ∧ Holds s'.mem rdx (Spec.scan (Spec.fold seed ws1) ws2) ∧
      (∀ x, 4 * ws1.length ≤ (x - rdi).toNat → 4 * ws2.length ≤ (x - rdx).toNat → 40 ≤ (x - (rsp - 40)).toNat →
        s'.mem x = m x) ∧
      s'.leak = scan2Leak rdi rdx rsp ra ws1.length ws2.length leak := by
  -- Eight instructions to `scan`'s first: three registers saved, the arguments in place, the call.
  have o2 := owned8_put64 m (rsp - 8 - 8) (rsp - 8) rbp hs2
  have o3 := owned8_put64 _ (rsp - 8 - 8 - 8) (rsp - 8 - 8) r14 (owned8_put64 m _ (rsp - 8) rbp hs3)
  have o4 := owned8_put64 _ (rsp - 8 - 8 - 8 - 8) (rsp - 8 - 8 - 8) rbx
    (owned8_put64 _ _ (rsp - 8 - 8) r14 (owned8_put64 m _ (rsp - 8) rbp hs4))
  have hA : steps Code.prog 8 ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r14, zf, cf, m, 0x1025, leak⟩ =
      some ⟨rax, rcx, r8 &&& 4294967295 &&& 4294967295, rcx, rsp - 8 - 8 - 8 - 8, rsp - 8, rsi, rdi, r8, rdx, zf, cf,
        frame4 m rsp rbp r14 rbx, 0x1000,
        .addr (rsp - 8 - 8 - 8 - 8) :: .addr (rsp - 8 - 8 - 8) :: .addr (rsp - 8 - 8) :: .addr (rsp - 8) :: leak⟩ := by
    run_code [write_quad hs1, write_quad o2, write_quad o3, write_quad o4]
  -- The first scan, by `scan`'s theorem.
  have outside1 : ∀ x, (x - rdi).toNat < 4 * ws1.length → frame4 m rsp rbp r14 rbx x = m x := fun x hx => by
    have := hapart1 x hx
    unfold frame4
    rw [put64_other _ _ _ x (by bv_omega), put64_other _ _ _ x (by bv_omega), put64_other _ _ _ x (by bv_omega),
      put64_other _ _ _ x (by bv_omega)]
  obtain ⟨k1, sB, eB, pcB, axB, spB, bxB, bpB, r14B, holdsB, frB, lkB⟩ :=
    scan_is_the_scan ws1 seed rax rcx (r8 &&& 4294967295 &&& 4294967295) rcx (rsp - 8 - 8 - 8 - 8) (rsp - 8) rsi rdi r8 rdx
      (BitVec.ofNat 64 0x103A) zf cf (frame4 m rsp rbp r14 rbx) _ hlen1 hn1 (by rw [← hseed]; bv_decide)
      (holds_congr ws1 rdi hn1 outside1 h1) (read_put64 _ _ _)
      (owned8_put64 _ _ _ _ (owned8_put64 _ _ _ _ (owned8_put64 _ _ _ _ (owned8_put64 _ _ _ _ hs5))))
      (fun x hx => by have := hapart1 x hx; bv_omega)
  have pcB : sB.pc = 0x103A := pcB
  -- What the first scan left of the caller's frame: everything.
  have kept : ∀ x, (x - (rsp - 8 - 8 - 8)).toNat < 32 → sB.mem x = frame4 m rsp rbp r14 rbx x := fun x hx =>
    frB x (Nat.le_of_not_lt (fun h => by have := hapart1 x h; bv_omega)) (by bv_omega)
  have pop1 : sB.mem.read (rsp - 8 - 8 - 8) 64 = some rbx := by
    rw [read_congr _ (fun x hx => kept x (by bv_omega)), read_put64_other _ _ _ _ (fun x hx => by bv_omega), read_put64]
  have pop2 : sB.mem.read (rsp - 8 - 8) 64 = some r14 := by
    rw [read_congr _ (fun x hx => kept x (by bv_omega)), read_put64_other _ _ _ _ (fun x hx => by bv_omega),
      read_put64_other _ _ _ _ (fun x hx => by bv_omega), read_put64]
  have pop3 : sB.mem.read (rsp - 8) 64 = some rbp := by
    rw [read_congr _ (fun x hx => kept x (by bv_omega)), read_put64_other _ _ _ _ (fun x hx => by bv_omega),
      read_put64_other _ _ _ _ (fun x hx => by bv_omega), read_put64_other _ _ _ _ (fun x hx => by bv_omega), read_put64]
  -- Seven more instructions: the second slice's arguments, the registers restored, the jump.
  obtain ⟨raxB, rcxB, rdxB, rbxB, rspB, rbpB, rsiB, rdiB, r8B, r14B', zfB, cfB, mB, pcB', leakB⟩ := sB
  simp only at pcB axB spB bxB bpB r14B holdsB frB lkB kept pop1 pop2 pop3
  subst pcB spB bpB lkB
  subst rbxB r14B'
  have hC : steps Code.prog 7 ⟨raxB, rcxB, rdxB, rcx, rsp - 8 - 8 - 8 - 8 + 8, rsp - 8, rsiB, rdiB, r8B, rdx, zfB, cfB, mB, 0x103A,
        scanLeak rdi (rsp - 8 - 8 - 8 - 8) (BitVec.ofNat 64 0x103A) ws1.length
          (.addr (rsp - 8 - 8 - 8 - 8) :: .addr (rsp - 8 - 8 - 8) :: .addr (rsp - 8 - 8) :: .addr (rsp - 8) :: leak)⟩ =
      some ⟨raxB, rcxB, raxB &&& 4294967295 &&& 4294967295, rbx, rsp, rbp, rcx, rdx, r8B, r14, zfB, cfB, mB, 0x1000,
        .addr (rsp - 8) :: .addr (rsp - 8 - 8) :: .addr (rsp - 8 - 8 - 8) ::
          scanLeak rdi (rsp - 8 - 8 - 8 - 8) (BitVec.ofNat 64 0x103A) ws1.length
            (.addr (rsp - 8 - 8 - 8 - 8) :: .addr (rsp - 8 - 8 - 8) :: .addr (rsp - 8 - 8) :: .addr (rsp - 8) :: leak)⟩ := by
    run_code [sub8_add8, pop1, pop2, pop3]
  -- The second scan, by `scan`'s theorem again; it returns to `scan2`'s caller.
  have after1 : ∀ x, 4 * ws1.length ≤ (x - rdi).toNat → 40 ≤ (x - (rsp - 40)).toNat → mB x = m x := fun x hx h40 => by
    rw [frB x hx (by bv_omega)]
    unfold frame4
    rw [put64_other _ _ _ x (by bv_omega), put64_other _ _ _ x (by bv_omega),
      put64_other _ _ _ x (by bv_omega), put64_other _ _ _ x (by bv_omega)]
  have in2 : ∀ x, (x - rdx).toNat < 4 * ws2.length → mB x = m x := fun x hx =>
    after1 x (Nat.le_of_not_lt (fun h => by have := hdisj x h; omega)) (by have := hapart2 x hx; bv_omega)
  have top : ∀ x, (x - (rsp - 8)).toNat < 16 → mB x = frame4 m rsp rbp r14 rbx x := fun x hx => kept x (by bv_omega)
  obtain ⟨k2, sD, eD, pcD, axD, spD, bxD, bpD, r14D, holdsD, frD, lkD⟩ :=
    scan_is_the_scan ws2 (Spec.fold seed ws1) raxB rcxB (raxB &&& 4294967295 &&& 4294967295) rbx rsp rbp rcx rdx r8B r14 ra zfB cfB
      mB _ hlen2 hn2 (by rw [← axB]; bv_decide) (holds_congr ws2 rdx hn2 in2 h2)
      (by rw [read_congr (m := m) _ (fun x hx => by
            rw [top x (by bv_omega)]
            unfold frame4
            rw [put64_other _ _ _ x (by bv_omega), put64_other _ _ _ x (by bv_omega),
              put64_other _ _ _ x (by bv_omega), put64_other _ _ _ x (by bv_omega)])]
          exact hret)
      (owned8_congr _ (fun x hx => top x (by bv_omega))
        (owned8_put64 _ _ _ _ (owned8_put64 _ _ _ _ (owned8_put64 _ _ _ _ (owned8_put64 _ _ _ _ hs1)))))
      (fun x hx => by have := hapart2 x hx; bv_omega)
  refine ⟨8 + (k1 + (7 + k2)), sD, ?_, pcD, axD, spD, bxD, bpD, r14D, ?_, holdsD, ?_, ?_⟩
  · rw [steps_add, hA, Option.bind_some, steps_add, eB, Option.bind_some, steps_add, hC, Option.bind_some, eD]
  · exact holds_congr _ rdi (by rw [scan_length]; exact hn1)
      (fun x hx => frD x (by rw [scan_length] at hx; exact hdisj x hx) (by rw [scan_length] at hx; have := hapart1 x hx; bv_omega))
      holdsB
  · intro x hx1 hx2 h40
    rw [frD x hx2 (by bv_omega), after1 x hx1 h40]
  · rw [lkD]; rfl

#print axioms scan2_is_two_scans
