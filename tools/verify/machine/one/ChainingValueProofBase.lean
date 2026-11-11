import Run
import Flat
import SseProof
import AvxProof
open X86

/-! # `Output::chaining_value`, as rustc compiled it in the core crate

Twenty-nine instructions: the node's key is copied to the stack, its length, counter and flags
are put in the argument registers, the platform's byte chooses the AVX-512 or the SSE4.1
compression kernel, and the kernel's result is copied to where the caller asked. The kernel's
run is taken from its contract (`Avx.contract`, `Sse.contract`): its code is not run again. -/

theorem sub8_add8 (a : BitVec 64) : a - 8 + 8 = a := by bv_decide
theorem len_of (b : BitVec 8) : BitVec.setWidth 32 (BitVec.setWidth 8 (BitVec.setWidth 64 b &&& 255)) = BitVec.setWidth 32 b := by bv_decide
theorem len_of' (b : BitVec 8) : BitVec.setWidth 64 b &&& 255 = BitVec.setWidth 64 (BitVec.setWidth 32 b) := by bv_decide
theorem flags_of (b : BitVec 8) : BitVec.setWidth 32 (BitVec.setWidth 64 b &&& 255) = BitVec.setWidth 32 b := by bv_decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- The first sixteen instructions, on the avx path: the key copied to the stack, the node's
length, counter and flags in the kernel's argument registers, and the call. -/
theorem pre_avx (k0 k1 b0 b1 b2 b3 : V) (len8 fl8 pl8 : BitVec 8) (ctr ra : BitVec 64) (rax rcx rdx rbx rsp rbp rsi rdi r8 r9 r12 r13 r14 r15 : BitVec 64) (zf cf : Option Bool)
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : V) (mem : Mem)
    (hK0 : Vec mem (rsi + 0x40) k0) (hK1 : Vec mem (rsi + 0x50) k1)
    (hB0 : Vec mem (rsi + 0) b0) (hB1 : Vec mem (rsi + 16) b1) (hB2 : Vec mem (rsi + 32) b2) (hB3 : Vec mem (rsi + 48) b3)
    (hLen : mem (rsi + 0x60) = some len8) (hCtr : Quad mem (rsi + 0x68) ctr) (hFl : mem (rsi + 0x70) = some fl8)
    (hPl : mem (rsi + 0x71) = some pl8)
    (oPush : Owned8 mem (rsp - 8)) (oC1 : Owned16 mem (rsp - 8 - 32 + 0x10)) (oC0 : Owned16 mem (rsp - 8 - 32 + 0x0))
    (oCall : Owned8 mem (rsp - 8 - 32 - 8))
    (hsp : rsp &&& 15 = 8) (hsi : rsi &&& 15 = 0)
    (aOS : ∀ x, (x - rsi).toNat < 0x72 → 0x30 ≤ (x - (rsp - 0x30)).toNat)
    (hp : pl8 = 5) :
    ∃ s', steps Code.prog 16 ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r12, r13, r14, r15, zf, cf, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, mem, 0x11000⟩ = some s' ∧ s'.pc = 0x30000 ∧
      s'.rdi = rsp - 0x28 ∧ s'.rsi = rsi ∧ s'.rdx = BitVec.setWidth 64 len8 &&& 255 ∧ s'.rcx = ctr ∧
      s'.r8 = BitVec.setWidth 64 fl8 &&& 255 ∧ s'.rsp = rsp - 0x30 ∧ s'.rbx = rdi ∧
      (s'.rbp = rbp ∧ s'.r12 = r12 ∧ s'.r13 = r13 ∧ s'.r14 = r14 ∧ s'.r15 = r15) ∧
      s'.mem = ((((mem.put64 (rsp - 8) rbx).put128 (rsp - 0x18) k1).put128 (rsp - 0x28) k0).put64 (rsp - 0x30) (BitVec.ofNat 64 0x1103B)) := by
  have rK0 : ∀ v0, (mem.put64 (rsp - 8) v0).read128 (rsi + 0x40) = some k0 := fun v0 => by
    rw [read128_congr (m := mem) _ (fun x hx => by have h := aOS x (by bv_omega); rw [put64_other _ _ _ x (by bv_omega)])]
    exact read_vec hK0
  have rK1 : ∀ v0, (mem.put64 (rsp - 8) v0).read128 (rsi + 0x50) = some k1 := fun v0 => by
    rw [read128_congr (m := mem) _ (fun x hx => by have h := aOS x (by bv_omega); rw [put64_other _ _ _ x (by bv_omega)])]
    exact read_vec hK1
  have rLen : ∀ v0 v1 v2, (((mem.put64 (rsp - 8) v0).put128 (rsp - 8 - 32 + 0x10) v1).put128 (rsp - 8 - 32 + 0x0) v2).read (rsi + 0x60) 8 = some (len8.setWidth 64) := fun v0 v1 v2 =>
    read_byte (by have h := aOS (rsi + 0x60) (by bv_omega); rw [put128_other _ _ _ _ (by bv_omega), put128_other _ _ _ _ (by bv_omega), put64_other _ _ _ _ (by bv_omega)]; exact hLen)
  have rFl : ∀ v0 v1 v2, (((mem.put64 (rsp - 8) v0).put128 (rsp - 8 - 32 + 0x10) v1).put128 (rsp - 8 - 32 + 0x0) v2).read (rsi + 0x70) 8 = some (fl8.setWidth 64) := fun v0 v1 v2 =>
    read_byte (by have h := aOS (rsi + 0x70) (by bv_omega); rw [put128_other _ _ _ _ (by bv_omega), put128_other _ _ _ _ (by bv_omega), put64_other _ _ _ _ (by bv_omega)]; exact hFl)
  have rPl : ∀ v0 v1 v2, (((mem.put64 (rsp - 8) v0).put128 (rsp - 8 - 32 + 0x10) v1).put128 (rsp - 8 - 32 + 0x0) v2).read (rsi + 0x71) 8 = some (pl8.setWidth 64) := fun v0 v1 v2 =>
    read_byte (by have h := aOS (rsi + 0x71) (by bv_omega); rw [put128_other _ _ _ _ (by bv_omega), put128_other _ _ _ _ (by bv_omega), put64_other _ _ _ _ (by bv_omega)]; exact hPl)
  have rCtr : ∀ v0 v1 v2, (((mem.put64 (rsp - 8) v0).put128 (rsp - 8 - 32 + 0x10) v1).put128 (rsp - 8 - 32 + 0x0) v2).read (rsi + 0x68) 64 = some ctr := fun v0 v1 v2 => by
    rw [read_congr (m := mem) _ (fun x hx => by have h := aOS x (by bv_omega); rw [put128_other _ _ _ x (by bv_omega), put128_other _ _ _ x (by bv_omega), put64_other _ _ _ x (by bv_omega)])]
    exact read_quad hCtr
  have a40 : aligned16 (rsi + 0x40) = true := by simp only [aligned16]; bv_decide
  have a50 : aligned16 (rsi + 0x50) = true := by simp only [aligned16]; bv_decide
  have aC1 : aligned16 (rsp - 8 - 32 + 0x10) = true := by simp only [aligned16]; bv_decide
  have aC0 : aligned16 (rsp - 8 - 32 + 0x0) = true := by simp only [aligned16]; bv_decide
  have w1 : ∀ (v0 : BitVec 64) (w : V), (mem.put64 (rsp - 8) v0).write128 (rsp - 8 - 32 + 0x10) w = some ((mem.put64 (rsp - 8) v0).put128 (rsp - 8 - 32 + 0x10) w) :=
    fun v0 w => write_vec (owned16_put64 _ _ _ _ oC1) w
  have w2 : ∀ (v0 : BitVec 64) (v1 w : V), ((mem.put64 (rsp - 8) v0).put128 (rsp - 8 - 32 + 0x10) v1).write128 (rsp - 8 - 32 + 0x0) w = some (((mem.put64 (rsp - 8) v0).put128 (rsp - 8 - 32 + 0x10) v1).put128 (rsp - 8 - 32 + 0x0) w) :=
    fun v0 v1 w => write_vec (owned16_put128 _ _ _ _ (owned16_put64 _ _ _ _ oC0)) w
  have w3 : ∀ (v0 : BitVec 64) (v1 v2 : V) (w : BitVec 64), (((mem.put64 (rsp - 8) v0).put128 (rsp - 8 - 32 + 0x10) v1).put128 (rsp - 8 - 32 + 0x0) v2).write (rsp - 8 - 32 - 8) w 64 = some ((((mem.put64 (rsp - 8) v0).put128 (rsp - 8 - 32 + 0x10) v1).put128 (rsp - 8 - 32 + 0x0) v2).put64 (rsp - 8 - 32 - 8) w) :=
    fun v0 v1 v2 w => write_quad (owned8_put128 _ _ _ _ (owned8_put128 _ _ _ _ (owned8_put64 _ _ _ _ oCall))) w
  subst hp
  have hz : True := trivial
  run_code [write_quad oPush, rK0, rK1, rLen, rFl, rPl, rCtr, a40, a50, aC1, aC0, w1, w2, w3, hz]
  refine ⟨_, rfl, rfl, ?_, rfl, rfl, rfl, rfl, ?_, rfl, ⟨rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  · dsimp only; bv_decide
  · dsimp only; bv_decide
  · dsimp only
    simp only [show rsp - 8 - 32 + 16 = rsp - 0x18 by bv_decide, show rsp - 8 - 32 + 0 = rsp - 0x28 by bv_decide,
      show rsp - 8 - 32 - 8 = rsp - 0x30 by bv_decide]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- The first sixteen instructions, on the sse path: the key copied to the stack, the node's
length, counter and flags in the kernel's argument registers, and the call. -/
theorem pre_sse (k0 k1 b0 b1 b2 b3 : V) (len8 fl8 pl8 : BitVec 8) (ctr ra : BitVec 64) (rax rcx rdx rbx rsp rbp rsi rdi r8 r9 r12 r13 r14 r15 : BitVec 64) (zf cf : Option Bool)
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : V) (mem : Mem)
    (hK0 : Vec mem (rsi + 0x40) k0) (hK1 : Vec mem (rsi + 0x50) k1)
    (hB0 : Vec mem (rsi + 0) b0) (hB1 : Vec mem (rsi + 16) b1) (hB2 : Vec mem (rsi + 32) b2) (hB3 : Vec mem (rsi + 48) b3)
    (hLen : mem (rsi + 0x60) = some len8) (hCtr : Quad mem (rsi + 0x68) ctr) (hFl : mem (rsi + 0x70) = some fl8)
    (hPl : mem (rsi + 0x71) = some pl8)
    (oPush : Owned8 mem (rsp - 8)) (oC1 : Owned16 mem (rsp - 8 - 32 + 0x10)) (oC0 : Owned16 mem (rsp - 8 - 32 + 0x0))
    (oCall : Owned8 mem (rsp - 8 - 32 - 8))
    (hsp : rsp &&& 15 = 8) (hsi : rsi &&& 15 = 0)
    (aOS : ∀ x, (x - rsi).toNat < 0x72 → 0x30 ≤ (x - (rsp - 0x30)).toNat)
    (hp : pl8 ≠ 5) :
    ∃ s', steps Code.prog 16 ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r12, r13, r14, r15, zf, cf, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, mem, 0x11000⟩ = some s' ∧ s'.pc = 0x20000 ∧
      s'.rdi = rsp - 0x28 ∧ s'.rsi = rsi ∧ s'.rdx = BitVec.setWidth 64 len8 &&& 255 ∧ s'.rcx = ctr ∧
      s'.r8 = BitVec.setWidth 64 fl8 &&& 255 ∧ s'.rsp = rsp - 0x30 ∧ s'.rbx = rdi ∧
      (s'.rbp = rbp ∧ s'.r12 = r12 ∧ s'.r13 = r13 ∧ s'.r14 = r14 ∧ s'.r15 = r15) ∧
      s'.mem = ((((mem.put64 (rsp - 8) rbx).put128 (rsp - 0x18) k1).put128 (rsp - 0x28) k0).put64 (rsp - 0x30) (BitVec.ofNat 64 0x1104D)) := by
  have rK0 : ∀ v0, (mem.put64 (rsp - 8) v0).read128 (rsi + 0x40) = some k0 := fun v0 => by
    rw [read128_congr (m := mem) _ (fun x hx => by have h := aOS x (by bv_omega); rw [put64_other _ _ _ x (by bv_omega)])]
    exact read_vec hK0
  have rK1 : ∀ v0, (mem.put64 (rsp - 8) v0).read128 (rsi + 0x50) = some k1 := fun v0 => by
    rw [read128_congr (m := mem) _ (fun x hx => by have h := aOS x (by bv_omega); rw [put64_other _ _ _ x (by bv_omega)])]
    exact read_vec hK1
  have rLen : ∀ v0 v1 v2, (((mem.put64 (rsp - 8) v0).put128 (rsp - 8 - 32 + 0x10) v1).put128 (rsp - 8 - 32 + 0x0) v2).read (rsi + 0x60) 8 = some (len8.setWidth 64) := fun v0 v1 v2 =>
    read_byte (by have h := aOS (rsi + 0x60) (by bv_omega); rw [put128_other _ _ _ _ (by bv_omega), put128_other _ _ _ _ (by bv_omega), put64_other _ _ _ _ (by bv_omega)]; exact hLen)
  have rFl : ∀ v0 v1 v2, (((mem.put64 (rsp - 8) v0).put128 (rsp - 8 - 32 + 0x10) v1).put128 (rsp - 8 - 32 + 0x0) v2).read (rsi + 0x70) 8 = some (fl8.setWidth 64) := fun v0 v1 v2 =>
    read_byte (by have h := aOS (rsi + 0x70) (by bv_omega); rw [put128_other _ _ _ _ (by bv_omega), put128_other _ _ _ _ (by bv_omega), put64_other _ _ _ _ (by bv_omega)]; exact hFl)
  have rPl : ∀ v0 v1 v2, (((mem.put64 (rsp - 8) v0).put128 (rsp - 8 - 32 + 0x10) v1).put128 (rsp - 8 - 32 + 0x0) v2).read (rsi + 0x71) 8 = some (pl8.setWidth 64) := fun v0 v1 v2 =>
    read_byte (by have h := aOS (rsi + 0x71) (by bv_omega); rw [put128_other _ _ _ _ (by bv_omega), put128_other _ _ _ _ (by bv_omega), put64_other _ _ _ _ (by bv_omega)]; exact hPl)
  have rCtr : ∀ v0 v1 v2, (((mem.put64 (rsp - 8) v0).put128 (rsp - 8 - 32 + 0x10) v1).put128 (rsp - 8 - 32 + 0x0) v2).read (rsi + 0x68) 64 = some ctr := fun v0 v1 v2 => by
    rw [read_congr (m := mem) _ (fun x hx => by have h := aOS x (by bv_omega); rw [put128_other _ _ _ x (by bv_omega), put128_other _ _ _ x (by bv_omega), put64_other _ _ _ x (by bv_omega)])]
    exact read_quad hCtr
  have a40 : aligned16 (rsi + 0x40) = true := by simp only [aligned16]; bv_decide
  have a50 : aligned16 (rsi + 0x50) = true := by simp only [aligned16]; bv_decide
  have aC1 : aligned16 (rsp - 8 - 32 + 0x10) = true := by simp only [aligned16]; bv_decide
  have aC0 : aligned16 (rsp - 8 - 32 + 0x0) = true := by simp only [aligned16]; bv_decide
  have w1 : ∀ (v0 : BitVec 64) (w : V), (mem.put64 (rsp - 8) v0).write128 (rsp - 8 - 32 + 0x10) w = some ((mem.put64 (rsp - 8) v0).put128 (rsp - 8 - 32 + 0x10) w) :=
    fun v0 w => write_vec (owned16_put64 _ _ _ _ oC1) w
  have w2 : ∀ (v0 : BitVec 64) (v1 w : V), ((mem.put64 (rsp - 8) v0).put128 (rsp - 8 - 32 + 0x10) v1).write128 (rsp - 8 - 32 + 0x0) w = some (((mem.put64 (rsp - 8) v0).put128 (rsp - 8 - 32 + 0x10) v1).put128 (rsp - 8 - 32 + 0x0) w) :=
    fun v0 v1 w => write_vec (owned16_put128 _ _ _ _ (owned16_put64 _ _ _ _ oC0)) w
  have w3 : ∀ (v0 : BitVec 64) (v1 v2 : V) (w : BitVec 64), (((mem.put64 (rsp - 8) v0).put128 (rsp - 8 - 32 + 0x10) v1).put128 (rsp - 8 - 32 + 0x0) v2).write (rsp - 8 - 32 - 8) w 64 = some ((((mem.put64 (rsp - 8) v0).put128 (rsp - 8 - 32 + 0x10) v1).put128 (rsp - 8 - 32 + 0x0) v2).put64 (rsp - 8 - 32 - 8) w) :=
    fun v0 v1 v2 w => write_quad (owned8_put128 _ _ _ _ (owned8_put128 _ _ _ _ (owned8_put64 _ _ _ _ oCall))) w
  have hz : (BitVec.setWidth 64 pl8 - 5#64 &&& 255 == 0) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]; revert hp; bv_decide
  run_code [write_quad oPush, rK0, rK1, rLen, rFl, rPl, rCtr, a40, a50, aC1, aC0, w1, w2, w3, hz]
  refine ⟨_, rfl, rfl, ?_, rfl, rfl, rfl, rfl, ?_, rfl, ⟨rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  · dsimp only; bv_decide
  · dsimp only; bv_decide
  · dsimp only
    simp only [show rsp - 8 - 32 + 16 = rsp - 0x18 by bv_decide, show rsp - 8 - 32 + 0 = rsp - 0x28 by bv_decide,
      show rsp - 8 - 32 - 8 = rsp - 0x30 by bv_decide]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- The instructions after the kernel returns (a jump, then eight): the chaining value copied from the stack
to where the caller asked, RBX restored, the return. -/
theorem suf_avx (c0 c1 : V) (rbx0 ra : BitVec 64) (s : State) (hpc : s.pc = 0x1103B)
    (hC0 : Vec s.mem (s.rsp + 0x0) c0) (hC1 : Vec s.mem (s.rsp + 0x10) c1)
    (al0 : aligned16 (s.rsp + 0x0) = true) (al1 : aligned16 (s.rsp + 0x10) = true)
    (oU1 : Owned16 s.mem (s.rbx + 0x10)) (oU0 : Owned16 s.mem (s.rbx + 0x0))
    (hpop : s.mem.read (s.rsp + 32) 64 = some rbx0) (hret : s.mem.read (s.rsp + 32 + 8) 64 = some ra)
    (aUS : ∀ x, (x - (s.rsp + 32)).toNat < 16 → 32 ≤ (x - s.rbx).toNat) :
    ∃ s', steps Code.prog 9 s = some s' ∧ s'.pc = ra.toNat ∧ s'.rsp = s.rsp + 32 + 8 + 8 ∧ s'.rax = s.rbx ∧ s'.rbx = rbx0 ∧
      (s'.rbp = s.rbp ∧ s'.r12 = s.r12 ∧ s'.r13 = s.r13 ∧ s'.r14 = s.r14 ∧ s'.r15 = s.r15) ∧
      s'.mem = (s.mem.put128 (s.rbx + 0x10) c1).put128 (s.rbx + 0x0) c0 := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r12, r13, r14, r15, zf, cf, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, mem, pc⟩ := s
  simp only at hpc hC0 hC1 al0 al1 oU1 oU0 hpop hret aUS
  subst hpc
  have w1 : ∀ (a w : V), (mem.put128 (rbx + 0x10) a).write128 (rbx + 0x0) w = some ((mem.put128 (rbx + 0x10) a).put128 (rbx + 0x0) w) :=
    fun a w => write_vec (owned16_put128 _ _ _ _ oU0) w
  have rpop : ∀ (a b : V), ((mem.put128 (rbx + 0x10) a).put128 (rbx + 0x0) b).read (rsp + 32) 64 = some rbx0 := fun a b => by
    rw [read_congr (m := mem) _ (fun x hx => by
      have h := aUS x (by bv_omega)
      rw [put128_other _ _ _ x (by bv_omega), put128_other _ _ _ x (by bv_omega)])]
    exact hpop
  have rret : ∀ (a b : V), ((mem.put128 (rbx + 0x10) a).put128 (rbx + 0x0) b).read (rsp + 32 + 8) 64 = some ra := fun a b => by
    rw [read_congr (m := mem) _ (fun x hx => by
      have h := aUS x (by bv_omega)
      rw [put128_other _ _ _ x (by bv_omega), put128_other _ _ _ x (by bv_omega)])]
    exact hret
  run_code [read_vec hC0, read_vec hC1, al0, al1, write_vec oU1, w1, rpop, rret]
  exact ⟨_, rfl, rfl, rfl, rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl⟩, rfl⟩

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- The instructions after the kernel returns (eight): the chaining value copied from the stack
to where the caller asked, RBX restored, the return. -/
theorem suf_sse (c0 c1 : V) (rbx0 ra : BitVec 64) (s : State) (hpc : s.pc = 0x1104D)
    (hC0 : Vec s.mem (s.rsp + 0x0) c0) (hC1 : Vec s.mem (s.rsp + 0x10) c1)
    (al0 : aligned16 (s.rsp + 0x0) = true) (al1 : aligned16 (s.rsp + 0x10) = true)
    (oU1 : Owned16 s.mem (s.rbx + 0x10)) (oU0 : Owned16 s.mem (s.rbx + 0x0))
    (hpop : s.mem.read (s.rsp + 32) 64 = some rbx0) (hret : s.mem.read (s.rsp + 32 + 8) 64 = some ra)
    (aUS : ∀ x, (x - (s.rsp + 32)).toNat < 16 → 32 ≤ (x - s.rbx).toNat) :
    ∃ s', steps Code.prog 8 s = some s' ∧ s'.pc = ra.toNat ∧ s'.rsp = s.rsp + 32 + 8 + 8 ∧ s'.rax = s.rbx ∧ s'.rbx = rbx0 ∧
      (s'.rbp = s.rbp ∧ s'.r12 = s.r12 ∧ s'.r13 = s.r13 ∧ s'.r14 = s.r14 ∧ s'.r15 = s.r15) ∧
      s'.mem = (s.mem.put128 (s.rbx + 0x10) c1).put128 (s.rbx + 0x0) c0 := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r12, r13, r14, r15, zf, cf, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, mem, pc⟩ := s
  simp only at hpc hC0 hC1 al0 al1 oU1 oU0 hpop hret aUS
  subst hpc
  have w1 : ∀ (a w : V), (mem.put128 (rbx + 0x10) a).write128 (rbx + 0x0) w = some ((mem.put128 (rbx + 0x10) a).put128 (rbx + 0x0) w) :=
    fun a w => write_vec (owned16_put128 _ _ _ _ oU0) w
  have rpop : ∀ (a b : V), ((mem.put128 (rbx + 0x10) a).put128 (rbx + 0x0) b).read (rsp + 32) 64 = some rbx0 := fun a b => by
    rw [read_congr (m := mem) _ (fun x hx => by
      have h := aUS x (by bv_omega)
      rw [put128_other _ _ _ x (by bv_omega), put128_other _ _ _ x (by bv_omega)])]
    exact hpop
  have rret : ∀ (a b : V), ((mem.put128 (rbx + 0x10) a).put128 (rbx + 0x0) b).read (rsp + 32 + 8) 64 = some ra := fun a b => by
    rw [read_congr (m := mem) _ (fun x hx => by
      have h := aUS x (by bv_omega)
      rw [put128_other _ _ _ x (by bv_omega), put128_other _ _ _ x (by bv_omega)])]
    exact hret
  run_code [read_vec hC0, read_vec hC1, al0, al1, write_vec oU1, w1, rpop, rret]
  exact ⟨_, rfl, rfl, rfl, rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl⟩, rfl⟩

