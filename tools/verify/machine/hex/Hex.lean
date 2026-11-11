import X86
import Code
import ByteLemmas
import Regions
open X86

/-! # `Hash::to_hex`, as compiled into the core crate, writes the hash's hexadecimal

A function of the public API with a loop, a table and the stack's red zone: 39 instructions, 324
executed. The theorem is about the machine code rustc 1.99.1 made of it in the two-crate trial. -/

/-- The character of a nibble: `0123456789abcdef`. -/
def hexc (n : BitVec 8) : BitVec 8 := if n.ult 10 then n + 0x30 else n + 0x57
def hi (b : BitVec 8) : BitVec 8 := hexc (b >>> 4)
def lo (b : BitVec 8) : BitVec 8 := hexc (b &&& 0xF)

/-- **The specification**: two characters a byte, the high nibble first. -/
def hex : List (BitVec 8) → List (BitVec 8)
  | [] => []
  | b :: bs => hi b :: lo b :: hex bs

/-- The thirty-two bytes of a hash, given as a function of the offset. -/
def bytesOf (h : BitVec 64 → BitVec 8) : List (BitVec 8) := [h 0#64, h 1#64, h 2#64, h 3#64, h 4#64, h 5#64, h 6#64, h 7#64, h 8#64, h 9#64, h 10#64, h 11#64, h 12#64, h 13#64, h 14#64, h 15#64, h 16#64, h 17#64, h 18#64, h 19#64, h 20#64, h 21#64, h 22#64, h 23#64, h 24#64, h 25#64, h 26#64, h 27#64, h 28#64, h 29#64, h 30#64, h 31#64]

/-- The bytes of a list are in memory from `a`. -/
def Bytes (m : Mem) : BitVec 64 → List (BitVec 8) → Prop
  | _, [] => True
  | a, b :: bs => m a = some b ∧ Bytes m (a + 1) bs

/-- The red zone the function uses: the 68 bytes below the stack pointer. The output: 68 bytes. -/
def inR (d : BitVec 64) : Bool := (d + 68#64).ult 68#64
def inO (c : BitVec 64) : Bool := c.ult 68#64

/-- What one turn of the loop shows an observer, newest first: the addresses of two bytes of the
hash, of four characters of the table, AT INDEXES THAT ARE THE HASH'S NIBBLES, and of four bytes
of the red zone. -/
def turn (T hash sp : BitVec 64) (h : BitVec 64 → BitVec 8) (c0 c1 d0 d1 d2 d3 : BitVec 64) (next : Nat) : List Obs :=
  [.pc next, .addr (sp + d3), .addr ((BitVec.setWidth 64 (h c1) &&& 15#64) + T), .addr (sp + d2),
   .addr (BitVec.setWidth 64 (h c1) >>> 4 + T), .addr (hash + c1), .addr (sp + d1),
   .addr ((BitVec.setWidth 64 (h c0) &&& 15#64) + T), .addr (sp + d0), .addr (BitVec.setWidth 64 (h c0) >>> 4 + T),
   .addr (hash + c0)]

/-- What a whole call shows, newest first. It is a function of the hash: the table is read at
its nibbles. -/
def hexLeak (T hash sp out : BitVec 64) (h : BitVec 64 → BitVec 8) : List Obs :=
  [.pc 0, .addr sp, .addr (out + 12#64), .addr (sp + 18446744073709551560#64), .addr (out + 4#64), .addr (sp + 18446744073709551552#64), .addr (out + 0#64), .addr (sp + 18446744073709551548#64), .addr (out + 16#64), .addr (out + 32#64), .addr (out + 48#64), .addr (sp + 18446744073709551596#64), .addr (sp + 18446744073709551580#64), .addr (sp + 18446744073709551564#64), .addr (out + 64#64), .addr (sp + 18446744073709551612#64), .addr (sp + 18446744073709551548#64)] ++
  turn T hash sp h 30#64 31#64 18446744073709551612#64 18446744073709551613#64 18446744073709551614#64 18446744073709551615#64 4190 ++
  turn T hash sp h 28#64 29#64 18446744073709551608#64 18446744073709551609#64 18446744073709551610#64 18446744073709551611#64 4112 ++
  turn T hash sp h 26#64 27#64 18446744073709551604#64 18446744073709551605#64 18446744073709551606#64 18446744073709551607#64 4112 ++
  turn T hash sp h 24#64 25#64 18446744073709551600#64 18446744073709551601#64 18446744073709551602#64 18446744073709551603#64 4112 ++
  turn T hash sp h 22#64 23#64 18446744073709551596#64 18446744073709551597#64 18446744073709551598#64 18446744073709551599#64 4112 ++
  turn T hash sp h 20#64 21#64 18446744073709551592#64 18446744073709551593#64 18446744073709551594#64 18446744073709551595#64 4112 ++
  turn T hash sp h 18#64 19#64 18446744073709551588#64 18446744073709551589#64 18446744073709551590#64 18446744073709551591#64 4112 ++
  turn T hash sp h 16#64 17#64 18446744073709551584#64 18446744073709551585#64 18446744073709551586#64 18446744073709551587#64 4112 ++
  turn T hash sp h 14#64 15#64 18446744073709551580#64 18446744073709551581#64 18446744073709551582#64 18446744073709551583#64 4112 ++
  turn T hash sp h 12#64 13#64 18446744073709551576#64 18446744073709551577#64 18446744073709551578#64 18446744073709551579#64 4112 ++
  turn T hash sp h 10#64 11#64 18446744073709551572#64 18446744073709551573#64 18446744073709551574#64 18446744073709551575#64 4112 ++
  turn T hash sp h 8#64 9#64 18446744073709551568#64 18446744073709551569#64 18446744073709551570#64 18446744073709551571#64 4112 ++
  turn T hash sp h 6#64 7#64 18446744073709551564#64 18446744073709551565#64 18446744073709551566#64 18446744073709551567#64 4112 ++
  turn T hash sp h 4#64 5#64 18446744073709551560#64 18446744073709551561#64 18446744073709551562#64 18446744073709551563#64 4112 ++
  turn T hash sp h 2#64 3#64 18446744073709551556#64 18446744073709551557#64 18446744073709551558#64 18446744073709551559#64 4112 ++
  turn T hash sp h 0#64 1#64 18446744073709551552#64 18446744073709551553#64 18446744073709551554#64 18446744073709551555#64 4112

theorem steps_mk (prog : Nat → Option (Instr × Nat)) (k : Nat) (rax rcx rdx rbx rsp rbp rsi rdi r8 r9 : BitVec 64)
    (x0 x1 x2 : BitVec 128) (zf cf : Option Bool) (mem : Mem) (pc : Nat) (leak : List Obs) :
    steps prog (k + 1) ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, x0, x1, x2, zf, cf, mem, pc, leak⟩ =
      match prog pc with
      | none => none
      | some (i, next) => (step i next ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, x0, x1, x2, zf, cf, mem, pc, leak⟩).bind (steps prog k) := rfl

theorem steps_zero (prog : Nat → Option (Instr × Nat)) (s : State) : steps prog 0 s = some s := rfl

theorem add_add (a c d : BitVec 64) : a + c + d = a + (c + d) := by bv_decide

theorem zmask (b : BitVec 8) : b.setWidth 64 &&& 4294967295#64 = b.setWidth 64 := by bv_decide
theorem zshr (b : BitVec 8) : (b.setWidth 64 >>> 4) &&& 4294967295#64 = b.setWidth 64 >>> 4 := by bv_decide
theorem zlo (b : BitVec 8) : (b.setWidth 64 &&& 15#64) &&& 4294967295#64 = b.setWidth 64 &&& 15#64 := by bv_decide
theorem byte_zext (c : BitVec 8) : byte (c.setWidth 64 &&& 255#64) 0 = c := by simp only [byte]; bv_decide

/-- Run the instructions of a state that is written out, with memory kept by region. -/
macro "run_hex" "[" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic|
  simp (config := {maxSteps := 100000000, implicitDefEqProofs := false}) (disch := decide) only [steps_mk, steps_zero, step,
    X86.read, write, addr, State.get, State.set, State.xmm, State.setx, trunc, logic, holds, done, touched, seen,
    List.nil_append, List.cons_append, List.append_nil, code_at,
    Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.map_some, bind_pure_comp,
    Nat.reduceEqDiff, ↓reduceIte, reduceCtorEq,
    Mem.read, Mem.read8, Mem.read128, Mem.write, Mem.write8, Mem.write128, Option.isSome_some,
    upd_apply, none_apply, Option.some_or, Option.none_or,
    BitVec.ofNat_eq_ofNat, add_add, BitVec.reduceAdd, BitVec.reduceMul, BitVec.reduceAnd, BitVec.reduceEq, BitVec.reduceSub,
    BitVec.reduceBEq, BitVec.reduceULT, Nat.reduceAdd, Nat.reduceMul, Bool.not_false, Bool.not_true, Bool.false_eq_true,
    zmask, zshr, zlo, byte_zext, byte32_0, byte32_1, byte32_2, byte32_3, byte64_0, byte64_1, byte64_2, byte64_3, byte64_4, byte64_5, byte64_6, byte64_7, by8_0, by8_1, by8_2, by8_3, by8_4, by8_5, by8_6, by8_7, by8_8, by8_9, by8_10, by8_11, by8_12, by8_13, by8_14, by8_15, $hs,*])

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- **The compiled `Hash::to_hex` writes the hash's hexadecimal.** Called with the address of the
output (an `ArrayString<64>`: its length, then 64 characters) in RDI and of the 32 bytes of the hash in
RSI, with the table `0123456789abcdef` at `T`, the 68 bytes below the stack pointer and the output's 68
bytes owned, and those apart as the hypotheses say: it returns, with the output's address in RAX, the
stack pointer popped, the length 64 and `hex` of the hash's bytes in the output, every byte outside the
output and the red zone as it was, and having shown an observer `hexLeak`. -/
theorem to_hex_is_hex (T hash out rsp : BitVec 64) (h : BitVec 64 → BitVec 8) (m : Mem)
    (rax rcx rdx rbx rbp r8 r9 : BitVec 64) (x0 x1 x2 : BitVec 128) (zf cf : Option Bool) (leak : List Obs)
    (hin : ∀ c : BitVec 64, c.ult 32#64 = true → m (hash + c) = some (h c))
    (htab : ∀ x : BitVec 64, x.ult 16#64 = true → m (x + T) = some (hexc (x.setWidth 8)))
    (hrz : ∀ d : BitVec 64, inR d = true → (m (rsp + d)).isSome = true)
    (hout : ∀ c : BitVec 64, inO c = true → (m (out + c)).isSome = true)
    (hra : ∀ k : BitVec 64, k.ult 8#64 = true → m (rsp + k) = some 0#8)
    -- no byte of the red zone, the hash, the table or the return address is in the output; none of the
    -- hash, the table or the output is in the red zone
    (aRO : ∀ d : BitVec 64, inR d = true → inO (rsp + d - out) = false)
    (aOR : ∀ c : BitVec 64, inO c = true → inR (out + c - rsp) = false)
    (aIO : ∀ c : BitVec 64, c.ult 32#64 = true → inO (hash + c - out) = false)
    (aIR : ∀ c : BitVec 64, c.ult 32#64 = true → inR (hash + c - rsp) = false)
    (aTO : ∀ x : BitVec 64, x.ult 16#64 = true → inO (x + T - out) = false)
    (aTR : ∀ x : BitVec 64, x.ult 16#64 = true → inR (x + T - rsp) = false)
    (aAO : ∀ k : BitVec 64, k.ult 8#64 = true → inO (rsp + k - out) = false) :
    ∃ s', Returns (Code.prog T) ⟨rax, rcx, rdx, rbx, rsp, rbp, hash, out, r8, r9, x0, x1, x2, zf, cf, m, 0x1000, leak⟩ s' ∧
      s'.rax = out ∧ s'.rsp = rsp + 8 ∧ s'.rbx = rbx ∧ s'.rbp = rbp ∧
      Bytes s'.mem out ([64#8, 0#8, 0#8, 0#8] ++ hex (bytesOf h)) ∧
      (∀ x, inO (x - out) = false → inR (x - rsp) = false → s'.mem x = m x) ∧
      s'.leak = hexLeak T hash rsp out h ++ leak := by
  -- Memory by region: `mm fR fO` is `m` with the red zone's and the output's written bytes over it.
  let mm (fR fO : Written) : Mem := over (over m rsp inR fR) out inO fO
  have hm : m = mm none' none' := by simp only [mm, over_none]
  have wR : ∀ (fR fO : Written) (d : BitVec 64) (v : BitVec 8), inR d = true → (mm fR fO).put8 (rsp + d) v = mm (upd fR d v) fO := by
    intro fR fO d v hd
    simp only [mm]; rw [put8_over_out _ _ _ _ _ _ (aRO d hd), put8_over_in _ _ _ _ _ _ hd]
  have wO : ∀ (fR fO : Written) (c : BitVec 64) (v : BitVec 8), inO c = true → (mm fR fO).put8 (out + c) v = mm fR (upd fO c v) := by
    intro fR fO c v hc
    simp only [mm]; rw [put8_over_in _ _ _ _ _ _ hc]
  have rR : ∀ (fR fO : Written) (d : BitVec 64), inR d = true → mm fR fO (rsp + d) = (fR d).or (m (rsp + d)) := by
    intro fR fO d hd
    simp only [mm]; rw [over_out _ _ _ _ _ (aRO d hd), over_in _ _ _ _ _ hd]
  have rO : ∀ (fR fO : Written) (c : BitVec 64), inO c = true → mm fR fO (out + c) = (fO c).or (m (out + c)) := by
    intro fR fO c hc
    simp only [mm]; rw [over_in _ _ _ _ _ hc, over_out _ _ _ _ _ (aOR c hc)]
  have rI : ∀ (fR fO : Written) (c : BitVec 64), c.ult 32#64 = true → mm fR fO (hash + c) = some (h c) := by
    intro fR fO c hc
    simp only [mm]; rw [over_out _ _ _ _ _ (aIO c hc), over_out _ _ _ _ _ (aIR c hc), hin c hc]
  have rT : ∀ (fR fO : Written) (x : BitVec 64), x.ult 16#64 = true → mm fR fO (x + T) = some (hexc (x.setWidth 8)) := by
    intro fR fO x hx
    simp only [mm]; rw [over_out _ _ _ _ _ (aTO x hx), over_out _ _ _ _ _ (aTR x hx), htab x hx]
  have rHi : ∀ (fR fO : Written) (b : BitVec 8), mm fR fO (BitVec.setWidth 64 b >>> 4 + T) = some (hi b) := by
    intro fR fO b
    rw [rT fR fO _ (by bv_decide)]; simp only [hi]; congr 2; bv_decide
  have rLo : ∀ (fR fO : Written) (b : BitVec 8), mm fR fO ((BitVec.setWidth 64 b &&& 15#64) + T) = some (lo b) := by
    intro fR fO b
    rw [rT fR fO _ (by bv_decide)]; simp only [lo]; congr 2; bv_decide
  have rA : ∀ (fR fO : Written) (k : BitVec 64), k.ult 8#64 = true → mm fR fO (rsp + k) = some 0#8 := by
    intro fR fO k hk
    have : inR (rsp + k - rsp) = false := by simp only [inR, add_sub_self]; bv_decide
    simp only [mm]; rw [over_out _ _ _ _ _ (aAO k hk), over_out _ _ _ _ _ this, hra k hk]
  have rA0 : ∀ (fR fO : Written), mm fR fO rsp = some 0#8 := by
    intro fR fO
    have := rA fR fO 0#64 (by decide)
    rwa [show rsp + 0#64 = rsp by bv_decide] at this
  have rO0 : ∀ (fR fO : Written), mm fR fO out = (fO 0#64).or (m out) := by
    intro fR fO
    have := rO fR fO 0#64 (by decide)
    rwa [show out + 0#64 = out by bv_decide] at this
  have hrun : ∃ s', steps (Code.prog T) 324 ⟨rax, rcx, rdx, rbx, rsp, rbp, hash, out, r8, r9, x0, x1, x2, zf, cf, mm none' none', 0x1000, leak⟩ = some s' ∧
      s'.pc = done ∧ s'.rax = out ∧ s'.rsp = rsp + 8 ∧ s'.rbx = rbx ∧ s'.rbp = rbp ∧
      Bytes s'.mem out ([64#8, 0#8, 0#8, 0#8] ++ hex (bytesOf h)) ∧
      (∃ fR fO, s'.mem = mm fR fO) ∧
      s'.leak = hexLeak T hash rsp out h ++ leak := by
    run_hex [wR, wO, rR, rO, rI, rHi, rLo, rA, rA0, hrz, hout]
    refine ⟨_, rfl, ?_, rfl, rfl, rfl, rfl, ?_, ⟨_, _, rfl⟩, ?_⟩
    · rfl
    · simp (config := {maxSteps := 100000000}) (disch := decide) only [Bytes, hex, bytesOf, rO, rO0, upd_apply, none_apply, Option.some_or,
        add_add, BitVec.reduceAdd, BitVec.reduceEq, ↓reduceIte, Option.some.injEq, byte, Nat.reduceMul,
        BitVec.reduceUShiftRight, BitVec.reduceSetWidth, BitVec.ofNat_eq_ofNat, and_self, and_true, true_and]
      decide
    · simp only [hexLeak, turn, List.cons_append, List.nil_append, List.append_assoc]
      rfl
  obtain ⟨s', hs, hpc, hax, hsp, hbx, hbp, hbytes, ⟨fR, fO, hmem⟩, hleak⟩ := hrun
  rw [← hm] at hs
  refine ⟨s', ⟨324, hs, hpc⟩, hax, hsp, hbx, hbp, hbytes, ?_, hleak⟩
  intro x hO hR
  rw [hmem]
  simp only [mm]
  rw [over_out _ _ _ _ _ hO, over_out _ _ _ _ _ hR]

#print axioms to_hex_is_hex

set_option maxRecDepth 100000 in
/-- **What it shows depends on the hash.** Two hashes whose first bytes differ in the high nibble
give different traces: the table is read at a different address. So this function is not
constant-time in the hash; where the hash is a secret (a keyed hash's tag not yet compared, a
derived key), its hexadecimal should not be made this way. -/
theorem the_trace_depends_on_the_hash (T hash sp out : BitVec 64) (h h' : BitVec 64 → BitVec 8)
    (hne : h 0#64 >>> 4 ≠ h' 0#64 >>> 4) : hexLeak T hash sp out h ≠ hexLeak T hash sp out h' := by
  intro e
  have e1 := congrArg (fun l => l[191]?) e
  simp only [hexLeak, turn, List.cons_append, List.nil_append, List.append_assoc] at e1
  have e2 : BitVec.setWidth 64 (h 0#64) >>> 4 + T = BitVec.setWidth 64 (h' 0#64) >>> 4 + T := by
    simpa using e1
  exact hne (by bv_decide)

#print axioms the_trace_depends_on_the_hash
