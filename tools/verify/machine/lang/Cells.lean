import Machine
import MemLemmas
import Hoare
import Lean
open X86

/-! # Memory in cells: what a generated proof of word-level code runs on

Word-level code reaches memory through 8-byte words and 16-byte vectors at addresses of the form
`base + offset`. Memory after some writes is the memory before with those cells put over it, and a
read finds its cell by going down through the puts: the same cell gives its value, a cell that is
apart is passed. "Apart" is two bit-vector inequalities, which `bv_decide` settles from what is known
of the bases. These lemmas are written once; the compiler's proofs use them by name. -/

/-- The lemmas that say which instruction of a function written in the language is at which address. -/
register_simp_attr ode_at

/-- Definitions a contract is written with, which a proof opens to see what the contract says of memory. -/
register_simp_attr abi

namespace Cells

/-- From this state the program runs, without a fault, to a state where `Q` holds. -/
def Runs (prog : Nat → Option (Instr × Nat)) (s : State) (Q : State → Prop) : Prop := ∃ k s', steps prog k s = some s' ∧ Q s'

theorem runs_then {prog : Nat → Option (Instr × Nat)} {a : Nat} {s s1 : State} {Q : State → Prop}
    (h : steps prog a s = some s1) (next : Runs prog s1 Q) : Runs prog s Q := by
  obtain ⟨k, s', h2, q⟩ := next
  exact ⟨a + k, s', by rw [steps_add, h, Option.bind_some, h2], q⟩

theorem runs_done {prog : Nat → Option (Instr × Nat)} {s : State} {Q : State → Prop} (q : Q s) : Runs prog s Q := ⟨0, s, rfl, q⟩

/-! ## Reading through a put -/

theorem read_put64_same (m : Mem) (a v : BitVec 64) : (m.put64 a v).read a 64 = some v := read_quad (quad_put64 m a v)
theorem read128_put128_same (m : Mem) (a : BitVec 64) (v : V) : (m.put128 a v).read128 a = some v := read_vec (vec_put128 m a v)

theorem read_put64_far (m : Mem) (a v b : BitVec 64) (h : 8#64 ≤ b - a ∧ 8#64 ≤ a - b) : (m.put64 a v).read b 64 = m.read b 64 :=
  read_congr b (fun x hx => put64_other m a v x (by obtain ⟨h1, h2⟩ := h; bv_omega))
theorem read_put128_far (m : Mem) (a : BitVec 64) (v : V) (b : BitVec 64) (h : 16#64 ≤ b - a ∧ 8#64 ≤ a - b) : (m.put128 a v).read b 64 = m.read b 64 :=
  read_congr b (fun x hx => put128_other m a v x (by obtain ⟨h1, h2⟩ := h; bv_omega))
theorem read128_put64_far (m : Mem) (a v b : BitVec 64) (h : 8#64 ≤ b - a ∧ 16#64 ≤ a - b) : (m.put64 a v).read128 b = m.read128 b :=
  read128_congr b (fun x hx => put64_other m a v x (by obtain ⟨h1, h2⟩ := h; bv_omega))
theorem read128_put128_far (m : Mem) (a : BitVec 64) (v : V) (b : BitVec 64) (h : 16#64 ≤ b - a ∧ 16#64 ≤ a - b) : (m.put128 a v).read128 b = m.read128 b :=
  read128_congr b (fun x hx => put128_other m a v x (by obtain ⟨h1, h2⟩ := h; bv_omega))

/-! ## Reading a cell that a fact at hand describes -/

theorem read_cell (m : Mem) (a v : BitVec 64) (h : Quad m a v) : m.read a 64 = some v := read_quad h
theorem read128_cell (m : Mem) (a : BitVec 64) (v : V) (h : Vec m a v) : m.read128 a = some v := read_vec h

/-! ## Writing a cell the program owns -/

theorem write64_owned (m : Mem) (a v : BitVec 64) (o : Owned8 m a) : m.write a v 64 = some (m.put64 a v) := write_quad o v
theorem write128_owned (m : Mem) (a : BitVec 64) (v : V) (o : Owned16 m a) : m.write128 a v = some (m.put128 a v) := write_vec o v

/-- A region the program owns: `n` bytes from `b`. -/
def Region (m : Mem) (b n : BitVec 64) : Prop := ∀ d : BitVec 64, d < n → (m (b + d)).isSome

theorem owned8_region {m : Mem} {b n : BitVec 64} (h : Region m b n) (c : BitVec 64) (hc : c ≤ c + 7#64 ∧ c + 7#64 < n) : Owned8 m (b + c) := by
  obtain ⟨h1, h2⟩ := hc
  have e : ∀ i : BitVec 64, b + c + i = b + (c + i) := fun i => BitVec.add_assoc b c i
  simp only [Owned8, e]
  exact ⟨h _ (by bv_omega), h _ (by bv_omega), h _ (by bv_omega), h _ (by bv_omega), h _ (by bv_omega), h _ (by bv_omega), h _ (by bv_omega), h _ (by bv_omega)⟩

theorem owned16_region {m : Mem} {b n : BitVec 64} (h : Region m b n) (c : BitVec 64) (hc : c ≤ c + 15#64 ∧ c + 15#64 < n) : Owned16 m (b + c) := by
  obtain ⟨h1, h2⟩ := hc
  have e : ∀ i : BitVec 64, b + c + i = b + (c + i) := fun i => BitVec.add_assoc b c i
  simp only [Owned16, e]
  exact ⟨h _ (by bv_omega), h _ (by bv_omega), h _ (by bv_omega), h _ (by bv_omega), h _ (by bv_omega), h _ (by bv_omega), h _ (by bv_omega), h _ (by bv_omega),
    h _ (by bv_omega), h _ (by bv_omega), h _ (by bv_omega), h _ (by bv_omega), h _ (by bv_omega), h _ (by bv_omega), h _ (by bv_omega), h _ (by bv_omega)⟩

theorem owned8_region0 {m : Mem} {b n : BitVec 64} (h : Region m b n) (hc : 7#64 < n) : Owned8 m b := by
  have := owned8_region h 0#64 (by bv_decide)
  rwa [BitVec.add_zero] at this
theorem owned16_region0 {m : Mem} {b n : BitVec 64} (h : Region m b n) (hc : 15#64 < n) : Owned16 m b := by
  have := owned16_region h 0#64 (by bv_decide)
  rwa [BitVec.add_zero] at this

theorem region_put64 {m : Mem} {b n : BitVec 64} (a v : BitVec 64) (h : Region m b n) : Region (m.put64 a v) b n :=
  fun d hd => put64_isSome m a v _ (h d hd)
theorem region_put128 {m : Mem} {b n : BitVec 64} (a : BitVec 64) (v : V) (h : Region m b n) : Region (m.put128 a v) b n :=
  fun d hd => put128_isSome m a v _ (h d hd)

/-! ## A byte that no put touched -/

theorem put64_away (m : Mem) (a v x : BitVec 64) (h : 8#64 ≤ x - a) : m.put64 a v x = m x := put64_other m a v x (by bv_omega)
theorem put128_away (m : Mem) (a : BitVec 64) (v : V) (x : BitVec 64) (h : 16#64 ≤ x - a) : m.put128 a v x = m x := put128_other m a v x (by bv_omega)

/-! ## A cell under a put -/

theorem vec_put128_far (m : Mem) (a : BitVec 64) (w : V) (b : BitVec 64) (v : V) (h : 16#64 ≤ b - a ∧ 16#64 ≤ a - b) (hv : Vec m b v) : Vec (m.put128 a w) b v :=
  vec_congr (fun x hx => put128_other m a w x (by obtain ⟨h1, h2⟩ := h; bv_omega)) hv
theorem vec_put64_far (m : Mem) (a w b : BitVec 64) (v : V) (h : 8#64 ≤ b - a ∧ 16#64 ≤ a - b) (hv : Vec m b v) : Vec (m.put64 a w) b v :=
  vec_congr (fun x hx => put64_other m a w x (by obtain ⟨h1, h2⟩ := h; bv_omega)) hv
theorem quad_put128_far (m : Mem) (a : BitVec 64) (w : V) (b v : BitVec 64) (h : 16#64 ≤ b - a ∧ 8#64 ≤ a - b) (hv : Quad m b v) : Quad (m.put128 a w) b v :=
  quad_congr (fun x hx => put128_other m a w x (by obtain ⟨h1, h2⟩ := h; bv_omega)) hv
theorem quad_put64_far (m : Mem) (a w b v : BitVec 64) (h : 8#64 ≤ b - a ∧ 8#64 ≤ a - b) (hv : Quad m b v) : Quad (m.put64 a w) b v :=
  quad_congr (fun x hx => put64_other m a w x (by obtain ⟨h1, h2⟩ := h; bv_omega)) hv

/-! ## Addresses in one form: `base + offset` -/

theorem add_sub_lit (a c d : BitVec 64) : a + c - d = a + (c - d) := by bv_decide

/-! ## The tactics -/

/-- A fact that is several facts joined by "and", taken apart (cells stay whole). -/
syntax "split_ands " ident : tactic
macro_rules
  | `(tactic| split_ands $h) => `(tactic| with_reducible (first | (have hh := And.left (a := _) (b := _) $h; have $h := And.right $h; split_ands $h) | skip))

/-- Addresses in the hypotheses named, in the one form the run uses. -/
macro "norm_addr" " at " hs:(ppSpace colGt ident)+ : tactic => `(tactic| simp only [add_sub_lit, BitVec.add_assoc, BitVec.add_zero, BitVec.reduceAdd, BitVec.reduceSub] at $[$hs]*)

/-- Settles what a memory lemma asks: a cell is owned (through any puts, from a region or a fact at
hand), or two cells are apart (bit-vector inequalities, from what is known of the bases). Lemmas are
matched without unfolding definitions (a put is sixteen puts of a byte underneath; comparing two
unfolded is slow). -/
macro "mem_disch" : tactic => `(tactic| first
  | with_reducible assumption
  | ((repeat (with_reducible (first | apply owned8_put64 | apply owned8_put128 | apply owned16_put64 | apply owned16_put128)))
     first
       | with_reducible assumption
       | ((with_reducible apply owned8_region (by assumption)); bv_decide)
       | ((with_reducible apply owned16_region (by assumption)); bv_decide)
       | ((with_reducible apply owned8_region0 (by assumption)); bv_decide)
       | ((with_reducible apply owned16_region0 (by assumption)); bv_decide)
       | ((with_reducible apply vec_owned); with_reducible assumption)
       | ((with_reducible apply quad_owned); with_reducible assumption))
  | bv_decide)

/-- Run a function's instructions on a state that is written out, memory in cells. -/
macro "run_fn" "[" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic|
  simp (config := {maxSteps := 100000000, implicitDefEqProofs := false}) (disch := mem_disch) only [steps_mk, steps_zero, step, src,
    X86.read, write, State.get, State.set, State.xmm, State.setx, trunc, ode_at,
    read_put64_same, read128_put128_same, read_put64_far, read_put128_far, read128_put64_far, read128_put128_far,
    write64_owned, write128_owned, read_cell, read128_cell, add_sub_lit, BitVec.add_assoc, BitVec.add_zero,
    Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.map_some, bind_pure_comp, Option.isSome_some,
    Nat.reduceEqDiff, ↓reduceIte, reduceCtorEq,
    BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, BitVec.reduceSub, BitVec.reduceMul, BitVec.reduceAnd, BitVec.reduceOr, BitVec.reduceEq,
    BitVec.reduceBEq, BitVec.reduceULT, BitVec.reduceSetWidth, BitVec.reduceShiftLeft, BitVec.reduceHShiftLeft, BitVec.reduceToNat, BitVec.reduceOfNat,
    Nat.reduceAdd, Nat.reduceMul, Bool.not_false, Bool.not_true, Bool.false_eq_true, Bool.true_eq_false, Bool.or_false, Bool.false_or,
    Bool.and_false, Bool.false_and, Bool.true_and, Bool.and_true, $hs,*])

/-- A fact about a cell of a memory that is some puts over a known one: the put that wrote it, or the
fact at hand below the puts that are apart from it. An unknown value is found on the way. -/
macro "mem_fact" : tactic => `(tactic| ((try simp only [add_sub_lit, BitVec.add_assoc, BitVec.add_zero, BitVec.reduceAdd, BitVec.reduceSub]); repeat (first
  | with_reducible exact vec_put128 _ _ _
  | with_reducible exact quad_put64 _ _ _
  | with_reducible assumption
  | with_reducible apply vec_put128_far
  | with_reducible apply vec_put64_far
  | with_reducible apply quad_put128_far
  | with_reducible apply quad_put64_far
  | bv_decide)))

/-- A region is still owned under any puts. -/
macro "mem_region" : tactic => `(tactic| ((repeat (with_reducible (first | apply region_put64 | apply region_put128))); with_reducible assumption))

/-- A byte away from every put is what it was. -/
macro "mem_away" : tactic => `(tactic| simp (disch := bv_decide) only [put64_away, put128_away])

open Lean Elab Tactic Meta in
/-- Run a tactic on a goal that is a proposition; leave any other goal (a value still to be found) alone. -/
elab "skip_unless_prop " t:tactic : tactic => do
  if (← isProp (← (← getMainGoal).getType)) then evalTactic t else pure ()

/-- What a lemma about memory asks of its user, whichever kind it is: a fact at hand, a cell of the
memory after some puts, a region still owned, bytes no put touched, or bit-vector arithmetic. -/
macro "mem_auto" : tactic => `(tactic| skip_unless_prop (first
  | with_reducible assumption
  | (mem_fact; done)
  | mem_region
  | (intros; mem_away; done)
  | bv_decide))

open Lean Elab Tactic Meta in
/-- `have_by h := LEMMA`: the lemma's conclusion as the new fact `h`, each of its hypotheses settled in
order by `mem_auto` (a fact at hand, a cell of memory, arithmetic). Says which hypothesis it could not
show. -/
elab "have_by " h:ident " := " t:term : tactic => withMainContext do
  let e ← Tactic.elabTerm t none (mayPostpone := true)
  let ty ← instantiateMVars (← inferType e)
  let (args, bis, body) ← forallMetaTelescopeReducing ty
  let mut n : Nat := 0
  for (a, bi) in args.zip bis do
    let aty ← instantiateMVars (← inferType a)
    if bi.isExplicit && (← isProp aty) then
      n := n + 1
      let g := a.mvarId!
      unless (← g.isAssigned) do
        let rest ← try Tactic.run g (do evalTactic (← `(tactic| mem_auto))) catch _ => pure [g]
        unless rest.isEmpty do
          throwError "hypothesis {n} of {t} could not be shown:\n{← instantiateMVars aty}"
  let pf ← instantiateMVars (mkAppN e args)
  if pf.hasExprMVar then throwError "{t}: something it speaks of was not found"
  let g ← (← getMainGoal).assert h.getId (← instantiateMVars body) pf
  let (_, g) ← g.intro1P
  replaceMainGoal [g]

open Lean Elab Tactic Meta in
/-- Forget every fact that mentions `x`, but those named: what was known of the memory at entry is not
known of the memory now. -/
elab "forget_about " x:ident " except" keep:(ppSpace colGt ident)* : tactic => withMainContext do
  let fx ← getFVarId x
  let keepIds ← keep.mapM getFVarId
  let mut g ← getMainGoal
  let mut decls : Array LocalDecl := #[]
  for d in (← getLCtx) do decls := decls.push d
  for d in decls.reverse do
    if d.fvarId != fx && !keepIds.contains d.fvarId && !d.isImplementationDetail then
      if (← instantiateMVars d.type).containsFVar fx then
        g ← g.tryClear d.fvarId
  replaceMainGoal [g]

end Cells
