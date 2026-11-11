import Spec_merge
import Proof_merge
import MergeTree
import ReadingList
open X86 Cells MergeCode

/-! # `merge` meets its statement

From the compiler's theorem about the machine's state (`Proof_merge.merge_meets_its_contract`) and
`Stack.merged_is_mergeTo`. Checked by Lean; not to be read. -/

theorem Cvs.at_of_entries {m : Mem} : ∀ (es : List (V × V)) (a : BitVec 64), Entries m a es → Cvs.At m a (es.map cvOf)
  | [], _, _ => trivial
  | e :: es, a, ⟨h0, h1, hr⟩ => ⟨⟨e.1, e.2, by rw [BitVec.add_zero] at h0; exact h0, h1, rfl⟩, Cvs.at_of_entries es _ hr⟩

theorem Cvs.entries_of_at {m : Mem} : ∀ (cvs : List Blake3.CV) (a : BitVec 64), Cvs.At m a cvs → ∃ es, Entries m a es ∧ es.map cvOf = cvs
  | [], _, _ => ⟨[], trivial, rfl⟩
  | cv :: rest, a, ⟨⟨v0, v1, h0, h1, hw⟩, hr⟩ => by
    obtain ⟨es, he, hm⟩ := Cvs.entries_of_at rest _ hr
    exact ⟨(v0, v1) :: es, ⟨by rw [BitVec.add_zero]; exact h0, h1, he⟩, by simp only [List.map_cons, cvOf, hw, hm]⟩

theorem top_address (st x : BitVec 64) : st + 32#64 + (x - 1#64) <<< 5 = st + 32#64 * x := by bv_decide

theorem Stack.at_of_holds {m : Mem} {st len : BitVec 64} {es : Stack.Cvs} (h : Stack.holds m st len es) :
    Stack.At m st (es.map cvOf) ∧ len.toNat = (es.map cvOf).length := by
  obtain ⟨hl, hb, hq, he, hr⟩ := h
  have e : BitVec.ofNat 64 (es.map cvOf).length = len := by
    rw [List.length_map, ← hl]; exact BitVec.ofNat_toNat ..
  refine ⟨⟨by rw [List.length_map]; bv_omega, hr, by rw [e]; exact hq, ?_⟩, by rw [List.length_map]; exact hl⟩
  rw [e, ← top_address]; exact Cvs.at_of_entries es _ he

theorem Stack.holds_of_at {m : Mem} {st : BitVec 64} {cvs : List Blake3.CV} (h : Stack.At m st cvs) :
    ∃ len es, Stack.holds m st len es ∧ es.map cvOf = cvs := by
  obtain ⟨hn, hr, hq, hc⟩ := h
  rw [← top_address] at hc
  obtain ⟨es, he, hm⟩ := Cvs.entries_of_at cvs _ hc
  have hlen : es.length = cvs.length := by rw [← hm, List.length_map]
  refine ⟨BitVec.ofNat 64 cvs.length, es, ⟨?_, ?_, hq, he, hr⟩, hm⟩
  · rw [hlen, BitVec.toNat_ofNat]; omega
  · rw [BitVec.le_def, BitVec.toNat_ofNat]; simp only [BitVec.toNat_ofNat]; omega

set_option maxRecDepth 100000 in
/-- **`merge`, as assembled, meets its statement.** -/
theorem merge_meets : Merge.statement := by
  intro st key flags plat target k cvs h1 hfl s ra hpc hargs hra hstack hapart ⟨hS, v0, v1, hk0, hk1, hk⟩
  obtain ⟨len0, es0, hH, hmap⟩ := Stack.holds_of_at hS
  simp only [List.length_cons, List.length_nil, List.take, List.cons.injEq, and_true] at hargs
  obtain ⟨a1, a2, a3, a4, a5⟩ := hargs
  simp only [Abi.AllApart, Abi.Apart, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true] at hapart
  obtain ⟨⟨ap1, ap2⟩, ap3⟩ := hapart
  have e176 : s.rsp - 176#64 + 176#64 = s.rsp := by bv_decide
  obtain ⟨n, s', hrun, hpc', hsp', hbx, hbp, h12, h13, h14, h15, hout, hpost⟩ :=
    Proof_merge.merge_meets_its_contract (s.rsp - 176#64) st key flags plat target ra s.rbx s.rbp s.r12 s.r13 s.r14 s.r15 es0 v0 v1 len0 s.mem
      h1 hfl ap1 ap2 ap3 s
      ⟨hpc, e176.symm, a1.symm, a2.symm, a3.symm, a4.symm, a5.symm, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hstack, by rw [e176]; exact hra, hH, hk0, hk1⟩
  have hm := Stack.merged_is_mergeTo v0 v1 flags target es0 hfl h1
  rw [hk, hmap] at hm
  obtain ⟨hat, hres⟩ := Stack.at_of_holds hpost
  rw [hm] at hat hres
  refine ⟨n, s', hrun, hpc', by rw [hsp']; bv_decide, hbx, hbp, h12, h13, h14, h15, ⟨hat, hres⟩, ?_⟩
  intro x hx hmod
  simp only [List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true] at hmod
  exact hout x hx hmod

#print axioms merge_meets
#reading_list merge_meets
