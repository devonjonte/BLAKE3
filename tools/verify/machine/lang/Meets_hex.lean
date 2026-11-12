import AbiProof
import Lemmas_hex
import Proof_hex
import ReadingList
open X86 Cells

/-! # `hex`, as assembled, meets `Hex.contract`, quietly

From the kernel's own theorem about vectors (`Proof_hex.lean`, written by the compiler) and the lemmas that
carry bytes to vectors and back. Checked by Lean; not to be read but for the theorem's statement. -/

set_option maxRecDepth 100000 in
/-- **`hex`, as assembled, meets its contract whatever the hash is, and what an observer of time and of the
cache sees does not depend on the hash.** -/
theorem hex_meets : ∀ (out inp : BitVec 64),
    Abi.MeetsQuietly Code_hex.prog 0x50000 (fun hash : List (BitVec 8) => Hex.contract out inp hash) := by
  intro out inp rsp ra
  obtain ⟨seen, hk⟩ := hex_meets_its_contract out inp rsp ra
  refine ⟨seen, ?_⟩
  intro hash s hpc hsp hargs hra hstack hap _ hreq
  simp only [Hex.contract, List.length_cons, List.length_nil, List.take, List.cons.injEq, and_true] at hargs
  obtain ⟨hdi, hsi⟩ := hargs
  simp only [Hex.contract, abi, List.map_cons, List.map_nil, List.cons_append, List.nil_append, Abi.AllApart, Abi.Apart,
    List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, BitVec.sub_zero, BitVec.zero_add] at hap hreq
  obtain ⟨⟨apOut, apInp⟩, _⟩ := hap
  obtain ⟨hOwn, hLen, hAt⟩ := hreq
  obtain ⟨v0, v1, hv0, hv1, rfl⟩ := Bytes.vecs32 hLen hAt
  obtain ⟨o0, o1, o2, o3⟩ := Bytes.owned4 hOwn
  obtain ⟨S, hrun, hleak, hpc', hsp', hbx, hbp, h12, h13, h14, h15, w0, w1, w2, w3, hframe⟩ :=
    hk s v0 v1 hpc hdi.symm hsi.symm hsp (by simpa using hv0) hv1 o0 o1 o2 o3
      (by rw [← hsp]; exact read_quad hra) (by intro x hx; rw [← hsp] at hx; obtain ⟨a1, a2⟩ := apOut; bv_omega)
  refine ⟨45, S, hrun, hleak, hpc', by rw [hsp', hsp]; rfl, hbx, hbp, h12, h13, h14, h15, ?_, ?_⟩
  · simp only [Hex.contract, abi, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, true_and]
    rw [Hex.text_vecs]
    exact ⟨rfl, Bytes.at_of_vecs64 (by simpa using w0) w1 w2 w3⟩
  · intro x _ hmod
    simp only [Hex.contract, abi, List.map_cons, List.map_nil, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true] at hmod
    exact hframe x (BitVec.le_def.mp hmod)

#print axioms hex_meets
#reading_list hex_meets
