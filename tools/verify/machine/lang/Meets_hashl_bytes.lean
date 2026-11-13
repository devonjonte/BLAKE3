import Proof_hashl
import StackAsBytes
import HashBytes
open X86

/-! # `hashl` on x86-64 meets the contract that names no machine: the function computes BLAKE3

`Hash.byteContract` (`../spec/HashContract.lean`) is the statement a user reads: with a message's bytes at
`input` and the specification's IV at `key`, the 32 bytes at `out` become `Blake3.hashBytes` of the message
(C2SP's `Blake3.hash`). `hashl_meets` (`Proof_hashl.lean`) is about the model's own contract
(`Hashl.contract`: any key, any mode, the root's eight words); here it is read as the byte contract. -/

/-- A function that meets a contract meets it with more asked of the arguments. -/
theorem Abi.Meets.of_accepts {prog : Nat → Option (Instr × Nat)} {entry : Nat} {c : Abi.Contract} (accepts : Prop)
    (h : Abi.Meets prog entry c) (hacc : accepts → c.accepts) : Abi.Meets prog entry { c with accepts := accepts } :=
  fun s ra hpc hargs hq hR hAp ha hreq => h s ra hpc hargs hq hR hAp (hacc ha) hreq

/-- The IV's 32 bytes, as a caller passes them, are the model's chaining value of the IV. -/
theorem Hash.piece_key (a : BitVec 64) :
    Abi.Piece.ofBytes ((Bytes.plain 32).keeps a Blake3.ivBytes) = Cv.layout.keeps a Blake3.IV :=
  Cv.piece_keeps a Blake3.IV

/-- The 32 bytes of the hash, as the byte contract says them, are the model's chaining value of the root's words. -/
theorem Hash.piece_out (a : BitVec 64) (msg : List (BitVec 8)) :
    Abi.Piece.ofBytes ((Bytes.plain 32).fills a (Blake3.hashBytes msg)) = Cv.layout.fills a (Hash.words Blake3.IV 0#64 msg) := by
  rw [hashBytes_words]
  exact Cv.opens.fills a _

/-- **`Hash.byteContract` read for this machine is `Hashl.contract` under the IV and no flags**, with what
the byte contract accepts. -/
theorem Hash.contract_eq (out inp len key plat : BitVec 64) (msg : List (BitVec 8)) (hlen : msg.length < 2 ^ 64) :
    Abi.ofBytes (Hash.byteContract out inp len key plat msg) 4608#64
      = { Hashl.contract out inp len key 0#64 plat Blake3.IV msg with accepts := (Hash.byteContract out inp len key plat msg).accepts } := by
  simp only [Abi.ofBytes, Hash.byteContract, Hashl.contract, List.map, Hash.piece_key, Hash.piece_out, Bytes.piece_keeps _ hlen]

/-- **The x86-64 code of `hashl` computes BLAKE3**: for every message shorter than 2^64 - 1024 bytes it meets
`Hash.byteContract`, with 4608 bytes of stack. -/
theorem hashl_meets_bytes (out inp len key plat : BitVec 64) (msg : List (BitVec 8)) (hlen : msg.length < 2 ^ 64 - 1024) :
    Abi.Meets Code_hashl.prog 0x40000 (Abi.ofBytes (Hash.byteContract out inp len key plat msg) 4608#64) := by
  rw [Hash.contract_eq out inp len key plat msg (by omega)]
  exact Abi.Meets.of_accepts _ (Proof_hashl.hashl_meets out inp len key 0#64 plat Blake3.IV msg)
    (fun h => ⟨h.1, hlen, by decide⟩)

#print axioms hashl_meets_bytes
