# What two auditors must each read, and what they share (November 12, 2026)

Lines of Lean that a statement depends on, through every definition those use (`#reading_defs`, experiment
branch at e9574d86; Lean's own library left out). These are the lines a reader must read and judge to know
what a theorem *says*; no proof, lemma, tactic or generator is among them. `layers.py` here made the tables
from Lean's output (`rd-*.txt`).

## 1. By layer, for six theorems

| layer | `hex_meets_bytes` | `push_meets_bytes` | `merge_meets_bytes` | `add_meets_bytes` | `hex_neon_meets` | `push_arm_meets` |
|---|---|---|---|---|---|---|
| Google's AArch64 model (shared with a libsignal auditor) | 0 | 0 | 0 | 0 | 6113 | 6113 |
| our x86-64 model (shared with nobody outside) | 338 | 345 | 345 | 345 | 0 | 0 |
| what a contract is and what meeting one means (any code in the language) | 144 | 104 | 104 | 104 | 51 | 49 |
| BLAKE3 and its data (all of blake3-servil-core) | 0 | 20 | 126 | 126 | 0 | 20 |
| the function's contract | 13 | 8 | 14 | 15 | 13 | 8 |
| the function's instructions | 48 | 31 | 277 | 341 | 3 | 3 |
| **total** | **543** | **508** | **866** | **931** | **6,180** | **6,193** |

- Layer 1 is the machine. On AArch64 it is Google DeepMind's model: the 6,113 lines our statements reach are
  all in their `Arm64/Trusted/` (16,767 lines in all), which an auditor of their libsignal theorem reads too.
- Layer 2 is read once by anyone who audits any code written in the language (144 for `hex` because its
  statement also names the observer of time and cache, 40 lines).
- Layer 3 is read once for all of blake3-servil-core. `push` reaches 20 lines of it (what a chaining value and
  the stack are, as bytes); `merge` and `add` 126 (those and the specification's compression and tree).
- Layers 4 and 5 are the function's own: its contract (8 to 15 lines) and the instructions it is about. The
  instructions are the layer nobody should have to read: on x86-64 they are a table a script made from the
  object's listing (Lean does not yet read the bytes); on AArch64 they are the 3 lines of words, which Lean
  decodes.

## 2. Pairs of auditors

| the two auditors | first reads | second reads | both read | only the first | only the second |
|---|---|---|---|---|---|
| `merge` and `push` (x86-64) | 866 | 508 | **469** | 397 (Code_merge 102, Blake3 98, Sse 96, Avx 78, MergeContract 14, Stack 8, KCode 1) | 39 (Code_push 31, PushContract 8) |
| `add` and `merge` (x86-64) | 931 | 866 | **853** | 78 (Code_add 40, Code_push 28, MergeContract 10) | 13 (MergeContract 9, Code_merge 4) |
| `merge` and `hex` (x86-64): two functions with no data in common | 866 | 543 | **420** | 446 (Code_merge 102, Blake3 100, Sse 96, Avx 78, Abi 20, StackBytes 17, MergeContract 14) | 123 (Code_hex 48, Observer 40, Abi 18, HexContract 8, HexText 5, Contract 4, Machine 0) |
| `push` on x86-64 and `push` on AArch64 | 508 | 6,193 | **56** | 452 (Machine 343, Abi 57, Code_push 31, AbiBytes 14, Spec_bytes 3, Cells 2, MemLemmas 2) | 6,137 (Arm64.Trusted.ISA.Eval 2928, Arm64.Trusted.ISA.Decode 1097, Arm64.Trusted.ISA.Float 599, Arm64.Trusted.ISA.Syntax 473, Arm64.Trusted.ISA.State 391, Arm64.Trusted.ISA.Memory 236, Arm64.Trusted.Spec.Hoare 143) |
| `hex` on x86-64 and `hex` on AArch64 | 543 | 6,180 | **43** | 500 (Machine 336, Abi 55, Code_hex 48, Observer 40, AbiBytes 14, Spec_bytes 3, Cells 2) | 6,137 (Arm64.Trusted.ISA.Eval 2928, Arm64.Trusted.ISA.Decode 1097, Arm64.Trusted.ISA.Float 599, Arm64.Trusted.ISA.Syntax 473, Arm64.Trusted.ISA.State 391, Arm64.Trusted.ISA.Memory 236, Arm64.Trusted.Spec.Hoare 143) |
| `push` and `hex` (AArch64) | 6,193 | 6,180 | **6,160** | 33 (StackBytes 17, PushContract 8, Proof_push_arm 3, Blake3 2, Contract 2, Stack 1) | 20 (HexContract 8, HexText 5, Contract 4, Proof_hex_neon 3) |

| our AArch64 `hex` and Google's libsignal theorem | 6,180 | about 26,000 (their paper's count of trusted lines, by file) | **6,113** (what our statement reaches of `Arm64/Trusted/`) | 67 (the contract, `Hex.text`, what meeting means, the words) | about 20,000 (the rest of `Arm64/Trusted/`: process, loader, system calls, 10,654 lines; and their protocol specifications) |
| blake3-servil-core and another codebase in the language, x86-64 | | | **449** (the machine model 345, what a contract is and what meeting one means 104; 40 more if both speak of the observer) | its specification, layouts, contracts, code | theirs |
| the same on AArch64 | | | **6,162** (Google's 6,113, and 49) | the same | theirs |

How to read the libsignal row: their number is whole trusted files, ours is definitions reached, so the two
are not the same measure; I have not built their statement to ask Lean for its list (it needs their whole
build: hours). What is certain: every line of Google's that our AArch64 statements depend on is one their
auditor reads anyway.

## 3. What this says

- Two functions of the core share nearly everything but their own contract and code: `add` over `merge` costs
  78 lines, of which 10 are contract.
- Two architectures share only the contract and the data (43 to 56 lines): the machine is the bulk, and it
  differs. That is the price of two models; it is paid once an architecture, not once a function.
- The function-specific part a person must really read is the contract: 8 to 15 lines.
- The largest avoidable part is layer 5 on x86-64 (31 to 341 lines of instruction tables). Lean reading the
  object's bytes itself (a decoder, as Google's model has) would take it to a few lines, at the price of a
  decoder in layer 1.
