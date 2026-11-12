# What two auditors must each read, and what they share (November 12, 2026)

Lines of Lean that a statement depends on, through every definition those use (`#reading_defs`, experiment
branch at e9574d86). Lean itself is counted too, in its own row and in section 4. These are the lines a reader must read and judge to know
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
| Lean's library: the definitions the statement reaches (`#reading_core`) | 2,237 | 2,330 | 3,434 | 3,434 | 3,961 | 3,990 |
| **total with Lean's library** | 2,780 | 2,838 | 4,300 | 4,365 | 10,141 | 10,183 |
| axioms beyond Lean's three: where they are not 0, Lean's kernel is not enough (section 4) | 5 | 90 | 555 | 718 | 72 | 0 |

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

## 4. Lean itself

"Lean is doing what it is alleged to do" has three parts for an auditor of one theorem, and only the first is
reading that the theorem decides.

**a. The words the statement is written in.** A statement uses Lean's own definitions (`BitVec`, `Nat`, `List`,
`And`, equality, ...). `#reading_core T` (`lang/ReadingCore.lean`) walks from the statement as `#reading_list`
does and counts the ones in Lean's library: 241 definitions, 2,237 lines for `hex` on x86-64, up to 417
definitions, 3,990 lines for `push` on AArch64 (the row above). Two thirds are in one file, `Init/Prelude.lean`,
and the count takes each definition with its documentation comment, so it is an upper figure. Every Lean
theorem in the world shares most of it: this is the layer most shared of all.

**b. The checker.** No statement decides this; it is the same for every theorem. Three choices, in lines:

| checker | lines | notes |
|---|---|---|
| Lean's own kernel (`src/kernel`, C++, v4.34.1) | 8,071 in 36 files | on Lean's runtime (17,559 lines) and GMP for large numbers |
| nanoda (an independent checker, Rust) | 8,760 in 16 files without its tests; the checking itself 5,320 | reads Lean's exported proofs; takes a list of permitted axioms; tried in `build-check/` |
| lean4lean's checker (the kernel written in Lean) | 3,901 in 18 files | partly proved correct in Lean; itself compiled by Lean |

Running a second, independent checker over the same proof is the usual answer to "is the kernel right": then
neither has to be read whole.

**c. What the kernel is not enough for, today.**
- **`bv_decide`'s axioms.** Each one says: a checker compiled by Lean's compiler accepted a solver's
  certificate. A theorem with any of them rests on Lean's compiler, its code generator and the C compiler that
  built it, not on the kernel alone, and an independent checker refuses it. Today only `push_arm_meets` has
  none (row above). So removing them is not polish: it is what makes part b true.
- **From text to term.** A reader reads source text; the kernel checks the term Lean's elaborator made of it
  (the elaborator is 75,021 lines of Lean, `Lean/Elab`, within the 271,566 of `Lean/`; nobody reads it). Notation can be redefined. The
  guard is to have Lean print the statement back in full, and to keep statements free of local notation.
- **From the object to the statement.** On x86-64 the instructions in the statement are a table a script made
  from the object's listing (layer 5); on AArch64 Lean decodes the words itself.
