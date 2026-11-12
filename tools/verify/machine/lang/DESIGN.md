# The language and its prover: what they are for

Decisions of Sam Shackleton's, November 11, 2026, written down for whoever works on this next. The
state of the code is in `../README.md`; this file is the intent. BLAKE3 #361 is the issue.

## The aim

Very fast code, a specification a person can read in one sitting, and a machine-checked proof that the
bytes that run meet it: the right result, only valid memory accesses, no branch or address that depends
on a secret. For every instruction that can execute, checkable by a skeptical stranger.

## There is one way to do it

- One implementation language, made for this job, for word-level code and for kernels alike. No
  hand-written Rust, no second generator, no second prover.
- Lean is the language of specifications and proofs. It is not the implementation language.
- The compiler does not have to be trusted or proved. It writes, beside the assembly, the theorem the
  source's contract makes and its proof, about the assembled bytes; Lean checks it. A compiler bug is a
  proof that fails.
- Contracts are in the source, in the language's own expressions: `requires`, `ensures`, and on a loop
  `invariant` and `decreases`. Where a property is mathematical a clause names a Lean definition.

## Every function comes with its statement in Lean

(Sam, November 11: "if we're going right-hand path, then let's go hard right. Let's make the translator
the identity.") Nothing checks that a statement means what its author intended, so nothing should stand
between what the author wrote and what Lean proved. A translator from clauses in the source to a Lean
statement would be such a thing: trusted, or one more text to read.

- A function's statement is written in Lean, by hand, in a file of its own that holds nothing else
  (`Spec_merge.lean`: `Merge.statement`). The source names it. The reader reads that file.
- Statements share one small vocabulary, read once (`Abi.lean`): `Abi.Meets prog entry contract`, where a
  contract is the arguments, the stack the function may use, the regions it speaks of, `requires`,
  `ensures` and `modifies`. Registers, frames and the calling convention are in that one definition, not
  in every statement.
- A statement speaks the specification's language (`Blake3.mergeTo`, `Blake3.CV`), never definitions made
  for the proof's convenience. What is made for the proof stays internal and off the reading list.
- What the compiler writes about registers and frames (`Pre`, `Inv`, `Post`), the loop's invariants and
  the prover's hints are internal: Lean checks that they give the statement.
- A function no user calls needs no reader at all: its statement is an interface between two proofs.

State on November 12: done for `merge`. Its contract is `Merge.contract` (`Spec_merge.lean`); the compiler
writes `Proof_merge.lean`, whose last theorem `merge_meets` says: for all arguments,
`Abi.Meets Code_merge.prog 0x60000 (Merge.contract ...)`. Nothing is translated.

### Words

- A **contract** (`Abi.Contract`) is what a caller owes a function and what it gets.
- A **statement** is a proposition: something that may be true or false, such as "the function at this
  address of this program meets this contract, whatever its arguments". A reader reads statements.
- A **theorem** is a statement with a proof Lean has checked. Nobody reads proofs.
- A **lemma** is a theorem made to be used in other proofs. Nobody need read those either.

### What a reader reads, and where it is

| File | What | Read |
|---|---|---|
| `Abi.lean` | what it means to meet a contract | once |
| `Spec_THING.lean` | a data structure's layout in memory, or a function's contract | per thing |
| the specification (`c2sp/BLAKE3`) | BLAKE3 | once |
| `one/Machine.lean` | the machine | once |
| the last line of `Proof_FN.lean` | which program and entry the theorem is about | per function |

A `Spec_` file holds definitions only: no theorem, no tactic, nothing made for a proof's convenience. It
imports `Abi`, the specification and other `Spec_` files, never code or proofs, so it can be written and
read before the code exists. `#reading_list FN_meets` is the check that this table is the whole of it.

### What a developer writes

1. The contract, in `Spec_FN.lean`. Its stack is a round budget, not the frame's size: the compiler's
   frame may change without the contract changing.
2. The code, in the source, with `meets CONTRACT(...)`, `uses FILES`, `leave by LEMMA`, and for a loop
   the `invariant` clauses and `decreases` (`prove_fn.py`'s first lines give the whole syntax).
3. Lemmas, in Lean: for a data structure, once (`StackLemmas.lean`: what its holder may read at once,
   that it depends on its own bytes only, how it is taken apart into the cells code reads and put together
   again); for the function (`Lemmas_merge.lean`: what carries the invariant across a turn, and what
   gives `ensures` when the loop ends).
4. `./prove_fn.sh FN`, then `python3 mutants_fn.py`.

Rules that kept it simple:

- **One view of the data.** The invariant speaks in the contract's own terms (`Stack.At`, `Merge.result`).
  A second representation for the proof's convenience doubled the lemmas and needed a bridge; it is gone.
- **The invariant says "what is left to do gives the whole result"**, so one lemma carries it across a turn
  and one closes it at the end.
- **What the contract requires of the arguments alone is known at every turn**; the source does not
  repeat it. What it requires of memory at entry is forgotten once the loop is entered: only the
  invariant speaks of memory now.
- **Conventions in place of declarations.** A clause `Name(args)` alone says `Name` of memory; its lemmas
  are `Name.cells` and `Name.frame`; a lemma's memory is `m`.
- **Every hypothesis of a lemma the source names is of a kind one tactic settles** (`mem_auto`): a fact at
  hand, a cell of the memory after some writes, a region still owned, bytes no write touched, arithmetic.
  Values a lemma speaks of are found by unification, never guessed.
- **A callee's oddities stay in its contract.** (The SSE4.1 kernel reads its flags from a wider register
  than the AVX-512 one; the lemma for its call asks the caller to show they are small, and then states
  its result as the other's. The source needs no hint.)
- **An audit begins with a control**: an unchanged copy, forced to check again, must be accepted.

`hex` is in this shape since November 12: `Spec_hex.lean` (13 lines: `Hex.char`, `Hex.text`,
`Hex.contract`) and `hex_meets : ∀ out inp, Abi.MeetsQuietly Code_hex.prog 0x50000 (Hex.contract out inp)`:
the contract met whatever the hash is, and one list of what an observer of time and cache sees, the
same for every hash. Its reader reads 513 lines, of which 67 are `hex`'s own (the contract 13, bytes in
memory 6, the 45 instructions 48). Its proof has two layers: the kernel's theorem about vectors, which
the compiler writes (`Proof_hex.lean`), and 40 lines by hand from vectors to the contract's bytes
(`Meets_hex.lean`; `BytesLemmas.lean` is written once for all code that moves bytes sixteen at a time).
The hand layer is the next thing for the compiler to write: it is the same for any kernel whose
contract speaks of bytes.

`push` is in this shape since November 12 (`Spec_push.lean`, 9 lines; `push_meets`, 13 s from the
source): the first function with no loop, proved as one straight piece from the entry to the return
(the source gives `enter know LEMMA`, `enter open LEMMA as names` and `leave by LEMMA`; no invariant).
Its contract accepts only a stack with room (`cvs.length < 55`): that speaks of memory, so no entry can
test it from the arguments, and the tool says so: a caller shows it. The test the source had for it
is gone (no proved caller reaches it). A function that calls nothing is its own program: `push`'s
reading list (480 lines) has no kernel in it.

Not yet in this shape: the hash; a function that calls another of ours by its contract.

## A requirement is stated once; proved where it can be, tested where it cannot

(Sam, November 12, after E's guards and auditors and Goose's index types and `checkfree`.) A type is a
predicate. Proving it of a value and testing it of a value are two ways to enforce one statement, and the
programmer should write that statement once.

- What a function requires of its **arguments themselves** is the contract's `accepts`. What it requires
  of **memory** is in its pieces (below): no code can test that a pointer leads to bytes the program owns.
- At a call, `accepts` is **proved** by the caller's own proof (then no code is spent on it), or
  **tested**: the function's *checked entry* tests it, refuses loudly if it fails, and otherwise goes on
  to the function. Never assumed.
- Nobody writes the test or its proof. `#checks CONTRACT` (`Checks.lean`) reads the comparisons out of
  the contract's `accepts`; `check_fn.py` makes the checked entry's instructions from them and the proof
  that the entry meets `CONTRACT.checked refused` (`Abi.lean`: where the contract accepts the arguments
  the entry does as the contract says; where not, it returns `refused` and every piece of memory holds
  what it held). Done for `merge`: `Checked_merge.merge_checked_meets`.
- A public function is a checked entry: its callers are not proved. What then remains assumed at the
  boundary is only what no code can test (the calling convention, the pieces of memory), stated in
  `Abi.Meets`.
- Still to build: a proved caller that calls the unchecked entry; a predicate with a decider a programmer
  wrote (today: comparisons of arguments and numbers); the report of every call that fell back to
  testing, and a mark that forbids it inside the library.

### Secrets (a proposal, not yet a decision)

Sam: an attacker may want any value, so there is no class of "secret values"; all values are secret. Then
no branch and no address may depend on any value, except where the contract says so: the principled
conversion of a secret into something an observer may learn is a line of the contract ("what an observer
sees depends only on: the addresses; the input's length; whether the arguments were accepted"), which is
on the reader's list. That is the shape the kernels' trace theorems already have. A test in a checked
entry is a branch, so `accepted or refused` is one such line. `Abi.Meets` has no trace yet.

## A contract speaks of memory in pieces

A contract names each piece of memory once: where it is, and what it holds (`Abi.Piece`, made from a
data structure's `Abi.Layout` by `keeps` or `turns`). From the pieces follow the regions that must be
apart, what must hold at the call, what holds at the return, and what may change; a contract can no
longer give one of those and forget another (the mistake "the key is not said to be apart from the
stack" cannot be written). `Merge.contract` is six lines: `args`, `stack`, `accepts`, `reads`,
`updates`, `returns`.

## Arm: Google's model, and an observer of our own

(Sam, November 11: use the AArch64 model of `google-deepmind/code-verification`. November 12: done for
one kernel, their repository unchanged; `../arm/`.) What we learned by doing it:

- **Their trusted part is enough to state our contracts**: a decoder from the 32-bit words, `execInst`,
  `Step`, and `subroutine_ok` (total correctness with a frame; the stack pointer and callee-saved
  registers kept). Our contract in bytes (`Hex.text`) is a `Spec` of theirs, 6 lines.
- **Their proof library does the stepping** (`wp_init`, `wp_steps`: 32 NEON instructions in seconds) and
  leaves us the arithmetic: eight equalities of 64-bit values, which `bv_decide` closes. Their
  `wp_done` does not hand back what it cannot close; `SepWP.of_eq` (three lines, ours) replaces the
  spatial context by the specification's and leaves the value goals. The compiler's Arm generator
  (`../arm/gen_arm.py`) writes that step and the tactic for the goals; the rest is theirs.
- **One source file, two architectures**: `kernel NAME on aarch64` beside `kernel NAME` in `hasher.ode`;
  `../arm/prove_arm.sh` is to Arm what `prove.sh` is to x86-64.
- **They have no observer** (side channels are outside their scope). Ours is small: what an instruction
  shows is its fetch, the addresses it reads and writes, and where it sends control; it is defined for
  the kinds of instruction our kernels use and says "no account" for the rest. The theorem is the
  textbook one: two machines that differ only in what memory holds and in the vector registers show
  the same. It needs no program logic: each instruction is decoded by the kernel (`decide +kernel`) and
  the facts about it hold by `rfl`. A candidate to offer them.
- **One specification for both architectures**: `../spec/HexText.lean`, no machine in it.

## No code the proof shows is never reached

(Sam, November 12.) A check that the proof shows can never fail is dead code: it costs instructions, it is
one more thing to read, and keeping it would say we do not believe the proof. `merge` had a trap for a
stack of fewer than two values; its contract and invariant exclude that, so the trap is gone (93
instructions became 88). Where a check is wanted because a caller is not proved, it is the checked entry's.

## Pinning the blame

**A failed check must say what is at fault: the code, the contract, the compiler, or the proof. Reliably
and fast. This is one of the main things the system is for.** A verifier that answers only "proved" or
"not proved" leaves a person to find out which, and that is where the hours go.

The system has two executable meanings for every function, the source's interpreter (`Sem.lean`) and
the machine model, and a generator that knows which clause every line of proof came from. So:

1. **Proved.** Lean accepted the theorem.
2. **Refuted by an input.** Run concrete inputs through the machine model. An input on which a `requires`
   holds and an `ensures` fails is evidence nobody has to take on trust. Then run the same input through
   the source's interpreter:
   - the source breaks the contract too: **the code and the contract disagree** (the programmer's);
   - the source keeps it and the machine code does not: **the compiler is wrong**.
3. **The proof recipe failed, at a named clause.** No input refutes it. Report it in the source's
   terms ("invariant 2 is not re-established on the turn's second path"), never as a line of Lean.
4. **Out of time.** Every check has a limit. No answer is an answer of its own kind, never a pass and
   never a refutation.

Built (November 12): verdict 2, as a test by running. `try_fn.py` runs the assembled function in the
machine model on the examples of `Example_NAME.lean` and compares the result with the contract (the tests
are made from the contract itself, read by `#pieces`); on a failure it runs the same example through
the source's meaning and says which is at fault. For `merge`: eight examples in 7 s, before the 90 s
proof. In the audit, 13 of 14 changed instructions were pinned on the compiler's code within 17 s each
(the fourteenth showed a gap in the examples, since filled), and 5 of 12 false statements on "the source
or the contract". `have_by` names the hypothesis of a lemma that could not be shown (a first piece of
verdict 3). Not built: verdict 3 in the source's terms; a refutation as a theorem Lean checks (today it
is a run anyone can repeat); the checked entry tried on examples; the examples' checkers
(`Sample_*.lean`) proved against the layouts, so that a false layout is refuted too (it is not, today).

## A contract must be able to hold

A theorem "from every state where the `requires` clauses hold ..." is true of any code if no such state
exists. (Shown: `requires target >= 1` and `requires target < 1` together were accepted by Lean.) Since
November 12 `prove_fn.sh` refuses a contract none of whose examples meets what it requires (6 s). That is
a test; the aim stays a proved witness: a state in which its `requires` clauses hold, and that state run
through the code with the `ensures` clauses checked on the result. The invariant needs none of its own:
`enter` proves it is reached.

## What a reader must read

- The parts no machine checks are the statements at the top (what is claimed), the assumptions at the
  bottom (the machine model, contracts of things nobody proved, the tools between the bytes Lean reasoned
  about and the bytes that run), and Lean's kernel. Everything between is checked.
- A specification between two proved parts needs no reader: it is the conclusion of one theorem and a
  hypothesis of the other, Lean checks they are the same statement, and it cancels. If it is too weak the
  user's proof fails; too strong, the provider's. It comes back onto the reading list only if the final
  statement mentions its definitions.
- The list is asked of Lean, not kept by hand: `#reading_list THEOREM` (`ReadingList.lean`) gives the
  definitions the statement depends on and the axioms under the proof. Keep that list short, and treat
  its length as a number to drive down.
- Only Lean's three standard axioms. (Today: 547 of `bv_decide`'s as well. They are to go.)
- Lean should read the object's bytes itself. (Today the lifter and llvm-objdump are trusted for that.)

## Share what can be shared

Machine models are trusted, so they are worth sharing with everyone who needs one. For AArch64 use the
model of Google DeepMind's AlphaProof Code (`google-deepmind/code-verification`, `arm64-semantics`:
Apache-2.0, tested against Sail, Unicorn and Arm's ASL), and offer upstream what we must add to it.
