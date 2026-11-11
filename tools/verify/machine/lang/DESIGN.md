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

State on November 11: `merge_meets : Merge.statement` is proved (`Meets_merge.lean`), from the compiler's
theorem; that last step (70 lines) is still written by hand and is the generator's to write. The clauses
`requires` and `ensures` in `hasher.ode` now say the same thing twice and are to go; `invariant`,
`decreases` and the hints stay in the source.

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

Not built yet (November 11): verdicts 2 and 3. Today the audit says "rejected" with a Lean line number.

## A contract must be able to hold

A theorem "from every state where the `requires` clauses hold ..." is true of any code if no such state
exists. (Shown: `requires target >= 1` and `requires target < 1` together are accepted today.) So every
contract comes with a proved witness: a state in which its `requires` clauses hold, and that state run
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
