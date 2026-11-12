# The language and its prover: what they are for

Decisions of Sam Shackleton's, November 11, 2026, written down for whoever works on this next. The
state of the code is in `../README.md`; this file is the intent. BLAKE3 #361 is the issue.

## The aim

Very fast code, a specification a person can read in one sitting, and a machine-checked proof that the
bytes that run meet it: the right result, only valid memory accesses, no branch or address that depends
on a secret. For every instruction that can execute, checkable by a skeptical stranger.

## Who checks: Alice finds bugs, Bob should be able to verify (Sam, November 12)

The language is called **Ode** from here on (Sam, November 12; the files are `.ode` already).

A deployment to expect, learned from our own practice: **Alice**, who provides the code, runs the prover to
*find* bugs, fixes them or reports them; **Bob**, who uses the code, verifies nothing and relies on Alice.
That is where blake3-servil-core stands today: its maintainer checks none of these proofs and has had one
finding from them (`Hash::to_hex` was not constant-time; fixed for 0.9). That use is real and worth having.
It is not the goal. The goal is that Bob can verify **for himself**, as cheaply as possible:

a. **What Bob must read is minimal** (or what the friend, colleague or agent he trusts must read): the
   contract, the specification, what meeting a contract means, the machine, and Lean itself as far as his
   statement reaches and no further. `LAYERS.md` counts it, Lean included.
b. **Checking the proof is fast.**
c. **Checking is automatic, the default in normal conditions:** if Bob builds from source, the proof is
   checked in that build, and the build fails if it does not check.

**Tried (November 12, `build-check/`):** a Rust crate whose build script has nanoda check Lean's export of
`push_arm_meets` (5,061 declarations; 1.4 s on an Apple M6 with the checker optimized, 11.8 s as Cargo builds
build scripts by default), compares the checked statement with the text read, and assembles the instruction
words *from the checked theorem*: the linked bytes have no other source. Changed words, sizes and statements
fail the build. Its README lists what that does not yet show.

What (c) asks of the system, beyond that trial: a checker that a build can run without Bob installing Lean (an
independent checker reading exported proofs is the candidate: nanoda is a Rust library); proofs with no axiom
beyond Lean's three (an independent checker refuses `bv_decide`'s; only `push_arm_meets` qualifies today);
statements about the bytes the build links, not about a table made from a listing (true on AArch64, not yet
on x86-64); and a check time a build can bear.

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

Not yet in this shape: the hash.

## A function calls another by its contract, and by nothing else

(November 12.) `add` is the step the hasher takes when a chunk's value arrives: `push`, then `merge` down
to a target. Its proof uses of the two callees their theorems `Abi.Meets … contract` and nothing of
their code:

- **At a call** the caller shows what the callee's contract asks, of the state at the callee's first
  instruction: the arguments, the return address on the stack, the stack the contract may use (a part of
  the caller's frame: the compiler's frame is its own needs, 8 bytes, and the largest budget of a callee),
  the pieces apart, `accepts`, `requires`. All by the tactics already there.
- **At the return** the state is known only by what the contract promises: the registers a callee
  keeps, `ensures`, every byte outside the callee's stack and what it may modify as it was. What holds
  of the new memory is said again: the frame's own cells (the compiler knows them), what the source
  says is kept (`keep Cv.At(key, k)`, by the convention's `Cv.At.frame`), and the bytes outside the
  caller's own frame and pieces. Then the run goes on.
- **The stack lent is the caller's again.** No instruction maps or unmaps memory, so after any run the
  same addresses are the program's (`one/Dom.lean`, `steps_dom`, proved once over the model's
  instructions). `Abi.Meets` did not have to say it.
- **The program** of a caller is its instructions with its callees' (`gen_code.py --with`), and a
  callee's theorem holds in it (`Abi.Meets.mono`, `Code_add.has_push`).

What the source gives for a call: which code stands behind the contract, once at the top
(`callee merge at 0x60000 meets Merge.contract by Proof_merge.merge_meets budget 256`); and at the call
what the contract is stated for besides the arguments (`with k; (new :: cvs)`) and what is kept across
it. `add`'s whole source is ten lines.

**Swapping an implementation** (`./swap.sh`): `merge_sse` is another `merge` (always the SSE4.1 kernel;
77 instructions) proved to meet the same `Merge.contract`. With that one `callee` line changed, `add`
is proved again from its source: 4 of the generated proof's 147 lines differ (two names, twice). This
is what a maintainer gets: change the code behind a contract, prove the new code against the contract,
and every caller's proof stands as generated.

Examples belong to a contract (`Example_merge.lean` for `Merge.contract`): every function that meets it
is tried on them, `merge_sse` as `merge`. `add`'s examples run through its calls (a few hundred to a
thousand instructions); to the source's meaning, when blame is asked, a call is the callee's own source.

**A loop that calls** (`merge_steps`): `merge` a third way, one level at a time, each turn a call of
`merge` with a target one less than the count. Its invariant is `merge`'s own; a turn's proof is the
call rule and three lemmas about the specification (merging to a target and then to a smaller one is
merging to the smaller one). The generator needed nothing new for it but to let a call stand in a
loop's turn: proved on its first run, 38 instructions, its examples through up to 30,592.

**Stack budgets add up, and so a contract's budget says who can implement it.** `merge_steps` does what
`Merge.contract` says, word for word, and cannot meet it: the contract gives 256 bytes of stack, and a
function that calls `merge` needs `merge`'s 256, a return address and its own frame. Its contract
(`MergeSteps.contract`) is the same text with 512. A budget is part of what a caller relies on, so it
belongs in the contract; but it is the one line of a contract that depends on how the function is
built. To think about: a budget stated as "what the code needs", derived, with the contract naming it.

**A call's result** (`return merge(…)`, `x = f(…)`): to the caller it is a value of which the callee's
contract says what it says (`returns`). `add` returns `merge`'s count, and `Add.contract` says so.

Not yet: calls under conditions; the budget read from the callee's contract instead of written beside
it; the callee line generated from what was built.

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

## Two architectures: contracts that name no machine

A contract is written once, of bytes at addresses, and names no machine; each machine model says once
what it means for its code to meet such a contract. Done for `push` and for the kernel `hex` (November
12), by hand where the compiler does not yet do it. For `push`:

- **`spec/Contract.lean`** (read once): `Bytes.Layout` (a size, and what it means for a list of bytes to
  hold a value), `Bytes.Piece`, `keeps` / `turns` / `fills`, `Bytes.Contract` (arguments, what is
  accepted, the pieces read and updated, what is returned). No memory and no machine in it.
- **`spec/StackBytes.lean`**: the data. `Cv.bytes`; `Stack.Holds b cvs` (1792 bytes: the count in eight,
  24 not used, the values oldest first, the rest not used; at most 55).
- **`spec/PushContract.lean`**: `Push.byteContract`, seven lines, the words of `Push.contract`.
- **x86-64** (`lang/AbiBytes.lean`, read once): `Abi.ofBytes c stack` reads a `Bytes.Contract` for our
  model (a piece holds when the bytes memory has at its address are bytes of which its statement holds),
  and `Abi.Meets` applies as before. `push_meets_bytes` (`Meets_push_bytes.lean`).
- **AArch64** (`arm/ArmAbi.lean`, read once): `ArmAbi.spec c` reads it as a specification of Google's
  logic (a piece is owned bytes of which its statement holds; arguments in X0 to X5).
  `push_arm_meets` (`arm/PushBytes.lean`).
- Both codes are printed from the one function `push` of `hasher.ode` (`odec.py … aarch64-fn` is the
  second printer, a trial for straight-line functions).

What a reader reads (`#reading_list`, lines):

| | `push_meets_bytes` (x86-64) | `push_arm_meets` (AArch64) |
|---|---|---|
| shared by both: the contract and its data (`Contract` 28, `StackBytes` 17, `PushContract` 8, the specification's types 3) | 56 | 56 |
| what meeting a contract means on this machine | 76 (`Abi` 57, `AbiBytes` 14, 5 small) | 21 (`ArmAbi`) |
| the machine model | 343 | 6,113 (Google's, shared with their Signal work) |
| the code | 31 | 3 (the words; Lean decodes them) |
| total | 508 (`push_meets`, in the model's own cells: 480) | 6,193 |

Of what is written for `push` itself a reader reads eight lines, once, for both architectures. The
other statements in this form: `hex_meets_bytes` 543 lines and `hex_neon_meets` 6,180 (43 shared);
`merge_meets_bytes` 866; `add_meets_bytes` 931. Each x86-64 list is 28 to 30 lines longer than with the
model's own contract (`Contract` and `AbiBytes` beside `Abi`): the price of the shared half until
`Abi.Contract` itself gives way.

For `hex` the same: `spec/HexContract.lean` (`Hex.byteContract`: the 64 bytes at `out` become `Hex.text`
of the 32 at `hash`), `hex_meets_bytes` on x86-64 (`Meets_hex_bytes.lean`; with what an observer sees, as
`hex_meets`) and `hex_neon_meets` on AArch64 (`arm/HexNeonBytes.lean`). So the one thing meant for the
library has one contract, in one file, for both architectures. (The observer's half is still stated per
machine: `Abi.MeetsQuietly` here, `hex_neon_quiet` there.)

What it took, and what it shows:

- On x86-64 the existing proof was kept: `Stack.At_iff_bytes` (`StackAsBytes.lean`, by hand) shows the
  model's own predicate is the statement in bytes, so `Abi.ofBytes (Push.byteContract …) 64 =
  Push.contract …` and the theorem carries over. What a data structure owes is one fact,
  `Abi.Layout.Opens L N` (`BytesAt.lean`: the layout in bytes `L` opens as the model's layout `N`; proved
  for plain bytes, a chaining value and the stack); `keeps`, `turns` and `fills` follow.
- **The next step, exactly:** the model's own contracts (`Spec_push.lean`, `Spec_merge.lean`,
  `Spec_add.lean`, `Spec_hex.lean`) are now a second text of what `spec/` says, tied to it by an equation
  Lean checks. They should go: the source names the contract in bytes and the stack budget
  (`meets Push.byteContract(...) stack 64`), the generated theorem is about `Abi.ofBytes` of it, and where
  the generated proof unfolds the contract it adds `Abi.ofBytes`, `List.map` and the `Opens` facts, after
  which the pieces are the model's and the proof goes on as today. **Tried, and it works:**
  `direct_fn.py` makes exactly that substitution in the generated proofs of `push` and of `merge` (its
  loop and its kernel calls included), and Lean accepts both (`Direct_push.push_meets`,
  `Direct_merge.merge_meets : Abi.Meets … (Abi.ofBytes (Merge.byteContract …) 256)`), with no proof text
  written. What is left before the model's own contracts can be deleted: callers (a callee's contract is
  named in the caller's proof), the examples and the checked entry (`#checks`, `#pieces` read the model's
  contract), and the audits that change `Spec_merge.lean`, which move to `mutants_spec.py`'s way (a copy
  of `spec/`).
- On AArch64 the compiler's proof is against cells (their tactics alone, nothing written), and a file
  by hand (`PushBytes.lean`, 144 lines) goes from the bytes to the cells and back (their rule
  `subroutine_ok_refine_frame`). The lemmas
  about lists of bytes (`spec/StackBytesLemmas.lean`: room for one more; the stack with one more) are
  shared by both architectures in principle; x86-64 does not use them yet.
- **The stack budget is not in the contract**: it differs by machine and by compiler. `Abi.ofBytes` takes
  it; Google's logic gives the code its own stack without a number. So "a budget decides who can
  implement a contract" (above) becomes a property of a machine's reading, not of the contract.
- A piece the function does not change: on our model the frame clause says so; in their logic the
  specification names the piece's bytes and gives the same bytes back.
- `merge` and `add` have their contracts in this form too (`spec/MergeContract.lean`), met on x86-64
  (`merge_meets_bytes`, `add_meets_bytes`, `Meets_merge_bytes.lean`: by the same two lemmas about the
  stack and a chaining value as pieces, a few lines each). `Merge.merged` there is `Merge.result` here,
  word for word, until the audit that names `Spec_merge.lean` is moved.
- Each of the four, read for x86-64, comes with its theorem that it can be used (`UsableBytes.lean`).
- The kernel `hex` in this form is what the candidate for the library holds: branch
  `candidate/sam-hex-proved` of the fork, folder `tools/verify/hex` (what the two theorems need and
  nothing else: 23 Lean files for x86-64, 12 for AArch64, three shared), made from this folder by a script.
- Not done: `merge` and `add` on AArch64 (loops and calls in the second printer and its proof generator,
  and a compression kernel with a contract there); the compression kernels' contracts in this form; the
  bytes-to-cells step generated; "quietly" stated once for both machines.
- An observation from the AArch64 proof: `push` never looks inside `Cv.bytes` (it copies 32 bytes), so its
  contract holds for any encoding of a chaining value. Only a function that computes with the value pins
  the encoding; a contract's data can be as abstract as the code allows.

## The function a user calls: `hash`, its contract, and a trial short of proof

The statement a user wants is about the function they call. It is written (`spec/HashContract.lean`,
`Hash.byteContract`, naming no machine): with the `len` bytes of a message at `input` and the
specification's `IV` at `key`, the 32 bytes at `out` become `Blake3.hashBytes` of the message (C2SP's
`Blake3.hash`), and the message and the key are unchanged.

**It is not proved.** `hash` in `hasher.ode` is the whole one-shot hash (815 of the 1,258 x86-64
instructions the language's code compiles to; the functions proved above are 306). What exists is the
first of the blame verdicts, one level up from the machine: `HashTry.lean` runs the *source* by the
language's meaning (`Sem.lean`), each kernel being what its contract says (one block, or many inputs of
many blocks), on the 35 lengths of the BLAKE3 test vectors and three platforms: 104 examples meet the
contract, none fails. `mutants_hash.py` audits that test: four wrong sources (a chunk's end not marked;
the root not marked; a parent merged at the wrong count; the counter not advanced) are each refuted by 9
to 27 of 27 examples, and the unchanged source meets all.

What that is worth: a wrong source or a wrong contract for `hash` is likely to be seen in seconds, before
any proof is tried, and the contract a reader would read exists to be argued with. What it is not: a
statement about every message, or about the assembled code, or about the kernels' own code (the two
one-block kernels are proved elsewhere here; the many-input kernels' contracts are assumed by this test,
and above 32 KiB on AVX-512 the source calls kernels whose contracts are not written).

A fault found on the way, for whoever runs sources as tests: a kernel's contract given as a function
from memory to memory (`Try.compress`) was computed again at every byte read, since Lean compiles a
definition that returns a function as one of more arguments; sixteen compressions took minutes. Computed
once when the kernel is called (`compressNow`), the 104 examples take two and a half minutes.

## Two designs of one thing, side by side: the stack and the levels (Sam, November 12)

`../levels/` holds the tree of chaining values in a second design (Sam's, from earlier work on BLAKE3):
a parent written to memory of its own, and no pair hashed while it may be the root's. It is there to
learn what two designs of one thing share in this system, and it may one day be the better `merge`.
Found so far (its README has the numbers): the user-facing contract and its trial are shared whole; 137
of about 200 lines of contract reading are shared; the layout and the functions' contracts are not; the
levels' contracts speak of the specification's tree itself, where the stack's speak of `mergeTo` and
leave the tree to other theorems and the caller. **Rule taken from it: prefer the contract that states
the specification's own object** (the tree over the chunks), **and a design whose caller computes
nothing for it.** Next: the levels' theorems (`ladd_meets`, `lroot_meets`, and the algorithm's), to
compare the proofs.

## The coder decides, and can predict (Sam, November 12)

Sam's rule, from the trouble she and Devon have with Rust's layout, inlining and whole-program optimization
making benchmarks unpredictable. At the fork between "the compiler makes this better for the coder, if it
can" and "the compiler makes *whether* this is better predictable and controllable by the coder", **Ode
takes the second.** More to think about for the coder is accepted; the work may be reduced only where the
result stays predictable and controllable.

Already so: nothing is optimised (what is written is what is emitted); `def` is the coder's inlining and
`reg` the coder's choice of registers; a change to one function changes no other function's code (checked
when `hash`'s stack went onto a boundary: the other eight functions' text was the same to the letter).

To keep, as tests: the same source and target give the same bytes; a function's bytes depend on that
function's source alone.

## Calls between Ode functions need not be C's (Sam, November 12)

Sam's direction: as the proofs remove run-time checks and dynamic allocation, let them remove the calling
convention between Ode functions too, down to a `jmp`; the C convention stays where C or Rust calls in.

What the convention costs in the code as compiled today (`push` 9 of 26 instructions, `merge` 32 of 88,
`merge_steps` 26 of 38, `add` 30 of 32: saving and restoring six registers, moving parameters to homes and
arguments to the convention's registers, `call`, `ret`; part of that is this compiler giving every variable
a home in a saved register, not the convention itself).

What can replace it, each piece stated in the callee's contract and proved, none assumed:
- **Where the arguments are** and **what the callee may change**: per function, chosen by the coder, in
  place of one rule for all. The theorems already say what is changed; they would say it of registers too.
- **No frame of its own**: with no recursion (needed anyway for an exact memory bound) the calls form a
  tree, and every function's buffers can be places in one block the coder lays out. Then the stack pointer
  never moves, the whole tree's memory is one piece of the entry's contract, and "exactly the memory this
  call needs" and "where every buffer lies, by line and page" are the same statement.
- **The way back**: a function with one caller is entered and left by direct jumps; a tail call is a jump
  already; a function with several callers needs a return address, which can be in a register.

To weigh before building (not measured): processors predict `ret` from `call` by a stack of their own, and
a return by an indirect jump gives that up where a function has several callers; Intel's shadow stack and
Arm's pointer authentication assume the pairing; profilers and debuggers find callers by the frame's
conventions (unwinding tables can say it without code). The System V entry stays, as a wrapper, for every
function C or Rust calls. In the proofs a callee is already used as "from its entry, for any return address,
the continuation runs from a state the contract describes": that form fits a jump as it fits a call.

## Memory: boundaries, lines and pages; nothing allocated (Sam, November 12)

Sam's direction. The cost of memory is in how it is touched (cache lines, pages, what is shared), never in a
count of bytes. `alloc`/`free` were fixed before virtual memory existed; Ode targets 64-bit machines with
virtual memory and should say memory in those terms: a boundary with every use, lines and pages where the
programmer wants them. And no dynamic allocation: the memory a call needs is set aside beforehand, exactly,
and that is proved.

**Where Ode stands.** It has no allocator and gets none. A function's memory is its frame's buffers (fixed
sizes) and the pieces its contract names, which are the caller's. What a call may touch is already a
theorem's content: the contract's pieces and a stack budget (`Abi.ofBytes c stack`), nothing else.

**Done (November 12):** `buf NAME[BYTES] align BOUNDARY` (a power of two: 64, 4096, ...). A function with
such a buffer sets its frame on the largest boundary and keeps the caller's stack pointer in the frame; a
function without one is assembled exactly as before (checked: the same text for all nine functions of
`hasher.ode` before `hash`'s stack was put on a 64-byte boundary).

**To do, in this order:**
1. A boundary in a contract's pieces (`Bytes.Layout` gains one; a caller shows an address is on it), so a
   kernel may rely on it and "this piece is N whole lines" can be said.
2. The stack budget derived from the code, for the whole tree of calls, and shown reached by an example:
   then "exactly the memory this call needs" is a number in the theorem, not an upper bound written by hand.
3. **The coder lays memory out; the compiler does what is written or refuses** (Sam, November 12: not "the
   compiler arranges it and reports"). Proposed, for Sam to decide:
   - `line` and `page` are names the source may use in sizes and boundaries. A target says what they are
     (64 and 4096 bytes on our x86-64 machines; 128 and 16384 on Apple's; on other AArch64 systems the
     page is the operating system's choice, 4, 16 or 64 KiB, so there the build must be told). A contract
     that says "on a line" is one text for every machine, with the target's number.
   - Buffers lie in the order written, each on the boundary written. Nothing is reordered or padded
     unasked.
   - The coder states what the layout is for, and the compiler checks it and stops if it is false:
     `same line: a, b`; `apart lines: x, y`; `within pages 1: st, block, cv`. Different targets may need
     different layouts: then they are written per target, not derived.
   - The compiler prints the map (every buffer's offset, line and page, per target) as a record of what
     was written, to read and to compare between versions.
   Found with `hash2`, to be fixed by the coder's ordering under this rule: its 3520 bytes of levels,
   mostly never touched, lie between the buffers every call touches, and the frame is 5232 bytes.
4. Where code lies is layout too: a function's own boundary and the order of functions in the object, by
   the coder (today every function is on 16 bytes, in source order).
5. Where a function needs more than fits a frame well: a workspace the caller passes, a piece on a page
   boundary.

## No code the proof shows is never reached

(Sam, November 12.) A check that the proof shows can never fail is dead code: it costs instructions, it is
one more thing to read, and keeping it would say we do not believe the proof. `merge` had a trap for a
stack of fewer than two values; its contract and invariant exclude that, so the trap is gone (93
instructions became 88). Where a check is wanted because a caller is not proved, it is the checked entry's.

The audit that makes each instruction a no-op in turn (`mutants_code.py`) finds what else the contract
does not need: it accepted the removal of `mov rax, 0` from `push` and `add` (their source returns
nothing) and of a move in `add` of a value already in place. The first is gone: a function whose source
returns nothing sets no result. The second wants the compiler to know what a register holds.

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
November 12 `prove_fn.sh` refuses a contract none of whose examples meets what it requires (6 s), and a
contract with no theorem that it can be used: `Abi.Contract.Usable` (in `Abi.lean`, four lines to read)
says some stack and memory give the contract all it asks, and `Usable.lean` proves it of each contract
(`Merge.usable`, `Push.usable`, `Add.usable`, `Hex.usable`) on the plainest memory there is: an empty
stack, zeroes. So the two together: a theorem that the requirements do not contradict one another, and
examples that are worth something, run through the code and compared with the contract. Not yet: the
examples' own states proved to be what they are meant to be (their builders are tested, not proved).
The invariant needs no witness of its own: `enter` proves it is reached.

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

### The lists on November 12, in layers

Lines a reader must read to know what each theorem says (`#reading_list`), by who else reads them too:

| theorem | all | the machine and what "meets" means | the specification | the data in memory | this function: contract, instructions |
|---|---|---|---|---|---|
| `hex_meets` (x86-64) | 513 | 446 (machine 336, `Abi` 66, observer 40, 4) | 5 (`HexText`) | 6 | 8, 48 |
| `push_meets` | 481 | 417 (machine 343, `Abi` 68, 6) | 6 | 17 | 9, 32 |
| `merge_meets` | 838 | 417 | 112 (BLAKE3 100, `mergeTo` 9, 3) | 17 | 15, 102 and the two kernels' 175 |
| `merge_sse_meets` | 827 | 417 | 112 | 17 | 15, 91 and 175 |
| `add_meets` | 902 | 417 | 112 | 17 | 15 (`Add.contract`, `Merge.result`), 39 and its callees' 127 and 175 |
| `hex_neon_bytes_ok` (AArch64) | 6,126 | 6,106 (Google's trusted model) | 5 (`HexText`) | | 12, 3 |
| `hex_neon_quiet` | 7,677 | 7,629 (the same, and 1,400 of system calls that `execInst` carries) | | | 46 (our observer), 2 |

What the table says:

- **A caller costs its reader its own contract and instructions, and no callee's contract.** `add_meets`
  is `merge_meets` and 64 lines: `Add.contract` (10), `add`'s instructions (39), `push`'s (29), less
  `Merge.contract` itself, which `add`'s reader never reads (only `Merge.result`, which `Add.contract`
  names). `Push.contract` is not on the list at all. An internal contract is read by maintainers.
- **Instructions are most of what is specific to a function**, and they are the lifter's reading of the
  object, not checked by Lean on x86-64. On AArch64 they are 32 words in one line: Google's decoder is
  in the model. That is the case for a decoder of our own, or for their kind of model, on x86-64.
- **Google's model is twelve times ours to read, and it is not ours alone**: the same 6,106 lines stand
  under their Signal verification. Ours (417 lines) stands under nothing but this library. A reader who
  has read theirs for another reason reads 20 lines for our theorem.
- The kernels' instructions (175 lines) are on every list that reaches a kernel: with the kernels
  proved against contracts of their own (they are: `Kernels.lean`), a caller's list should name the
  kernel's contract and not its instructions. Not done: `Code_merge.prog` holds them, so they count.

## Share what can be shared

Machine models are trusted, so they are worth sharing with everyone who needs one. For AArch64 use the
model of Google DeepMind's AlphaProof Code (`google-deepmind/code-verification`, `arm64-semantics`:
Apache-2.0, tested against Sail, Unicorn and Arm's ASL), and offer upstream what we must add to it.
