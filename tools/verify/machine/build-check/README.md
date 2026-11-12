# A build that checks the proof of the code it links (a trial, November 12, 2026)

The aim (lang/DESIGN.md, "Who checks"): a user who builds from source verifies for himself, by default,
without installing Lean; the build fails if the proof does not check.

`crate/` is a Rust crate whose build script:

1. unpacks `proof/push_arm_meets.ndjson.gz`, Lean's export (lean4export) of the theorem `push_arm_meets`
   and everything it depends on: 5,061 declarations, 33 MB (5.1 MB packed);
2. has **nanoda** check every declaration (an independent checker of Lean proofs, written in Rust, a
   build dependency pinned by commit), permitting Lean's three axioms and no other;
3. has the checker print the theorem's statement back and compares it, to the letter, with
   `proof/push_arm_meets.statement.txt` (four lines: the text a reader reads);
4. takes the eighteen instruction words from the checked definition `push_arm_code` that the statement
   names, and assembles **those** as the function `b3l_push`. The linked bytes have no other source.

`cargo test --release` in `crate/` on an AArch64 machine does all of it and then calls the function.

## Measured

| | |
|---|---|
| export (workhorse, Lean 4.34.1) | 2.0 s |
| nanoda's own program on the export (Threadripper 7975WX) | 3.9 s on one thread, 2.9 s on sixteen; 0.6 GB |
| the crate's build on an Apple M6, checker optimized | check 1.4 s (four threads); `cargo test` from nothing 8.1 s; a rebuild 1.9 s |
| the same, build script unoptimized (Cargo's default) | check 11.8 s; `cargo test` from nothing 16.7 s |
| the function's test | passes |

Controls (`controls.py` on the export; `build-trial.sh` on the crate):

| change | result |
|---|---|
| unchanged copy | accepted |
| the first instruction word, aa0003f0 as aa0003f2 | refused by the checker (the build fails) |
| the stack's size, 1792 as 1794 | refused |
| the stack's capacity, 55 as 257 | refused |
| the literal 32 as 257 | refused |
| the statement file names the arguments in another order | the build fails: "the theorem that checks is not the statement" |
| the export of `hex_neon_meets` (72 `bv_decide` axioms) | refused: "export file declares unpermitted axiom" |

A first run of the controls was vacuous (the changed number was already in the export, and the parser
refuses a literal it has twice): `controls.py` now picks a number the export does not hold.

## What this does not yet show

- **One function, one architecture**: the only theorem whose proof has no axiom beyond Lean's three.
- **The definitions the statement names** (`Push.byteContract`, `ArmAbi.spec`, Google's
  `subroutineOk`, ...) are checked as the export has them; the build compares only the theorem's own
  statement with the text read. The same comparison is owed for each definition of the reading list.
- **5 MB of proof for eighteen instructions.** Nearly all of it is Lean's library and Google's model,
  which every theorem of a crate would share; what a second theorem adds is not measured.
- **The checker is a build dependency**: 31 crates in the lock file with it. And Cargo builds build
  scripts unoptimized unless the top crate of the build says otherwise (the 11.8 s above).
- **One checker in the build.** Lean's own kernel accepted the same proof where it was made; a second
  independent checker in the build is not tried.

## Again

    bash setup.sh WORKDIR                 # lean4export for the lab's Lean, and nanoda
    python3 trial.py WORKDIR ARMLAB       # export, check, time
    python3 controls.py WORKDIR ARMLAB    # the changed copies
    bash build-trial.sh crate OUT         # the crate as it is, then two changed copies (AArch64)
