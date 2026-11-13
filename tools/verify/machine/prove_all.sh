#!/bin/sh
# Everything the language's compiler proves, from the source to checked theorems, in one command (BLAKE3 #361).
#
#   x86-64 (our machine model, lang/):  hex, merge (and its checked entry), push, merge_sse, add (by its
#       callees' contracts; then with merge_sse swapped in behind merge's contract), merge_steps
#       and ladd and lroot (the tree's levels, another design than the stack: levels/levels.ode; its model first)
#   AArch64 (Google DeepMind's model, arm/; fetched at the commit arm/lakefile.toml names):
#       hex_neon (the kernel), push (the same source function, printed for AArch64)
#   "direct": the compiler's proofs of push and merge again, about the contracts in bytes themselves, with
#       the model's own contracts out of the way (direct_fn.py).
#   "hash-tried": not a proof. The source function `hash` (the whole one-shot hash), run by the language's
#       meaning with each kernel as its contract, against Hash.byteContract (spec/HashContract.lean: "the 32
#       bytes at out become the specification's BLAKE3 of the message") on the test vectors' 35 lengths.
#   Contracts that name no machine (spec/HexContract.lean, PushContract.lean, MergeContract.lean): "any-machine"
#       is the four x86-64 theorems (hex, push, merge, add); "hex_neon" and "push-aarch64" end with the two
#       AArch64 ones (hex, push).
#
# Each line of the result is one function: what Lean checked, and how long it took here.
# Needs python3, cc or clang, llvm-objdump (OBJDUMP), lake (elan). AUDIT=1 also runs the audits (minutes more).
# The steps run side by side, each chain in a copy of lang/ of its own (prove_all.py says how, and what
# "generated" checks); SERIAL=1 runs them in place, one after another.
here=$(cd "$(dirname "$0")" && pwd)
exec python3 "$here/prove_all.py"
