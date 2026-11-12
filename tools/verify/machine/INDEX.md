# What is proved: an index

Written by `index.py`. One row a theorem: what it says (a person's sentence), the contract it is about, what a reader
must read to know what it says (`#reading_list`: the definitions its statement depends on, through every definition
those use), and the axioms its proof rests on beyond Lean's three. The numbers are Lean's.

| theorem | code and machine | what it says | the contract | lines to read | axioms beyond Lean's three |
|---|---|---|---|---|---|
| `hex_meets_bytes` | x86-64, the model written here | the kernel `hex`, as assembled, writes the hexadecimal of the 32 bytes read and changes nothing else; an observer of time and cache sees the same whatever they are | `Hex.byteContract` (spec/HexContract.lean) | 547 in 11 files | 5 (bv_decide) |
| `push_meets_bytes` | x86-64, the model written here | `push`, as assembled, puts a chaining value on the stack | `Push.byteContract` (spec/PushContract.lean) | 512 in 12 files | 90 (bv_decide) |
| `merge_meets_bytes` | x86-64, the model written here | `merge`, as assembled, turns the stack into the specification's `mergeTo` of it and returns its count | `Merge.byteContract` (spec/MergeContract.lean) | 870 in 15 files | 555 (bv_decide) |
| `add_meets_bytes` | x86-64, the model written here | `add` (push, then merge, each by its contract) turns the stack into the merge of the stack with the new value | `Add.byteContract` (spec/MergeContract.lean) | 935 in 17 files | 718 (bv_decide) |
| `Checked_merge.merge_checked_meets` | x86-64, the model written here | `merge`'s checked entry does as `merge` where the arguments are accepted and otherwise returns the refusal, memory as it was | `(Merge.contract …).checked` (lang/Abi.lean, lang/Spec_merge.lean) | 851 in 13 files | 517 (bv_decide) |
| `Proof_merge_sse.merge_sse_meets` | x86-64, the model written here | a second `merge`, on the SSE4.1 kernel alone, meets the same contract | `Merge.contract` (lang/Spec_merge.lean) | 831 in 13 files | 296 (bv_decide) |
| `Proof_merge_steps.merge_steps_meets` | x86-64, the model written here | a loop that calls `merge` by its contract, one value a turn, does what `merge` does | `MergeSteps.contract` (lang/Spec_mergesteps.lean) | 890 in 15 files | 594 (bv_decide) |
| `Proof_ladd.ladd_meets` | x86-64, the model written here | `ladd` (the tree's levels, another design than the stack: levels/), as assembled, turns the levels of the tree over some chunks into the levels over those and one more | `Ladd.contract` (lang/Spec_ladd.lean) | 854 in 14 files | 377 (bv_decide) |
| `Add.keeps_the_tree` | none | on the tree's stack for `m` chunks, what `add` leaves is the tree's stack for `m + 1` | no code: `Add.contract`'s result and the specification's tree (alg/Stack.lean) | 139 in 3 files | 0 |
| `hex_neon_meets` | AArch64, Google DeepMind's model | the kernel `hex_neon`, as assembled, writes the hexadecimal of the 32 bytes read and changes nothing else | `Hex.byteContract` (spec/HexContract.lean) | 6,180 in 14 files | 72 (bv_decide) |
| `hex_neon_quiet` | AArch64, Google DeepMind's model | two machines that differ only in what memory holds and in the vector registers show an observer the same while `hex_neon`'s words run | arm/Observer.lean | 7,677 in 36 files | 0 |
| `hex_neon_observed` | AArch64, Google DeepMind's model | the observer has an account of every instruction of `hex_neon`, from any state: the theorem above is not about two runs both unobserved | arm/Observer.lean | 7,667 in 36 files | 0 |
| `push_arm_meets` | AArch64, Google DeepMind's model | `push`, printed for AArch64 from the same source function and assembled, puts a chaining value on the stack | `Push.byteContract` (spec/PushContract.lean) | 6,193 in 16 files | 0 |
