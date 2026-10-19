# Is this code safe to trust?

This code gives the same BLAKE3 answers as official BLAKE3, faster. It is
new, so it could contain mistakes. We check it in three ways.

## Proof

Much of the new low-level code for Arm computers is proved. This means a
computer checked the reasoning for all inputs, not only the inputs we
tried. It also checked that this code stays inside the memory given to it
and does not choose what to do based on secret data.

## Tests

We compare answers with official BLAKE3 on many inputs.

We also test the tests. We insert one small mistake at a time into the
code and require a test to notice. If none does, we add a test or record
why that mistake cannot change an answer.

## Memory checks

Other checks watch for code reading or writing memory it should not use,
or sharing memory unsafely between tasks running at the same time. For
low-level code, tests place forbidden memory beside the data, so touching
one byte outside the allowed area causes a crash.

When a program starts, it also checks a few known answers before doing
real work.

## What the checks found

They found eight mistakes. All are fixed. Three could have given a wrong
answer, and one could have crashed a program. None is known to have
reached a user.

## Limits

No person has read all the code carefully, and nobody outside the project
has audited it. Some low-level code is not covered by proof and relies on
tests. These checks reduce risk; they do not remove it.

## Try the checks

```sh
git clone -b servil https://github.com/johnservil/BLAKE3
cd BLAKE3
cargo test --release --lib --tests
```

The [quality manual](docs/quality-manual.md) gives details for experts and
maintainers.
