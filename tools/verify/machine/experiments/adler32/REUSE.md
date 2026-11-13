# Reuse the proved Ode project inside libdeflate

Libdeflate 1.26 supplies real whole-buffer compression and decompression. Its zlib
format writes an Adler-32 trailer after compression and checks the trailer after
decompression. Both call sites start from checksum 1:

- `lib/zlib_compress.c`: `libdeflate_adler32(1, in, in_nbytes)`.
- `lib/zlib_decompress.c`: `libdeflate_adler32(1, out, actual_out_nbytes)`.

These fit the existing Ode contract directly. The original Ode project computes
a whole message starting from 1. A general incremental Adler API takes an existing
checksum as well; retaining that API keeps streaming callers' contract intact.

## What the experiment does

`reuse_libdeflate.py PINNED_LIBDEFLATE_SOURCE NEW_OUTPUT`:

1. Invokes the existing project's normal `build.sh`: compile, generate the proof,
   check it, observe the object and verify the two compilation paths agree.
2. Copies libdeflate's pinned source into the output directory. The checkout stays
   unchanged. Replaces its two seed-one calls with calls to `b3l_adler32`.
3. Adds a C declaration for the two-argument function and packages the checked
   object in a static archive. CMake links that archive privately with
   `--exclude-libs,libode-adler.a`: both assembler aliases stay local, and internal
   calls bind to this library's checked body. The C declaration requires a 64-bit
   length. The result converts to u32, the checksum's public representation.
4. Builds ordinary and substituted shared libraries with the same release options.
5. Locates the Ode function in the final shared object and requires all 171 bytes
   to match the proved object before loading it. Requires the Ode symbols to stay
   out of the public exports and dynamic relocation table.
6. Exercises compression and decompression through each library's public API.

The experiment publishes the complete patch. It leaves libdeflate's DEFLATE engine
and general incremental `libdeflate_adler32` API unchanged. No system library is
installed or replaced.

From `tools/verify/machine/`, with the normal Ode build prerequisites and CMake:

```sh
python3 experiments/adler32/reuse_libdeflate.py /path/to/libdeflate NEW_OUTPUT
```

The source must be a clean checkout of libdeflate commit
`92e6a0db9fa848d742f9eb286c92afc60f2c3dda`. Use a bounded process-group supervisor.
The script itself gives its child commands deadlines. No timing is performed.

## Checked behavior

The experiment's successful run covers 40 inputs at levels 1, 6 and 12: 120 cases.
Inputs include fixed checksum vectors, four patterns and lengths at the modular
reduction boundary, through 1 MiB.

- Ordinary and substituted compression produce byte-identical zlib streams.
- Python zlib decompresses both streams to the original bytes.
- Both libraries decompress those streams and streams made by Python zlib.
- The output buffer has spare capacity: each decoder must report the actual output
  length and checksum that length, rather than the whole allocation.
- Changing each of the four checksum-trailer bytes independently gives 480 bad
  streams. Both decoders reject every one.
- The substituted library's original incremental Adler API still computes correct
  two-part checksums.

The summary records Python's zlib version and the pinned libdeflate commit.

## Assurance and performance scope

This demonstrates **mixed-language reuse**: a C library consumes the existing Ode
project's proof-checked object through its native ABI. Only the unchanged Ode
callee has the machine-code theorem. Libdeflate's callers, DEFLATE algorithm,
linker and the complete shared-library behavior receive executable integration
tests here. The existing x86 model/lifter and native proof-axiom trust remain.
A larger Ode program importing another Ode function's contract is a separate use.

This is an integration experiment, not a proposed performance replacement.
The standalone native comparison records the original scalar Ode loop's cost
beside libdeflate's optimized checksum. End-to-end compression and decompression
performance have yet to be measured with the substitution.
