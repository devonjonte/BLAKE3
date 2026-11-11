# blake3-servil-core 0.9: its API

**Coming soon, not yet released.** `blake3-servil-core` is BLAKE3-Servil on
one thread: a fast BLAKE3 for 64-bit Arm (Linux, macOS) and x86-64 (Linux)
that produces the same digests as official BLAKE3. Every call hashes on
the thread that makes it; the crate starts no thread. Its assembly
kernels are each proved against the BLAKE3 specification.

This page lists everything a program can name in the crate, as it stands
on [`next`](https://github.com/servil-software-factory/BLAKE3/tree/next),
the branch that becomes 0.9; a check holds the list to the code. It
changes with the code until the release; from the release on, the same
list with every call's full documentation is at
<https://servil-software-factory.github.io/BLAKE3/>. Progress toward the
release: [BLAKE3 #357](https://github.com/servil-software-factory/BLAKE3/issues/357).

**Two kinds of call.** `convenience` takes any slice and returns the
result: one call a hash, tuned for a hash now and then. `throughput` is
for call after call: inputs come as `Block`s (64 bytes on a 64-byte
boundary), many messages hash side by side in one call, and digests go
where the program says. Every program calls `initialize()` once first: it
runs each kernel built for the machine against fixed values.

**On several cores.** The crate `blake3-servil` is this crate, whole,
with a pool of threads and a multithreaded form of each call
(`hash_multithreaded`, `hash_many_multithreaded`,
`hash_each_multithreaded`, `update_multithreaded`,
`update_each_multithreaded`). It is released with this one.

**From C.** `b3.h` (in `capi/`) is the convenience API for C: `b3_hash`,
`b3_hasher_new`, `b3_hasher_update`, `b3_hasher_finalize`,
`b3_hasher_finalize_xof`, the three `b3_mode_*` constructors and
`b3_version`.

**Cargo features.** `std` (on by default: the `Read`, `Write` and `Seek`
implementations, `Packed`, a `Batch` that owns its storage, and the calls
over many messages of different lengths or many hashers: `hash_each`,
`update_each`, `finalize_each`); `serde` and `zeroize` (off by default).
Without `std` the crate needs no allocator.

The list below is generated from the compiler's own record of the crate
(`python3 tools/api.py`), a signature and the first sentence of each
item's documentation.

## The crate's root

```rust
const BUILD_VERSION  (from `blake3_servil_version`)
const OUT_LEN: usize
const KEY_LEN: usize
const BLOCK_LEN: usize
const CHUNK_LEN: usize
```


- `fn initialize()`  
  Run the startup self-test and detect the CPU.


### `struct Hash`

An output of the default size, 32 bytes, which provides constant-time equality checking.

```rust
const fn as_bytes(&self) -> &[u8; 32]
const fn from_bytes(bytes: [u8; 32]) -> Self
const fn as_slice(&self) -> &[u8]
fn from_slice(bytes: &[u8]) -> Result<Self, TryFromSliceError>
fn to_hex(&self) -> ArrayString<{ _ }>
fn from_hex(hex: impl AsRef<[u8]>) -> Result<Self, HexError>
```

Implements: `Clone`, `Copy`, `Debug`, `Deserialize`, `Display`, `Eq`, `From`, `FromStr`, `Hash`, `PartialEq`, `Serialize`, `Zeroize`.


### `struct HexError`

The error type for `Hash::from_hex`.

Implements: `Clone`, `Debug`, `Display`, `Error`.


### `type_alias ContextKey`

An alias to distinguish `context_key` outputs from other keys.


### `enum Mode<'a>`

Which of BLAKE3's three functions a call computes.

```rust
Plain
Keyed(&'a [u8; 32])
DeriveKey(&'a str)
DeriveKeyWith(&'a ContextKey)
```

Implements: `Clone`, `Copy`.


### `struct OutputReader`

An incremental reader for extended output, returned by `Hasher::finalize_xof`.

```rust
fn fill(&mut self, buf: &mut [u8])
fn position(&self) -> u64
fn set_position(&mut self, position: u64)
```

Implements: `Clone`, `Debug`, `Read`, `Seek`, `Zeroize`.


## Module `convenience`

The convenience API.


- `fn hash(input: &[u8]) -> Hash`  
  The hash of `input`, on the calling thread.
- `fn hash_with(mode: Mode<'_>, input: &[u8]) -> Hash`  
  `hash` in any `Mode`.
- `fn hash_xof(mode: Mode<'_>, input: &[u8]) -> OutputReader`  
  The extended output of `input` in `mode`.


### `struct Hasher`

A message's hash, fed in pieces.

```rust
fn new(mode: Mode<'_>, length_hint: Option<u64>) -> Self
fn update(&mut self, input: &[u8]) -> &mut Self
fn finalize(self) -> Hash
fn finalize_xof(self) -> OutputReader
fn update_reader(&mut self, reader: impl Read) -> Result<&mut Self>
```

Implements: `Clone`, `Debug`, `Write`, `Zeroize`.


## Module `throughput`

The throughput API, for power users.


- `fn finalize_each(hashers: &mut [Hasher], which: &[usize], out: &mut [[u8; 32]])`  
  The hash of each message `which` names.
- `fn hash_each(mode: Mode<'_>, items: &[(&[Block], usize)], out: &mut [[u8; 32]])`  
  The hash of each message, of any lengths, on the calling thread.
- `fn update_each(hashers: &mut [Hasher], pieces: &[(usize, &[u8])])`  
  Feed each piece to its hasher.
- `fn hash(mode: Mode<'_>, input: &[Block], len: usize) -> Hash`  
  The hash in `mode` of the message of `len` bytes that starts `input`.
- `fn hash_many<P: Prepared>(mode: Mode<'_>, batch: &P, out: &mut [[u8; 32]])`  
  The hashes of a `Batch`'s messages, in `mode`, on the calling thread.
- `fn context_key(context: &str) -> ContextKey`  
  Hash a key-derivation context string and return a `ContextKey`.


### `struct Packed<const N: usize>`

`count` messages of `N` bytes each, packed end to end with nothing between them, on a 128-byte boundary.

```rust
fn new(count: usize) -> Self
fn as_blocks(&self) -> &[Block]
```

Implements: `Deref`, `DerefMut`, `Prepared`.


### `struct Batch<'a>`

Messages of one length in `Block`s, the batch calls' input.

```rust
fn new(message_len: usize, count: usize) -> Self
fn from_blocks(blocks: &'a [Block], message_len: usize) -> Self
fn message_len(&self) -> usize
fn len(&self) -> usize
fn is_empty(&self) -> bool
fn blocks(&self) -> &[Block]
fn message_mut(&mut self, i: usize) -> &mut [u8]
fn set(&mut self, i: usize, message: &[u8])
fn blocks_mut(&mut self) -> &mut [Block]
fn digests_mut(&mut self) -> &mut [[u8; 32]]
```

Implements: `Clone`, `Prepared`.


### `struct Block`

64 bytes on a 64-byte boundary.

```rust
const ZERO
fn bytes(blocks: &[Block]) -> &[u8]
fn bytes_mut(blocks: &mut [Block]) -> &mut [u8]
fn from_bytes(bytes: &[u8]) -> Option<&[Block]>
```

Implements: `Clone`, `Copy`, `Debug`, `Eq`, `PartialEq`.


### `trait Prepared`

The batch calls' input.
