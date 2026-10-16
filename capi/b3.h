/* BLAKE3, the servil fork's C API.
 *
 * Every call succeeds. A call whose arguments break its contract (below)
 * stops the program with a message. The first call runs the library's
 * startup self-test (well under a millisecond), which stops the program if
 * this build or this CPU computes wrong digests; every later call costs
 * nothing extra. Calls that use other CPU cores (`_multithreaded`) start
 * the library's threads at their first use; they last for the process.
 *
 * Link with -lb3 (libb3.a or libb3.so / libb3.dylib, built by `cargo build
 * --release` in capi/). C11.
 */
#ifndef B3_H
#define B3_H

#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/* A digest: 32 bytes. */
typedef struct {
  uint8_t bytes[32];
} b3_digest;

/* A mode: which of BLAKE3's three functions a call computes. Make one with
 * b3_plain, b3_keyed, or b3_derive_key, and pass it to as many calls as
 * you like; its fields are the library's. */
typedef struct {
  uint8_t kind;
  uint8_t key[32];
} b3_mode;

/* The plain hash function. */
b3_mode b3_plain(void);

/* The keyed hash function (a MAC) with this 32-byte key. */
b3_mode b3_keyed(const uint8_t key[32]);

/* Key derivation (a KDF) with this context: a NUL-terminated UTF-8 string,
 * hardcoded, globally unique, and application-specific, such as
 * "example.com 2026-10-16 session keys". The context is hashed here, once;
 * the calls' inputs are then the key material. */
b3_mode b3_derive_key(const char *context);

/* The digest of `len` bytes at `input` (`input` may be NULL when `len` is
 * 0), on the calling thread. */
b3_digest b3_hash(const b3_mode *mode, const void *input, size_t len);

/* b3_hash, using other CPU cores where that is faster: the same digest,
 * never slower. */
b3_digest b3_hash_multithreaded(const b3_mode *mode, const void *input, size_t len);

/* The distance between messages in a batch: `message_len` rounded up to a
 * multiple of 64 (64 for empty messages). */
#define B3_STRIDE(message_len) ((message_len) == 0 ? (size_t)64 : ((size_t)(message_len) + 63) / 64 * 64)

/* The digests of `count` messages of `message_len` bytes each, into
 * `out[0..count]`, on the calling thread. Message i starts at byte
 * i * B3_STRIDE(message_len) of `input`, and the bytes between a message's
 * end and the next stride are zero. Messages whose length is a multiple of
 * 64 sit back to back: a Merkle tree's layer of leaves, or of 64-byte
 * pairs of child digests. Many short messages hash fastest this way, about
 * five times faster than one b3_hash call each. */
void b3_hash_many(const b3_mode *mode, const void *input, size_t message_len, size_t count, b3_digest *out);

/* b3_hash_many, using other CPU cores where that is faster. */
void b3_hash_many_multithreaded(const b3_mode *mode, const void *input, size_t message_len, size_t count,
                                b3_digest *out);

/* One message fed in pieces. A b3_hasher is your memory (18 KiB; on the
 * stack, in a struct, or allocated), so the library allocates nothing and
 * there is nothing to free. b3_hasher_init starts a message, and starts
 * one over. */
#define B3_HASHER_SIZE 18432
typedef struct {
  _Alignas(64) uint8_t opaque[B3_HASHER_SIZE];
} b3_hasher;

void b3_hasher_init(b3_hasher *hasher, const b3_mode *mode);

/* Add the message's next `len` bytes. */
void b3_hasher_update(b3_hasher *hasher, const void *input, size_t len);

/* b3_hasher_update, using other CPU cores where that is faster. */
void b3_hasher_update_multithreaded(b3_hasher *hasher, const void *input, size_t len);

/* The digest of the bytes so far; the hasher can take more. */
b3_digest b3_hasher_finalize(const b3_hasher *hasher);

/* Extended output: `len` bytes of the output from byte `offset` on, into
 * `out`. Its first 32 bytes are the digest. */
void b3_hasher_output(const b3_hasher *hasher, uint64_t offset, void *out, size_t len);

#ifdef __cplusplus
}
#endif

#endif /* B3_H */
