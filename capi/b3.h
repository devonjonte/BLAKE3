/* libb3_servil: the C API of blake3-servil.
 *
 * Every call succeeds. A call whose arguments break its contract (below)
 * stops the program with a message. The first call runs the library's
 * startup self-test (well under a millisecond), which stops the program if
 * this build or this CPU computes wrong digests; every later call costs
 * nothing extra. Calls that use other CPU cores (`_multithreaded`) start
 * the library's threads at their first use; they last for the process.
 *
 * Threads: any call may be made from any thread. A b3_mode is a value and
 * may be shared and read by any number of threads at once. A b3_hasher is
 * used by one thread at a time. After fork(), the child has none of the
 * library's threads; its calls still finish, on the calling thread.
 *
 * Link with -lb3_servil (libb3_servil.a, or libb3_servil.so /
 * libb3_servil.dylib). Build and install with `cargo cinstall --release`
 * in capi/; `pkg-config --cflags --libs b3_servil` gives the compiler flags.
 * The shared library has a versioned soname. C11, or C++11.
 * B3_VERSION names the header's version; b3_version() the library's, so a
 * program can check that the two agree.
 */
#define B3_VERSION "0.8.0"
#ifndef B3_H
#define B3_H

#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/* The library's version, the same text as B3_VERSION in the header it was
 * built with. */
const char *b3_version(void);

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
 * `out[0..count]`, on the calling thread. `input` starts at a 64-byte
 * boundary (aligned_alloc(64, n) gives one; a misplaced batch stops the
 * program). Message i starts at byte i * B3_STRIDE(message_len) of
 * `input`, and the bytes between a message's end and the next stride are
 * zero. Messages whose length is a multiple of
 * 64 sit back to back: a Merkle tree's layer of leaves, or of 64-byte
 * pairs of child digests. Short messages hash fastest this way: 1024
 * messages of 64 bytes take about a fifth of the time of 1024 b3_hash
 * calls (an Apple M4 Max). */
void b3_hash_many(const b3_mode *mode, const void *input, size_t message_len, size_t count, b3_digest *out);

/* b3_hash_many, using other CPU cores where that is faster. */
void b3_hash_many_multithreaded(const b3_mode *mode, const void *input, size_t message_len, size_t count,
                                b3_digest *out);

/* One message fed in pieces. A b3_hasher is your memory (18 KiB; on the
 * stack, in a struct, or allocated), so the library allocates nothing and
 * there is nothing to free. b3_hasher_init starts a message, and starts
 * one over. */
#define B3_HASHER_SIZE 18432
#ifdef __cplusplus
#define B3_ALIGN64 alignas(64)
#else
#define B3_ALIGN64 _Alignas(64)
#endif
typedef struct {
  B3_ALIGN64 uint8_t opaque[B3_HASHER_SIZE];
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

/* A stream: messages one after another, hashed on other CPU cores while
 * your program reads or makes the next ones; the fastest way to hash many
 * things. Begin one, submit each message with the place its digest goes
 * (your memory, which stays yours), and finish. Each place comes back to
 * `done` once its digests are in it, in submission order, on the thread
 * that calls the stream: during a submit when the stream is full (it holds
 * up to 1024 messages in flight), during b3_stream_collect, and during
 * b3_stream_finish, which hands back every place and ends the stream.
 * Every message and place submitted lives until b3_stream_finish. A
 * message stays unhashed in a task still open until the task fills or you
 * call collect or finish, so call one of them when you need a digest soon.
 *
 * A batch (b3_stream_submit_batch) is laid out as for b3_hash_many and
 * comes back as one place of `count` digests: for many short messages of
 * one length, batches hash several at a time and are faster than one
 * submit each. `ctx` goes to `done` unread. */
typedef struct b3_stream b3_stream;
typedef void (*b3_done)(void *ctx, b3_digest *places, size_t count);

b3_stream *b3_stream_begin(const b3_mode *mode, b3_done done, void *ctx);
void b3_stream_submit(b3_stream *stream, const void *input, size_t len, b3_digest *out);
void b3_stream_submit_batch(b3_stream *stream, const void *input, size_t message_len, size_t count, b3_digest *out);
void b3_stream_collect(b3_stream *stream);
void b3_stream_finish(b3_stream *stream);

#ifdef __cplusplus
}
#endif

#endif /* B3_H */
