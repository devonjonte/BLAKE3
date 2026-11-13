/* UNVERIFIED experiment: seed-one byte peel, only above libdeflate's 64 KiB
 * alignment threshold. Callers provide the original readable-input contract.
 * At most 63 bytes: A <= 16066, B <= 514143, both fit u32 before reduction. */
#include <stddef.h>
#include <stdint.h>

static inline uint32_t adler_align_input(const uint8_t **input, size_t *len) {
    const uint8_t *p = *input;
    uint32_t a = 1, b = 0;
    if (*len > 65536) {
        while ((uintptr_t)p & 63) {
            a += *p++;
            b += a;
            --*len;
        }
        *input = p;
    }
    return ((b % 65521) << 16) | a;
}
