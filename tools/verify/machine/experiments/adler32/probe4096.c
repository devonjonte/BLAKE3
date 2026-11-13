/* UNVERIFIED C caller around the Ode source kernel. The kernel's machine
 * theorem remains open. Seed one, arbitrary valid length, exact readable
 * bounds; same >65536-byte alignment peel as probe512_align. */
#include "align.h"

#ifndef RAW_KERNEL
#define RAW_KERNEL b3l_raw4096
#endif
extern uint64_t RAW_KERNEL(const uint8_t *p);
extern uint32_t probe512_r32(const uint8_t *p, size_t len);

#ifndef PROBE_NAME
#define PROBE_NAME probe4096
#endif

#if ENTRY_SPLIT
static __attribute__((noinline)) uint32_t probe4096_large(const uint8_t *p, size_t len) {
#else
uint32_t PROBE_NAME(const uint8_t *p, size_t len) {
#endif
    if (len < 4096) return probe512_r32(p, len);
    uint32_t prefix = adler_align_input(&p, &len);
    uint32_t a = prefix & 65535, b = prefix >> 16;
#if BATCH4
    while (len >= 16384) {
        uint64_t aa = a, bb = b;
        #pragma GCC unroll 4
        for (unsigned i = 0; i < 4; ++i) {
            uint64_t raw = RAW_KERNEL(p);
            bb += 4096 * aa + (raw >> 32);
            aa += (uint32_t)raw;
            p += 4096;
        }
        /* Block_adler32.update16384_bounds: aa fits u32, bb is below 2^36. */
        a = (uint32_t)aa % 65521;
        b = bb % 65521;
        len -= 16384;
    }
#endif
    while (len >= 4096) {
        uint64_t raw = RAW_KERNEL(p);
        /* Block_adler32.update4096_bounds checks these u32 bounds. */
        b = (b + 4096U * a + (uint32_t)(raw >> 32)) % 65521;
        a = (a + (uint32_t)raw) % 65521;
        p += 4096;
        len -= 4096;
    }
    if (len) {
        uint32_t tail = probe512_r32(p, len);
        /* Append a seed-one tail: subtract its seed contribution modulo P.
         * len < 4096 and a < P, so all these u32 expressions fit. */
        b = (b + (uint32_t)len * (a + 65520) + (tail >> 16)) % 65521;
        a = (a + (tail & 65535) + 65520) % 65521;
    }
#if CLEAN_AT_END
    /* Only word code runs between raw block calls. Clean upper state once
     * before returning to a caller that may use legacy SSE. */
    __asm__ volatile("vzeroupper");
#endif
    return (b << 16) | a;
}

#if ENTRY_SPLIT
uint32_t PROBE_NAME(const uint8_t *p, size_t len) {
    if (len < 4096) return probe512_r32(p, len);
    return probe4096_large(p, len);
}
#endif
