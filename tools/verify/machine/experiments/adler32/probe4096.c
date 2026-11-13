/* UNVERIFIED C caller around the Ode source kernel. The kernel's machine
 * theorem remains open. Seed one, arbitrary valid length, exact readable
 * bounds; same >65536-byte alignment peel as probe512_align. */
#include "align.h"

extern uint64_t b3l_raw4096(const uint8_t *p);
extern uint32_t probe512_r32(const uint8_t *p, size_t len);

uint32_t probe4096(const uint8_t *p, size_t len) {
    if (len < 4096) return probe512_r32(p, len);
    uint32_t prefix = adler_align_input(&p, &len);
    uint32_t a = prefix & 65535, b = prefix >> 16;
    while (len >= 4096) {
        uint64_t raw = b3l_raw4096(p);
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
    return (b << 16) | a;
}
