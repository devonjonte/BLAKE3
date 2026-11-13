/* UNVERIFIED algorithm probe, not the Ode implementation or a proof artifact.
 * Four striped VNNI accumulators follow libdeflate's Adler template algorithm.
 * This probe specializes seed 1 and permits a larger chunk by summing into u64.
 *
 * Copyright 2016 Eric Biggers
 * Copyright 2026 Devon Jonte
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 */
#include <immintrin.h>
#include <stddef.h>
#include <stdint.h>

_Static_assert(CHUNK <= 16384 && CHUNK % (4*VL) == 0, "bounded vector counters");
#if VL == 64
typedef __m512i Vec;
#define ADD _mm512_add_epi32
#define ADD8 _mm512_add_epi8
#define ZERO _mm512_setzero_si512
#define ONES _mm512_set1_epi8
#define LOAD(p) _mm512_loadu_si512(p)
#define MASKLOAD(m,p) _mm512_maskz_loadu_epi8((__mmask64)(m),p)
#define DOT _mm512_dpbusd_epi32
#define SHIFT _mm512_slli_epi32
#define MUL _mm512_mullo_epi32
#define SET32 _mm512_set1_epi32
static inline uint32_t sum32(Vec x) { return (uint32_t)_mm512_reduce_add_epi32(x); }
static inline uint64_t sum64(Vec x) {
    /* Each lane <= 2^31 at 16 KiB. Folding two lanes in u32 is safe. */
    __m256i halves = _mm256_add_epi32(_mm512_castsi512_si256(x), _mm512_extracti64x4_epi64(x,1));
    __m512i q = _mm512_cvtepu32_epi64(halves);
    return (uint64_t)_mm512_reduce_add_epi64(q);
}
#elif VL == 32
typedef __m256i Vec;
#define ADD _mm256_add_epi32
#define ADD8 _mm256_add_epi8
#define ZERO _mm256_setzero_si256
#define ONES _mm256_set1_epi8
#define LOAD(p) _mm256_loadu_si256((const __m256i*)(p))
#define MASKLOAD(m,p) _mm256_maskz_loadu_epi8((__mmask32)(m),p)
#define DOT _mm256_dpbusd_epi32
#define SHIFT _mm256_slli_epi32
#define MUL _mm256_mullo_epi32
#define SET32 _mm256_set1_epi32
static inline uint32_t sum32(Vec x) {
    __m128i q = _mm_add_epi32(_mm256_castsi256_si128(x), _mm256_extracti128_si256(x,1));
    q=_mm_add_epi32(q,_mm_shuffle_epi32(q,0x4e));
    q=_mm_add_epi32(q,_mm_shuffle_epi32(q,0xb1));
    return (uint32_t)_mm_cvtsi128_si32(q);
}
static inline uint64_t sum64(Vec x) {
    /* Eight lanes can each approach 2^32. Widen before folding any pair. */
    __m256i q=_mm256_add_epi64(_mm256_cvtepu32_epi64(_mm256_castsi256_si128(x)),
                             _mm256_cvtepu32_epi64(_mm256_extracti128_si256(x,1)));
    __m128i h=_mm_add_epi64(_mm256_castsi256_si128(q),_mm256_extracti128_si256(q,1));
    return (uint64_t)_mm_cvtsi128_si64(h)+(uint64_t)_mm_extract_epi64(h,1);
}
#else
#error "VL must be 32 or 64"
#endif
#define ADD3(a,b,c) ADD(ADD(a,b),c)
#define ADD4(a,b,c,d) ADD(ADD(a,b),ADD(c,d))
#if VL == 64
#define LG 6
#else
#define LG 5
#endif
static const uint8_t weights[VL] __attribute__((aligned(64))) = {
#if VL == 64
 64,63,62,61,60,59,58,57,56,55,54,53,52,51,50,49,48,47,46,45,44,43,42,41,40,39,38,37,36,35,34,33,
#endif
 32,31,30,29,28,27,26,25,24,23,22,21,20,19,18,17,16,15,14,13,12,11,10,9,8,7,6,5,4,3,2,1
};

uint32_t PROBE_NAME(const uint8_t *p, size_t len) {
    if (len == 0) return 1;
    if (len == 1) { uint32_t a=1+*p; return (a<<16)|a; }
    uint64_t a=1,b=0;
    const Vec ones=ONES(1), w=LOAD(weights);
    while (len) {
        size_t n=len < CHUNK ? len : CHUNK;
        b += a*n;
        len -= n;
        Vec s0=ZERO(),s1=ZERO(),s2=ZERO(),s3=ZERO();
        Vec t0=ZERO(),t1=ZERO(),t2=ZERO(),t3=ZERO();
        Vec h0=ZERO();
#if !ONEPREFIX
        Vec h1=ZERO(),h2=ZERO(),h3=ZERO();
#endif
        while (n >= 4*VL) {
#if ONEPREFIX
            h0=ADD(h0,ADD4(s0,s1,s2,s3));
#endif
            Vec x0=LOAD(p),x1=LOAD(p+VL),x2=LOAD(p+2*VL),x3=LOAD(p+3*VL);
            __asm__("" : "+v"(x0),"+v"(x1),"+v"(x2),"+v"(x3));
            t0=DOT(t0,x0,w); t1=DOT(t1,x1,w); t2=DOT(t2,x2,w); t3=DOT(t3,x3,w);
#if !ONEPREFIX
            h0=ADD(h0,s0); h1=ADD(h1,s1); h2=ADD(h2,s2); h3=ADD(h3,s3);
#endif
            s0=DOT(s0,x0,ones); s1=DOT(s1,x1,ones); s2=DOT(s2,x2,ones); s3=DOT(s3,x3,ones);
            __asm__("" : "+v"(t0),"+v"(t1),"+v"(t2),"+v"(t3),"+v"(h0),"+v"(s0),"+v"(s1),"+v"(s2),"+v"(s3)
#if !ONEPREFIX
                      ,"+v"(h1),"+v"(h2),"+v"(h3)
#endif
            );
            p+=4*VL; n-=4*VL;
        }
        Vec first=ADD(s0,s1), second=ADD(s0,s2);
        Vec sum=ADD4(s0,s1,s2,s3);
        Vec weighted=ADD4(t0,t1,t2,t3);
#if ONEPREFIX
        weighted=ADD(weighted,SHIFT(h0,LG+2));
#else
        weighted=ADD(weighted,SHIFT(ADD4(h0,h1,h2,h3),LG+2));
#endif
        weighted=ADD(weighted,ADD(SHIFT(first,LG+1),SHIFT(second,LG)));
        while (n >= VL) {
            Vec x=LOAD(p);
            weighted=ADD(weighted,SHIFT(sum,LG));
            weighted=DOT(weighted,x,w);
            sum=DOT(sum,x,ones);
            p+=VL; n-=VL;
        }
        if (n) {
            weighted=ADD(weighted,MUL(sum,SET32((int)n)));
            Vec x=MASKLOAD(UINT64_MAX>>(64-n),p);
            weighted=DOT(weighted,x,ADD8(w,ONES((int)n-VL)));
            sum=DOT(sum,x,ones);
            p+=n;
        }
        a=(a+sum32(sum))%65521;
        b=(b+sum64(weighted))%65521;
    }
    return (uint32_t)((b<<16)|a);
}
