#include <stdio.h>
#include <string.h>
#include <stdlib.h>
void b3l_hex_neon(unsigned char *out, const unsigned char *hash);
int main(void) {
  unsigned char h[32], o[64], e[64]; const char *d = "0123456789abcdef"; unsigned long long s = 88172645463325252ULL; long bad = 0;
  for (long n = 0; n < 1000000; n++) {
    for (int i = 0; i < 32; i++) { s ^= s << 13; s ^= s >> 7; s ^= s << 17; h[i] = (unsigned char)(s >> 24); }
    if (n < 256) memset(h, (int)n, 32);
    for (int i = 0; i < 32; i++) { e[2*i] = d[h[i] >> 4]; e[2*i+1] = d[h[i] & 15]; }
    b3l_hex_neon(o, h);
    if (memcmp(o, e, 64)) bad++;
  }
  printf("1000000 hashes (every byte value among them): %ld differ\n", bad); return bad != 0;
}
