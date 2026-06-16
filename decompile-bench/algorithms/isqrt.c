#include <stdint.h>
/* integer sqrt — data-dependent loop */
uint32_t isqrt(uint32_t n) { uint32_t r = 0; while ((r + 1) * (r + 1) <= n) r++; return r; }
