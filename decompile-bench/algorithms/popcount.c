#include <stdint.h>
/* population count — while loop */
uint32_t popcount(uint32_t x) { uint32_t c = 0; while (x) { c += x & 1u; x >>= 1; } return c; }
