#include <stdint.h>
/* floor(log2 x) — while loop */
uint32_t log2_floor(uint32_t x) { uint32_t r = 0; while (x > 1u) { x >>= 1; r++; } return r; }
