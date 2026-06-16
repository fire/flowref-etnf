#include <stdint.h>
/* Collatz step count — loop with branch */
uint32_t collatz_steps(uint32_t n) { uint32_t s = 0; while (n > 1u) { n = (n & 1u) ? 3u * n + 1u : n >> 1; s++; } return s; }
