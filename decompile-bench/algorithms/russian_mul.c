#include <stdint.h>
/* a*b via shift-add loop (unsafe signal) */
uint32_t russian_mul(uint32_t a, uint32_t b) { uint32_t p = 0; while (b) { if (b & 1u) p += a; a <<= 1; b >>= 1; } return p; }
