#include <stdint.h>
/* exponentiation by squaring — loop + branch */
uint32_t pow_uint(uint32_t base, uint32_t exp) { uint32_t r = 1; while (exp) { if (exp & 1u) r *= base; base *= base; exp >>= 1; } return r; }
