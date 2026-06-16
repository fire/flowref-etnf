#include <stdint.h>
/* number of divisors (unsafe signal) */
uint32_t count_divisors(uint32_t n) { uint32_t c = 0; for (uint32_t i = 1; i <= n; i++) if (n % i == 0u) c++; return c; }
