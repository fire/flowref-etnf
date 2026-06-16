#include <stdint.h>
/* primality test — loop with early return */
uint32_t is_prime(uint32_t n) { if (n < 2u) return 0; for (uint32_t i = 2; i * i <= n; i++) if (n % i == 0u) return 0; return 1; }
