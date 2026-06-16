#include <stdint.h>
/* least common multiple — CALLS gcd */
uint32_t gcd(uint32_t a, uint32_t b);
uint32_t lcm(uint32_t a, uint32_t b) { return a / gcd(a, b) * b; }
