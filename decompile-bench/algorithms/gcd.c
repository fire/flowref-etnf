#include <stdint.h>
/* Euclidean gcd — data-dependent loop */
uint32_t gcd(uint32_t a, uint32_t b) { while (b) { uint32_t t = a % b; a = b; b = t; } return a; }
