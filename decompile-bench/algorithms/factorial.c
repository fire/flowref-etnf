#include <stdint.h>
/* n! mod 2^32 — single counted loop */
uint32_t factorial(uint32_t n) { uint32_t r = 1; for (uint32_t i = 2; i <= n; i++) r *= i; return r; }
