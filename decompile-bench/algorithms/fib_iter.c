#include <stdint.h>
/* nth Fibonacci — single counted loop */
uint32_t fib_iter(uint32_t n) { uint32_t a = 0, b = 1; for (uint32_t i = 0; i < n; i++) { uint32_t t = a + b; a = b; b = t; } return a; }
