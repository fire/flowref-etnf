#include <stdint.h>
/* x & (x-1)  (clear lowest set bit) — register-only leaf */
uint32_t clear_lowest_bit(uint32_t x) { return x & (x - 1u); }
