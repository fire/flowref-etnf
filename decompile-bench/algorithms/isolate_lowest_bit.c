#include <stdint.h>
/* x & -x  (lowest set bit) — uses neg */
uint32_t isolate_lowest_bit(uint32_t x) { return x & (0u - x); }
