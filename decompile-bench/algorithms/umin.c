#include <stdint.h>
/* unsigned min — cmp + single cmov */
uint32_t umin(uint32_t a, uint32_t b) { return a < b ? a : b; }
