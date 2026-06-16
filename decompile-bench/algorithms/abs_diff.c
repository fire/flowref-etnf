#include <stdint.h>
/* |a-b| unsigned — sub + cmov */
uint32_t abs_diff(uint32_t a, uint32_t b) { return a < b ? b - a : a - b; }
