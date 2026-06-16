#include <stdint.h>
/* a<b — cmp + setb + movzx */
uint32_t cmp_lt(uint32_t a, uint32_t b) { return a < b; }
