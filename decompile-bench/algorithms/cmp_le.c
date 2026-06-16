#include <stdint.h>
/* a<=b — cmp + setbe + movzx */
uint32_t cmp_le(uint32_t a, uint32_t b) { return a <= b; }
