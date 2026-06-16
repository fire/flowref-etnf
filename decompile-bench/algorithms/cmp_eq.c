#include <stdint.h>
/* a==b — cmp + sete + movzx */
uint32_t cmp_eq(uint32_t a, uint32_t b) { return a == b; }
