#include <stdint.h>
/* x!=0 — test + setne + movzx */
uint32_t nonzero(uint32_t x) { return x != 0u; }
