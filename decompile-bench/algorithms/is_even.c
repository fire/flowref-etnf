#include <stdint.h>
/* (x&1)==0 — and + test/setcc */
uint32_t is_even(uint32_t x) { return (x & 1u) == 0u; }
