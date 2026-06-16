#include <stdint.h>
/* x*5 — compiler uses lea [rdi+rdi*4] (scaled-index lea) */
uint32_t mul5(uint32_t x) { return x * 5u; }
