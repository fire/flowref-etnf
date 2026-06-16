#include <stdint.h>
/* reverse 32 bits — counted loop */
uint32_t reverse_bits(uint32_t x) { uint32_t r = 0; for (uint32_t i = 0; i < 32; i++) { r = (r << 1) | (x & 1u); x >>= 1; } return r; }
