#include <stdint.h>
/* floor((a+b)/2) without overflow — register-only leaf */
uint32_t avg_floor(uint32_t a, uint32_t b) { return (a & b) + ((a ^ b) >> 1); }
