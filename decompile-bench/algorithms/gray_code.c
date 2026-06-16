#include <stdint.h>
/* binary -> Gray code — register-only leaf */
uint32_t gray_code(uint32_t x) { return x ^ (x >> 1); }
