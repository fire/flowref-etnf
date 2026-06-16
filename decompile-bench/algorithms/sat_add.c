#include <stdint.h>
/* saturating add — carry -> cmov */
uint32_t sat_add(uint32_t a, uint32_t b) {
  uint32_t s = a + b;
  return s < a ? 0xffffffffu : s;
}
