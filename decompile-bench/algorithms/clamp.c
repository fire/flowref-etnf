#include <stdint.h>
/* min(max(x,lo),hi) — two cmov */
uint32_t clamp(uint32_t x, uint32_t lo, uint32_t hi) {
  uint32_t a = x < lo ? lo : x;
  return a < hi ? a : hi;
}
