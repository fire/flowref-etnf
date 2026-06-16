#include <stdint.h>
/* max of three — two cmov */
uint32_t max3(uint32_t a, uint32_t b, uint32_t c) {
  uint32_t m = a < b ? b : a;
  return m < c ? c : m;
}
