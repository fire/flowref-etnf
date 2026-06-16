#include <stdint.h>
/* unsigned max — cmp + single cmov */
uint32_t umax(uint32_t a, uint32_t b) { return a < b ? b : a; }
