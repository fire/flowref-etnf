#include <stdint.h>
/* lo<=x && x<=hi — branchless compare/and (or cmov) */
uint32_t in_range(uint32_t x, uint32_t lo, uint32_t hi) { return (x >= lo) & (x <= hi); }
