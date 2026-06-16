#include <stdint.h>
/* pack two halves: (a<<16)|(b&0xffff) — shift/and/or leaf */
uint32_t pack16(uint32_t a, uint32_t b) { return (a << 16) | (b & 0xffffu); }
