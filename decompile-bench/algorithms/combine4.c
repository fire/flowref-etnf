#include <stdint.h>
/* a+b+c+d — exercises 4-parameter SysV recovery (edi,esi,edx,ecx) */
uint32_t combine4(uint32_t a, uint32_t b, uint32_t c, uint32_t d) { return a + b + c + d; }
