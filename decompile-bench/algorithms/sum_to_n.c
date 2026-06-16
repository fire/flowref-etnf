#include <stdint.h>
/* 1+2+...+n — single counted loop */
uint32_t sum_to_n(uint32_t n) { uint32_t s = 0; for (uint32_t i = 1; i <= n; i++) s += i; return s; }
