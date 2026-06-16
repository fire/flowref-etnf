#include <stdint.h>

uint32_t branch_select(uint32_t a, uint32_t b) {
  asm goto ("cmp %1, %0; jb %l[taken]" :: "r"(a), "r"(b) : "cc" : taken);
  return a;
taken:
  return b;
}
