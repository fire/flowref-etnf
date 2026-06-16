/* algorithms.c — textbook CS algorithms as pure, function-like uint32 routines.
 *
 * A self-authored decompilation benchmark: we wrote these, so we have the exact
 * ground truth and can (a) compile them to real binaries, (b) run flowref over
 * each function, and (c) check faithfulness with the equivalence oracle —
 * strict (proven-equal-or-refuse) and --unsafe (best-effort, scored).
 *
 * Constraints that keep them "function-like" (amenable to the proof path):
 *   - pure: output depends only on args; no globals, no I/O, no malloc.
 *   - total uint32 in / uint32 out (deterministic, side-effect free).
 *
 * Spread by structure so the bench exercises every flowref tier:
 *   leaf (straight-line)      → strict-provable today
 *   loop / branch / recursion → strict-refuses; --unsafe emits, oracle scores.
 */
#include <stdint.h>

/* ---- leaves: straight-line, register-only (strict-provable) ---- */
uint32_t id32(uint32_t x)              { return x; }
uint32_t add2(uint32_t a, uint32_t b)  { return a + b; }
uint32_t umax(uint32_t a, uint32_t b)  { return a < b ? b : a; }
uint32_t umin(uint32_t a, uint32_t b)  { return a < b ? a : b; }
uint32_t abs_diff(uint32_t a, uint32_t b) { return a < b ? b - a : a - b; }
uint32_t gray_code(uint32_t x)         { return x ^ (x >> 1); }          /* binary→Gray */
uint32_t avg_floor(uint32_t a, uint32_t b) { return (a & b) + ((a ^ b) >> 1); } /* no overflow */

/* ---- single counted loops ---- */
uint32_t sum_to_n(uint32_t n)          { uint32_t s = 0; for (uint32_t i = 1; i <= n; i++) s += i; return s; }
uint32_t factorial(uint32_t n)         { uint32_t r = 1; for (uint32_t i = 2; i <= n; i++) r *= i; return r; }
uint32_t fib_iter(uint32_t n)          { uint32_t a = 0, b = 1; for (uint32_t i = 0; i < n; i++) { uint32_t t = a + b; a = b; b = t; } return a; }
uint32_t popcount(uint32_t x)          { uint32_t c = 0; while (x) { c += x & 1u; x >>= 1; } return c; }
uint32_t log2_floor(uint32_t x)        { uint32_t r = 0; while (x > 1u) { x >>= 1; r++; } return r; }
uint32_t reverse_bits(uint32_t x)      { uint32_t r = 0; for (uint32_t i = 0; i < 32; i++) { r = (r << 1) | (x & 1u); x >>= 1; } return r; }

/* ---- loops with data-dependent control flow ---- */
uint32_t gcd(uint32_t a, uint32_t b)   { while (b) { uint32_t t = a % b; a = b; b = t; } return a; }
uint32_t isqrt(uint32_t n)             { uint32_t r = 0; while ((r + 1) * (r + 1) <= n) r++; return r; }
uint32_t pow_uint(uint32_t base, uint32_t exp) { uint32_t r = 1; while (exp) { if (exp & 1u) r *= base; base *= base; exp >>= 1; } return r; }
uint32_t is_prime(uint32_t n)          { if (n < 2u) return 0; for (uint32_t i = 2; i * i <= n; i++) if (n % i == 0u) return 0; return 1; }
uint32_t collatz_steps(uint32_t n)     { uint32_t s = 0; while (n > 1u) { n = (n & 1u) ? 3u * n + 1u : n >> 1; s++; } return s; }

/* ---- more branchless leaves: bit tricks (no flags) + multi-cmov ---- */
uint32_t isolate_lowest_bit(uint32_t x) { return x & (0u - x); }   /* x & -x */
uint32_t clear_lowest_bit(uint32_t x)   { return x & (x - 1u); }
uint32_t clamp(uint32_t x, uint32_t lo, uint32_t hi) {             /* min(max(x,lo),hi) — two cmov */
  uint32_t a = x < lo ? lo : x;
  return a < hi ? a : hi;
}
uint32_t max3(uint32_t a, uint32_t b, uint32_t c) {                /* two cmov */
  uint32_t m = a < b ? b : a;
  return m < c ? c : m;
}
uint32_t sat_add(uint32_t a, uint32_t b) {                         /* carry → cmov */
  uint32_t s = a + b;
  return s < a ? 0xffffffffu : s;
}

/* ---- calls another function ---- */
uint32_t lcm(uint32_t a, uint32_t b)   { return a / gcd(a, b) * b; }
