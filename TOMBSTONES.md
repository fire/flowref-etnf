# TOMBSTONES

Dead ends to avoid.

- Size-biased `plausible Fin 65536` oracle sampling: replaced by boundary values plus full-range random vectors; it missed high-value truncation bugs.
- `cmovCount ≤ 2` gate cap: removed after cmov-aware reaching definitions made arbitrary cmov chains sound.
- Trying `-fno-if-conversion` to force a pure branch select: GCC still emits `cmov`; use `-O0` or side-effecting branch arms for real branch fixtures.
