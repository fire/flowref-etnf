# TOMBSTONES — dead ends, refuted hypotheses, blocked avenues

Why each was abandoned, and where any surviving knowledge lives. Keeps us from
re-trying what already failed.

## `-fno-if-conversion` does NOT force a branch for a pure value-select

Tried to get a real branch-diamond test case (for branch→select lifting) by
compiling `a < b ? b : a` with `gcc -O1 -fno-if-conversion -fno-if-conversion2`.
gcc still emits `cmp; mov; cmovnb` — the backend lowers a select to `cmov`
regardless of the if-conversion passes. **Surviving knowledge:** to get a genuine
branch, use `-O0` or an arm the backend cannot cmov (memory effect / call); see
`OPEN_GAPS.md` item 1.

## ETNF / DuckDB corpus normaliser — removed

The `Etnf.lean` corpus normaliser, its `flowref-etnf` target, and the `lean_duckdb`
dependency were removed (orphaned). The self-authored `decompile-bench/algorithms/`
benchmark replaced the messy real-corpus harness as the ground-truth source.

## `plausible` `Fin 65536` sampler as the equivalence oracle — replaced

The oracle's `∀ args` search over `Fin 65536` was size-biased toward small values
and almost never tested args ≥ 256, passing **false EQUIVALENTs** for bugs that
only diverge at large inputs (e.g. a dropped `movzx` truncation). Replaced by a
deterministic boundary battery + full-range random sweep (now in `EquivCheck.lean`;
see `CHANGELOG.md`). Note: `plausible` is still correct and used for the
reaching-def witness search, where it hunts for *any* counterexample to existence,
not value-equivalence over the full input range.

## `cmovCount ≤ 2` gate cap — removed

Was a workaround for the cmov-feeds-cmp SSA bug. Once the single-block reaching-def
became cmov-aware (canonReg + latest-def-before-use), arbitrary cmov chains lift
soundly (med3 = 4 cmovs proven), so the cap was removed.
