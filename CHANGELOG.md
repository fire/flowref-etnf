# CHANGELOG

Completed facts only.

## Current state

- `flowref-etnf` is restored as a Lake executable in `lakefile.lean`.
- It uses `lean_duckdb` to write four Parquet tables from Decompile-Bench NDJSON.
- `./run-tests.sh` step 13 builds `flowref-etnf`, writes the fixture tables, and verifies the lossless join.
- Flowref decompiler/oracle targets are still present and green.

## Verification baseline

```text
lake build flowref-etnf                         PASS
./run-tests.sh                                  PASS
./decompile-bench/algo-bench.sh                SOUNDNESS: 0 violations
```

## Durable rules

- `flowref-etnf` must prove `missing=0, extra=0` before reporting success.
- Strict decompiler lifts must keep `SOUNDNESS: 0`.
- Do not use `objdump`; use flowref or `readelf` metadata only.
