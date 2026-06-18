# flowref-etnf

Lean tool that turns flat Decompile-Bench NDJSON rows into deduplicated Parquet tables.

```bash
lake build flowref-etnf
./.lake/build/bin/flowref-etnf decompile-bench/fixture.ndjson /tmp/etnf
```

Output:

```text
etnf_file.parquet
etnf_source.parquet
etnf_asm.parquet
etnf_function.parquet
```

It verifies the join before exiting:

```text
lossless-join verified: reconstruction == original (missing=0, extra=0) ✓
```

## Build

```bash
lake update
lake build flowref-etnf
./run-tests.sh
```

`flowref-etnf` uses `lean_duckdb` and its vendored DuckDB shared library.

## Included flowref tools

This repo still carries the flowref decompiler/oracle targets:

```bash
lake build flowref-decompiler flowref-equiv
./decompile-bench/algo-bench.sh
```

Current benchmark: 44/60 strict EQUIVALENT, 60/60 unsafe C compiles, 0 soundness violations.

## License

MIT.
