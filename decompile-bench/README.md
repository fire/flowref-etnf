# Decompile-Bench helpers

Small local fixtures for flowref and `flowref-etnf`.

## ETNF normalizer

Input rows are NDJSON objects with:

```text
{name, code, asm, file}
```

Run:

```bash
lake build flowref-etnf
./.lake/build/bin/flowref-etnf decompile-bench/fixture.ndjson /tmp/etnf
```

Writes:

```text
etnf_file.parquet       distinct file paths
etnf_source.parquet     distinct source bodies
etnf_asm.parquet        distinct assembly bodies
etnf_function.parquet   function fact table
```

The tool exits nonzero unless the join reconstructs the original rows.

## Flowref checks

```bash
./decompile-bench/equiv-demo.sh
./decompile-bench/algo-bench.sh
```

Expected soundness line:

```text
SOUNDNESS: 0 violations (no strict lift was wrong).
```
