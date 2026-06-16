# flowref

**Point it at a binary, get back compilable C you can actually read.** A
control-flow-aware xref finder and a small decompiler, written in Lean 4. For
*simple* functions it goes further and **machine-checks** that the C returns the
same value as the source — see *Equivalence* for exactly which.

```bash
flowref list   a.out                 # what functions are in here?
flowref decompile a.out main         # lift one to C (region read from the ELF)
flowref decompile a.out main | gcc -xc -std=c11 -w -fsyntax-only -   # it compiles
```

Real output, for a function taking two args and returning their sum:

```c
uint32_t sub_401000(uint32_t a0, uint32_t a1) {
  uint32_t eax_0 = a0;
  uint32_t eax_1 = eax_0 + a1;
  return eax_1;
}
```

The output is meant to be **read**: values declared where they're computed, real
`if`/`while` instead of `goto`, parameters recovered from the calling
convention, no machine noise. The style follows NASA/JPL's *Power of Ten* (simple
control flow, smallest scope) so it's easy to teach from and to review.

## Commands

| Command | What it does |
|---|---|
| `flowref list <bin>` | List functions (name, address, size) and the auto-detected arch. |
| `flowref decompile <bin> <name\|0xaddr>` | Lift a function to C. |
| `flowref xref <bin> <name\|0xaddr> <target>` | Find where `target` is used in that function. |
| `flowref demo` | Built-in self-tests (no files needed). |

Add `--json` for machine-readable output, `--search-trace` to watch the search.
For ELF binaries the arch, file offset, address and length are read from the
headers — give a symbol or `0x` address, not six hex numbers. For raw blobs,
pass them explicitly: `flowref decompile <bin> <arch> <fnVaddr> <fileOff> <vaddr> <len>`
(run `flowref --help` for the full list, including `.asm`-listing input).

## Equivalence

The goal is C that is both type-correct *and* returns the same value as the
original. This is **checked, not asserted** — and the **binary is the reference**,
not the source. The oracle (`flowref-equiv`, driven by `decompile-bench/equiv.sh`)
maps the function's raw bytes into executable memory and runs them directly,
compiles flowref's lifted C into a shared object, and compares the two over a
**deterministic boundary battery** (sub-register, sign and extreme edges —
0/255/256/0x7fffffff/0xffffffff, single-axis + diagonal + pairwise) followed by a
full-range random sweep. A divergence is the disproof (`NOT-EQUIVALENT`); its
absence is the witness (`EQUIVALENT`); anything unliftable is `INCOMPARABLE`,
never a false pass. (The earlier size-biased `plausible` sampler missed bugs that
only diverge at large inputs — see `TOMBSTONES.md`.)

What is proven **today** is the whole **single-basic-block leaf/flag/select
class**, with parameters: ALU, `neg`/`not`, `movzx`/`movsx`, variable shifts,
scaled+displaced `lea`, 1/2/3-operand `imul`, register-width aliasing, `cmp`+`cmov`
chains of any length, add/sub-carry and `test`-ZF conditional moves, and `setcc`
(the comparison-returning class). On the self-authored benchmark
(`decompile-bench/algorithms/`, one function per file):

```text
$ ./decompile-bench/algo-bench.sh
  …
  STRICT  : 41/57 proven EQUIVALENT (machine-checked)
  UNSAFE  : 57/57 emit C that compiles (best-effort coverage signal)
  SOUNDNESS: 0 violations (no strict lift was wrong).

$ ./decompile-bench/equiv-demo.sh
  RESULT: 11/11 proven functionally equivalent to their source.
```

A parallel **formal track** proves equivalence *as a theorem* rather than by the
differential oracle: a `BitVec 32` SSA IL (`FlowrefDecompiler/IL.lean`) discharged
by `bv_decide`, lifted from real decoded instructions
(`FlowrefDecompiler/Lift.lean`) and rendered meaning-preservingly to
[lean-slang](https://github.com/V-Sekai-fire/lean-slang) — which also compiles the
emitted shader to **SPIR-V in-process** and proves data-parallel kernel correctness.

Faithful C is the **bar, not a bonus.** `flowref decompile` emits C **only** for
the class it can lift exactly — a straight-line, register-only leaf. For anything
else (control flow, memory, calls) it is a **hard error**: a non-zero exit and
**nothing on stdout** — flowref never prints C it cannot stand behind. Closing
those gaps (parameters, memory, full control flow) is the job, not an excuse; the
current edge is in *Limitations*.

```text
$ flowref decompile a.out has_a_loop ; echo "exit=$?"
error: function is not faithfully liftable (control flow / memory / calls); flowref refuses to emit unverified C
exit=5
```

## How it works

- **Plausible-driven, no hand-rolled analysis.** Every data-flow fact (reaching
  defs, back-edges, reachability) is recovered as a *counterexample* from
  [`plausible`](https://github.com/leanprover-community/plausible), deepened
  on demand into a witness DAG. The `if`/`while` structure is rendered from
  those same witnesses.
- **Hexagonal.** A pure kernel speaks only an instruction model; adapters feed
  it from ELF, raw bytes, or an asm listing. The disassembler half
  (`Flowref.Disasm`/`Dataflow` + the ELF/Capstone adapters) lives in the
  [`fire/flowref`](https://github.com/fire/flowref) package, consumed here as a
  Lake dependency; this repo adds the decompiler (`FlowrefDecompiler.Emit`, the
  `FlowrefDecompiler.Params` calling-convention model, and the equivalence
  oracle). Decoding covers every Capstone target; data-flow patterns are x86 +
  PowerPC.

## Build & test

```bash
lake update                                                 # fetches fire/flowref + transitive deps
.lake/packages/lean-capstone/thirdparty/capstone/build.sh   # build libcapstone.a once (slow)
lake build
./run-tests.sh                                              # builds, runs demos, gcc-checks the C
```

`lake build` produces `.lake/build/bin/flowref-decompiler` (the CLI shown above)
and `flowref-equiv` (the equivalence oracle).

ELF parsing is a self-contained `<elf.h>` shim — no external library to install —
and now ships inside the [`fire/flowref`](https://github.com/fire/flowref)
dependency rather than this repo.

## Limitations

Faithful output is the standard. Today flowref *meets* it for the entire
**single-basic-block** leaf/flag/select class (above) — every such function in the
benchmark lifts and is proven. Everything with real **control flow** (branches,
loops), **memory**, or **calls** is an **open gap, not a finished feature**, and
`decompile` refuses it with a hard error rather than emit something unverified.
`xref` and `list` still work on any binary. The live edge — what is being modeled
next and why — is tracked in `OPEN_GAPS.md` (current #1: branch→select lifting,
reusing the plausible witness DAG); completed work and durable rules are in
`CHANGELOG.md`, and abandoned approaches in `TOMBSTONES.md`.

## License

MIT (see `LICENSE`). Disassembly via
[`lean-capstone`](https://github.com/fire/lean-capstone) (Capstone, BSD-3).
Evaluated against Decompile-Bench (Tan, Tian, Qi et al., 2025; see `CITATIONS.bib`).
