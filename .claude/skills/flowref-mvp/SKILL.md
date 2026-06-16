---
name: flowref-mvp
description: The minimal viable vertical slice of flowref — the irreducible end-to-end path (bytes → compilable C whose return is provably equal to source) and the invariants/modules that must survive any trim. Use when flowref has grown bloated and you need a north star for what to keep vs cut, or to onboard the core design fast.
---

# flowref — Minimal Viable Vertical Slice

This is the **load-bearing core**. Everything else (below, "Accretion" and the
"Formal-verification track") is a layer on top of this slice and is trimmable
back toward it. When the codebase feels bloated, trim toward this; do not trim this.

## The one-sentence product

> Raw machine-code **bytes** → a **compilable C** function whose **return value is
> provably equal** to the original source function's — **or an explicit refusal**.
> flowref is **faithful-or-refuse**: it never emits C it cannot stand behind.

## The vertical slice (one thin path through every layer)

```
 bytes ─▶ [decode] ─▶ Ins[] ─▶ [kernel: CFG + reaching-defs + params] ─▶ [emit+gate] ─▶ C ─▶ [verify]
 capstoneDecodeBytes      Disasm + Dataflow + Params                   emitC + Emit      flowref-equiv
```

1. **Decode** — `Flowref/Decoders.lean :: capstoneDecodeBytes` : `(arch,mode,bytes,va) → Ins[]`.
   `Ins = {addr, mn, ops}` (`Flowref/Disasm.lean`) — the whole contract between the
   outside world and the kernel.
2. **Kernel / CFG** — `Disasm` carves basic blocks from `branchTarget`/`isUncondJmp`.
3. **Kernel / data-flow** — `Flowref/Dataflow.lean :: reachingDefsB` : the witness search
   ("which def of register r reaches instruction j?"), plausible-driven, smallest form.
4. **Kernel / params** — `FlowrefDecompiler/Params.lean` : recover the calling convention
   (SysV x86-64 / cdecl x86-32) so a live-on-entry register read becomes a parameter `aₖ`.
5. **Emit + gate** — `FlowrefDecompiler.lean :: emitC` + `FlowrefDecompiler/Emit.lean`:
   declare each SSA value as a typed C local, lower each insn, `return` the reaching def
   of the return register, **and run the faithfulness gate** — emit as trustworthy output
   ONLY when the function is in the modeled class (see I0).
6. **Verify** — `flowref-equiv` (`EquivCheck.lean`): lifts the region, compiles the
   (reference, candidate) pair, and runs a `plausible` `∀ args, ref = cand` search.
   `EQUIVALENT` / `NOT-EQUIVALENT` / `INCOMPARABLE`.

## The proof commands (if these pass, the slice is intact)

```bash
flowref demo basic --emit-c | gcc -xc -std=c11 -w -fsyntax-only -   # I1: compiles
./decompile-bench/equiv-demo.sh                                     # 11/11 EQUIVALENT (I3)
./decompile-bench/algo-bench.sh                                     # I0: SOUNDNESS 0 violations
```

`algo-bench.sh` runs flowref over our own textbook algorithms (`algorithms.c`) and the
oracle per function; it **exits non-zero if any strict lift is `NOT-EQUIVALENT`** — that
is the soundness tripwire. (Current: 5/19 strict-proven EQUIVALENT, 0 violations.)

## Invariants (never let a refactor break these)

- **I0 — faithful-or-refuse (THE product integrity invariant).** Strict mode emits C
  **only** for the modeled class — one basic block, no call, no memory operand, and
  every instruction in the emitter's modeled set (the gate also models `cmp`+`cmovcc`
  as a `(X op Y) ? src : dst` ternary). Any unmodeled instruction ⇒ **refuse** (hard
  error, nothing on stdout). Widen the gate ONLY after the oracle proves the new lift
  `EQUIVALENT`. *Lesson: a `cmp+cmov` leaf once passed the structural checks and was
  silently mis-lifted to wrong C under a "faithful" banner — the gate must whitelist
  modeled mnemonics, not assume unknown ones are no-ops. `algo-bench.sh` guards this.*
- **I1 — emitted C always compiles** as C11 (drop the un-lowerable to a comment, never
  to invalid syntax).
- **I2 — the kernel is pure**: `Disasm`/`Dataflow`/`Emit` have no I/O and no Capstone
  dependency; they speak only `Ins`. (The hexagon — why decoders/arches/formats are
  added without touching analysis.)
- **I3 — `return` = reaching def of the return register** (eax / r3), via the cmov-aware
  `writesRegX`/`defSites` for single-block leaves. Drop this and `int f(){return 7;}`
  decompiles to something returning 0.

## Minimal module set (the slice; keep)

| Module | Irreducible role |
|---|---|
| `Flowref/Disasm.lean` | `Ins` model, `writesReg`/`branchTarget`/CFG carving |
| `Flowref/Dataflow.lean` | `reachingDefsB` — the single witness search |
| `FlowrefDecompiler/Params.lean` | calling-convention parameter recovery |
| `FlowrefDecompiler/Emit.lean` | `cPreamble`, `cName`, type/operand lowering |
| `FlowrefDecompiler.lean :: emitC` | decls + body + return-SSA wiring + faithfulness gate |
| `Flowref/Decoders.lean :: capstoneDecodeBytes` | one decoder |
| `Flowref/Adapters.lean :: binaryFileAdapter` | one validated input adapter |

## Formal-verification track (parallel to the MVP — higher assurance, strategic)

A second, machine-checked path proves equivalence *as a theorem* rather than by the
differential oracle. It is layered ON the MVP (trim it before the slice), but it is the
direction of travel:

- `FlowrefDecompiler/IL.lean` — a `BitVec 32` SSA IL; per-function correctness discharged
  by **`bv_decide`** (real proof, replacing the random-tuple oracle). Covers registers,
  loads, stores (with aliasing), select/`cmov`, branching `if`, bounded + symbolic loops,
  and function calls.
- `FlowrefDecompiler/Lift.lean` — adapter `Flowref.Ins → SInsn → SProg` (the bridge from
  real decoded instructions to the IL; includes the `cmp`+`cmovcc` flags fusion).
- **lean-slang** dep (`V-Sekai-fire/lean-slang`) — the IL renders to a real Slang AST,
  proved meaning-preserving against lean-slang's `BitVec` semantics (`evalU32`/`evalU32M`/
  `evalStmtsU32M`/`evalU32F`); a libslang FFI compiles the emitted Slang to **SPIR-V
  in-process** (`LeanSlang.spirvSize`); and `LeanSlang.SIMT` proves data-parallel kernel
  correctness = per-thread body (`evalU32`) ∘ race-free non-interference.

## Accretion (valuable, but layered ON the slice — trim here first)

- Iterative-deepening ladder + plausible **certification** (`certifyReaching`, `ladder`,
  `resolveReachingDef`) — the slice only needs `reachingDefsB` at one budget.
- All Capstone arches in `capstoneSpec?` — the slice needs one.
- The asm-text decoder (`decompile-asm`, AT&T→Intel) — alternate input format.
- **xref** / `demo` subcommands / `--search-trace` — alternate entrypoints + instrumentation.
- `--unsafe` mode — emits best-effort C for the refused class (a coverage signal, banner
  "NOT faithful — do not trust"); never trusted, never counted as proven.
- **Removed:** the ETNF/DuckDB corpus normaliser (`Etnf.lean` is orphaned; its `flowref-etnf`
  target + `lean_duckdb` dep are gone from `lakefile.lean`).

## Known honest gaps (so "missing" isn't mistaken for "broken")

- Strict equivalence is proven for the modeled class: straight-line register-only leaves
  **with parameters** and **`cmp`+`cmov`** value-selects. Control flow / memory / calls in
  the **production** emitter are refused (correctly) — the IL/formal track models them but
  is not yet wired to production bytes end-to-end (the lifter consumes decoded `Ins`, not
  the live disassembler output).
- Kernel pattern families are x86 (all widths) + PowerPC; other arches decode but recover
  little until a family is added.

## How to re-derive the slice from a bloated tree

Run the three proof commands. Whatever modules/symbols are in the transitive call graph of
`emitC` + `capstoneDecodeBytes` + `flowref-equiv` are the slice; the IL/lean-slang track is
the formal layer; everything else is Accretion — safe to gate or delete if the proofs
(including `algo-bench.sh`'s **SOUNDNESS 0**) still pass.
