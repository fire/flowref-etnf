# CHANGELOG — completed work, decisions, durable rules

State that is **done and verified** lives here. Unfinished work → `OPEN_GAPS.md`;
dead ends → `TOMBSTONES.md`. Each fact lives in exactly one of the three.

## Durable project rules (do not break)

- **Faithful-or-refuse (I0).** Strict mode emits C only for the modeled class; any
  unmodeled instruction ⇒ refuse (hard error, nothing on stdout). Widen the gate
  ONLY after the equivalence oracle proves the new lift EQUIVALENT. `algo-bench.sh`
  must always report `SOUNDNESS: 0`.
- **Verify + commit discipline.** Every change is checked with `lake build
  flowref-decompiler` AND `./decompile-bench/algo-bench.sh` (SOUNDNESS 0); commit
  each green step.
- **Build Lean tools, not CLIs.** lean-slang compiles to SPIR-V in-process via a
  libslang FFI, never the `slangc` CLI.
- **No `objdump`.** It is denied in `.claude/settings.json`. Use flowref's own
  disassembler or `gcc -S`.
- **Generated C contains no inline assembly.** Assembly fixtures may exist only as
  binary-side inputs for shape coverage; flowref's converted C output must stay
  portable C, not `asm`.
- **CFG recovery reuses the plausible witness DAG.** Do not write new dataflow/CFG
  analysis — reuse `reachingDefsB`/`resolveReachingDef`/`certifyReaching`,
  `condBlocks`, `predOf`, and the plausible back-edge check. It works and is fast.

## Done — production decompiler (faithful-or-refuse)

- The MVP vertical slice (bytes → compilable C, return provably equal, or refuse):
  decode → CFG/reaching-defs/params → emit+gate → `flowref-equiv` oracle. See the
  `flowref-mvp` skill for the load-bearing core.
- **Modeled & proven leaf/flag/select class is saturated** (every single-block
  function in the bench proven), and the first compact branch-diamond return-select
  bridge is now strict for both unsigned and signed branch predicates. Strict
  **43/59 EQUIVALENT, 0 violations**, UNSAFE 59/59 compile. Modeled: ALU,
  neg/not, movzx/movsx (both signs), variable shifts,
  scaled+displaced `lea`, 1/2/3-operand `imul`, register-width aliasing (canonReg),
  cmp+cmov chains of any length, add/sub-carry (CF) cmov, test-ZF cmov, and `setcc`
  (the comparison-returning class). Flag conditions share one `condFromFlags` helper
  feeding both cmov and setcc.
- **Equivalence oracle hardened.** `flowref-equiv` replaced its size-biased
  `plausible` sampler with a deterministic boundary battery (sub-register/sign/
  extreme edges) + full-range random sweep. This closed a soundness blind spot that
  had passed false EQUIVALENTs for bugs only diverging at large inputs.
- Self-authored benchmark: `decompile-bench/algorithms/<name>.c` plus narrow
  `decompile-bench/asm/<name>.S` branch-shape fixtures, one function per file;
  `algo-bench.sh` compiles each and runs the oracle. Decompiler output remains C,
  never inline assembly.

## Done — formal IL track (machine-checked, `bv_decide`)

- `FlowrefDecompiler/IL.lean` — BitVec 32 SSA IL; per-construct correctness +
  render-correctness to lean-slang semantics. Covers registers, loads, stores (with
  aliasing), select/cmov, branching `if` (terminal select), bounded + symbolic loops,
  and function calls (`Stmt.call`/`CallEnv`, proved for all callees).
- `FlowrefDecompiler/Lift.lean` — adapter `Flowref.Ins → SInsn → SProg`. End-to-end
  proofs (decode→IL→bv_decide) for: lock, lea-add, mem load, store/load aliasing,
  succ, umax/umin (cmp+cmov), forwarding call (`apply_f`), call composed with ALU
  (`g(x)+x`), and setcc+movzx comparison (`cmp;setb;movzx;ret → (a<b)?1:0`).
- **lean-slang** (`V-Sekai-fire/lean-slang`, owned): Slang AST + BitVec semantics +
  libslang FFI (in-process SPIR-V via `dlmopen`); `slangcheck` compiles all fixtures
  end-to-end. `LeanSlang.SIMT` proves data-parallel kernel correctness = per-thread
  body (`evalU32`) ∘ race-free non-interference.

## Done — fixed soundness/correctness bugs (each caught by the bench/oracle)

- cmp+cmov leaf silently mis-lifted under a "faithful" banner → gate whitelists
  modeled mnemonics.
- `readelf -s` Size is decimal (was read as hex) → harness over-read functions.
- `neg`/`not` not in the dep's `writesReg` → mis-lifted; modeled as SSA defs.
- Multi-cmov / register-width aliasing (`lea (%rdx,%rdi)` after `add %esi,%edx`) →
  wrong SSA; fixed with cmov-aware single-block reaching-def + canonReg.
- Oracle sampler blind spot (above) → boundary battery.
- `movzx`/`movsx` of a sub-register lifted as a plain copy (dropped truncation/sign)
  → modeled by source width.
- Tiny x86 branch targets printed as bare decimal digits (`jb 9`) were invisible to
  the dependency's `branchTarget`, so compact diamonds were mis-carved as straight
  blocks. `btX`/`cbtX` now parse the bare-digit case for CFG recovery, and the
  first branch→select strict bridge lowers a three-block return diamond to a ternary.
- x86 branch predicates now distinguish signed (`jl`/`jle`/`jg`/`jge`) from
  unsigned (`jb`/`jbe`/`ja`/`jae`) comparisons when emitting C predicates.
