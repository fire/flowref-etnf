# OPEN_GAPS — unfinished work, open problems (present tense)

Each item names the next decisive action when known. Completed items move to
`CHANGELOG.md`; abandoned approaches move to `TOMBSTONES.md`.

## Reranked priorities (2026-06-16)

The leaf/flag/select/forwarding-call class is saturated, so the old "raise strict
count on leaves" is essentially exhausted. Control flow / memory / calls hold the
remaining value. Current order, highest first:

1. **Broaden branch→select lifting beyond the first return diamond.**
   The first strict bridge is done: a compact 3-block forward branch diamond that
   only selects the return register now lowers to a ternary and proves in the
   oracle (`branch_select`). The remaining gateway is the general φ case: a use
   with multiple reaching defs across a 2-way conditional still lowers to an opaque
   `r_phi` local in `useToVer` (FlowrefDecompiler.lean, the `many` branch).
   **Next decisive action:** match each reaching def to its branch direction
   (taken vs fallthrough) for a reconverging diamond whose merge use is not just
   `ret`, emit `predOf ? def_then : def_else`, then widen the faithful gate only
   after the oracle proves the new bench case.

2. **Single-block memory in production.** Loads/stores for register+memory leaves.
   The IL already proves load/store/aliasing on real bytes; no CFG work needed —
   likely the fastest real-class win. Production `emitC` currently refuses any
   non-`lea` memory operand (`hasMemOp`).

3. **General calls (combine, not just forward).** ~87% of real functions call
   something. The IL proves `callDouble`; lift `call; <combine result with ALU>`
   from real multi-instruction sequences. The production emitter refuses calls.

4. **Loops** (gcd/is_prime/factorial/…). Biggest single corpus unlock, hardest
   (CFG structuring + invariant synthesis). Start with provably-bounded unrolling;
   defer general induction-from-bytes. Currently refused (multi-block).

5. **Harden/broaden leaves + oracle** — opportunistic background; diminishing but
   still occasionally finds bugs.

6. **`slangcheck`** — periodic health check (every few ticks): in `/tmp/lean-slang`
   ensure the vendor SDK (`vendor/fetch.sh` if `libslang.so` missing), pull if main
   moved, run `lake exe slangcheck`.

## Honest coverage gap

Faithful straight-line leaves are only ~4–13% of real Decompile-Bench functions
(register/memory-only, call-free). The formal IL *proves* loops, branches, and
calls, but the **lifter from real bytes** only handles straight-line + flag +
forwarding-call — wiring branch/loop CFG recovery end-to-end is the major remaining
engineering. "General-purpose faithful decompiler" is ~25–35% complete; the
straight-line slice is ~90%.

## Known latent caveats

- `whileLoopShader` in lean-slang `slangcheck` emits 168 bytes (== trivial shader):
  the loop body is dead-code-eliminated (no output buffer). Give it a side-effecting
  body so the SPIR-V actually exercises loop codegen.
- Variable-shift lifts (`a0 >> a1`, unmasked) are UB-reliant in C but recompile to
  the same count-masking `shr cl` as the binary — sound under the oracle's
  compiled-candidate-vs-binary contract, but a portability caveat for other
  toolchains.
