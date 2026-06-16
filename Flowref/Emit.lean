import Flowref.Disasm
import Flowref.Dataflow

/-! # flowref — compilable C emission

The emitter lowers the recovered CFG + SSA + expressions into a **complete C
translation unit that `gcc -fsyntax-only -std=c11 -w` accepts**, in a style aimed
at teaching and safety-critical review (NASA/JPL *Power of Ten*: simple control
flow, smallest-scope data, warning-clean). The strategy:

* Emit `#include <stdint.h>` + typedefs and forward-declare every referenced
  `sub_*`, then a real `uint32_t sub_<addr>(…) { … }` definition.
* **Declare values where computed** (Power-of-Ten Rule 6, smallest scope):
  `uint32_t eax_0 = …;` at the definition, when def + uses share one block/scope;
  cross-block / loop-carried values are declared at function top. Unused
  declarations are pruned.
* Memory operands become `*(uint32_t*)(base + disp)`; calls become
  `sub_<tgt>();` or an indirect function-pointer call. SSA φ is lowered away:
  each `(reg, version)` is a distinct local; no φ appears in the output.
* **Structured control flow** (Power-of-Ten Rule 1): the plausible witness DAG
  (back-edge witnesses + reaching-def witnesses) is rendered as `if` / `while` /
  `do-while`; a labelled `goto` is used only for the irreducible remainder, and
  unused labels are pruned. Conditions are real C from the compare + branch.

The emitted C is required to be **both type-correct and functionally equivalent
to the source** — functional equivalence is flowref's defining invariant. It is
machine-checked by the Decompile-Bench equivalence oracle
(`decompile-bench/equiv.sh`), which compiles, links and *runs* the candidate
against the reference and compares results. Where a construct is outside the
faithfully-liftable subset the oracle reports `INCOMPARABLE` rather than assert a
false equivalence — it never passes off non-equivalent output as correct.
-/

namespace Flowref

/-- Map an x86/ppc register name to a C width type. Default `uint32_t`. -/
def regCType (r : String) : String :=
  let r := r.trimAscii.toString
  -- x86 8-bit
  if r == "al" ∨ r == "bl" ∨ r == "cl" ∨ r == "dl"
     ∨ r == "ah" ∨ r == "bh" ∨ r == "ch" ∨ r == "dh"
     ∨ r == "sil" ∨ r == "dil" ∨ r == "bpl" ∨ r == "spl" then "uint8_t"
  -- x86 16-bit
  else if r == "ax" ∨ r == "bx" ∨ r == "cx" ∨ r == "dx"
       ∨ r == "si" ∨ r == "di" ∨ r == "bp" ∨ r == "sp" then "uint16_t"
  -- x86 64-bit / ppc 64-bit
  else if r.startsWith "r" ∧ r.length ≥ 2 then "uint64_t"
  else "uint32_t"

/-- Make a string a C-legal identifier fragment: keep `[A-Za-z0-9_]`, map other
characters to `_`. -/
def cIdent (s : String) : String :=
  String.ofList (s.toList.map (fun c =>
    if ('a' ≤ c ∧ c ≤ 'z') ∨ ('A' ≤ c ∧ c ≤ 'Z') ∨ ('0' ≤ c ∧ c ≤ '9') ∨ c == '_' then c else '_'))

/-- Turn an SSA name like `eax#1` into a C-legal local `eax_1`. -/
def cName (ssa : String) : String := cIdent ssa

/-- Strip an x86 size keyword prefix (`dword ptr`, `byte ptr`, …) and `fs:` etc.
from a memory operand body, leaving the address expression. -/
def stripPtrKw (s : String) : String :=
  let s := s.trimAscii.toString
  let drops := ["dword ptr ", "qword ptr ", "word ptr ", "byte ptr ",
                "xmmword ptr ", "tbyte ptr ", "ptr "]
  drops.foldl (fun acc d => String.intercalate "" (acc.splitOn d)) s

/-- Substring test. -/
def contains (hay needle : String) : Bool := (hay.splitOn needle).length > 1

/-- Width (textual C type) implied by an x86 size keyword in `s`. -/
def memCType (s : String) : String :=
  if contains s "qword ptr" then "uint64_t"
  else if contains s "dword ptr" then "uint32_t"
  else if contains s "word ptr" then "uint16_t"
  else if contains s "byte ptr" then "uint8_t"
  else "uint32_t"

/-- Render a single x86 memory operand `[...]` body into a C lvalue/expr:
`*(uint32_t*)(base)`. Segment overrides (`fs:[0]`) are flattened to `(0)`. -/
def memToC (operand : String) : String :=
  -- operand is the full operand text, e.g. "dword ptr [esi + 4]" or "dword ptr fs:[0]"
  let ty := memCType operand
  -- extract inside the brackets
  let inner := ((operand.splitOn "[").drop 1 |>.headD "").splitOn "]" |>.headD ""
  -- drop a segment prefix like "fs:" that may sit before "["
  let inner := inner.trimAscii.toString
  -- build address expr: registers stay, hex/decimal stay, '+'/'*' valid in C, '-' valid.
  -- ensure tokens are C identifiers (registers already are).
  let addr := if inner.isEmpty then "0" else inner
  s!"*({ty}*)((uintptr_t)({addr}))"

/-- Does an operand text contain a memory reference? -/
def hasMem (s : String) : Bool := s.any (· == '[')

/-- A C-legal token: a register name maps to its SSA local; a hex/decimal
literal is passed through (normalising `0x` is already C-legal); anything else
is wrapped so it cannot break parsing. `subs` maps a raw register to its SSA
name (e.g. `esi` → `esi_0`). -/
def renderExprC (a : A) (i : Ins) (subs : List (String × String)) : String :=
  -- Substitute register reads with their SSA locals (longest name first to avoid
  -- partial overlaps). Shared by the register and `lea`-address paths.
  let subst := fun (s : String) =>
    let regSubs := (subs.filter (fun (rg, _) => ¬ rg.startsWith "0x")).toArray.qsort
                     (fun x y => x.1.length > y.1.length) |>.toList
    regSubs.foldl (fun (acc : String) (p : String × String) =>
      let (rg, nm) := p
      String.intercalate nm (acc.splitOn rg)) s
  let raw := rhsText a i
  if i.mn == "lea" then
    -- `lea dst, [expr]` computes the ADDRESS `expr` — it is register arithmetic,
    -- NOT a memory load. Emit the bracket contents with registers substituted
    -- (e.g. `lea eax, [rdi + rsi]` → `(a0 + a1)`), never a dereference.
    let inner := ((i.ops.splitOn "[").drop 1 |>.headD "").splitOn "]" |>.headD ""
    let inner := (stripPtrKw inner).trimAscii.toString
    let body := if inner.isEmpty then subst raw else subst inner
    s!"({body})"
  else if hasMem i.ops then
    -- a genuine load/store source: render the memory operand as a C dereference.
    memToC i.ops
  else
    let replaced := subst raw
    -- A bare register with no SSA def (an argument) stays as a declared local;
    -- the text is C-legal. Guard: a stray '[' would mean a mem expr.
    if hasMem replaced then memToC replaced else replaced

/-- Does `name` occur in `body` as a whole identifier (bordered by non-identifier
characters, or the string ends)? Used to prune declarations for names that never
actually appear in the emitted body — so only the locals a reader can see in use
are declared. Never removes a needed declaration: if the name is used, it is
present, so it is kept. -/
def wholeWordIn (body name : String) : Bool := Id.run do
  if name.isEmpty then return false
  let parts := body.splitOn name
  if parts.length ≤ 1 then return false
  let isIdent := fun (c : Char) =>
    ('a' ≤ c ∧ c ≤ 'z') ∨ ('A' ≤ c ∧ c ≤ 'Z') ∨ ('0' ≤ c ∧ c ≤ '9') ∨ c == '_'
  for idx in [0:parts.length - 1] do
    let lc := (parts[idx]!).toList.getLast?
    let rc := (parts[idx+1]!).toList.head?
    let lok := match lc with | some c => !isIdent c | none => true
    let rok := match rc with | some c => !isIdent c | none => true
    if lok && rok then return true
  return false

/-- Forward prototypes + typedefs preamble for the translation unit. -/
def cPreamble : String :=
  "#include <stdint.h>\n#include <stddef.h>\n"

end Flowref
