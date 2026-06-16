-- Disassembler modules come from the `fire/flowref` Lake dependency.
import Flowref.Disasm
import Flowref.Dataflow
import Flowref.Ports
import Flowref.Decoders
import Flowref.Adapters
import Flowref.Toc
-- Decompiler-specific modules, local to this package.
import FlowrefDecompiler.Emit
import FlowrefDecompiler.Params
import Plausible
import Lean.Data.Json

/-! # flowref — control-flow-aware xref **and** a plausible-driven decompiler

A linear disassembler tells you the instructions; it does *not* tell you where
a value is **defined** vs **used**, because a value is built in one basic block
and consumed in another. `flowref` recovers those links and — in `decompile`
mode — lifts a whole function into a **compilable C** translation unit.

**The engine is `plausible`, not a hand-written fixpoint.** Every data-flow
query is posed as `∀ candidate witness, ¬(it is the fact we want)` and plausible
hands back the counterexample, which *is* the fact (reaching def, back-edge, …).
The searches are **iteratively deepened**: cheap level first, escalate only the
unresolved frontier — a witness DAG (see `Flowref/Dataflow.lean`).

The emitter (`Flowref/Emit.lean`) lowers the recovered facts into C that
`gcc -fsyntax-only -std=c11 -w` accepts.
-/

-- `Flowref` = disassembler kernel (fire/flowref dep); `FlowrefDecompiler` = the
-- emitter + calling-convention model defined in this package.
open Plausible Flowref FlowrefDecompiler
open Lean (Json toJson)

/-- Version string. -/
def flowrefVersion : String :=
  "flowref 1.1.0 — control-flow-aware xref + plausible-driven decompiler with a " ++
  "calling-convention parameter model (SysV x86-64 + cdecl x86-32)"

/-- `--json` output uses `Lean.Json` (toolchain `Lean.Data.Json`) so string
escaping and rendering are the library's, not ours. `jn` is a small alias for
turning a `Nat` into a JSON number. -/
def jn (n : Nat) : Json := toJson n

/-- Full usage text. -/
def usageText : String :=
  "flowref — control-flow-aware xref + plausible-driven decompiler (compilable C)\n\n" ++
  "USAGE (ELF — arch, file offset, vaddr & length read from the headers):\n" ++
  "  flowref list          <binary>                                   (functions + detected arch)\n" ++
  "  flowref decompile     <binary>  <symbol|0xVaddr>    [--arch=<a>] [--search-trace]\n" ++
  "  flowref xref          <binary>  <symbol|0xVaddr> <targetHex> [--arch=<a>] [--search-trace]\n\n" ++
  "USAGE (explicit region — for raw blobs / stripped binaries):\n" ++
  "  flowref decompile     <binary>  <arch> <fnVaddrHex> <fileOffHex> <vaddrHex> <lenHex> [--search-trace]\n" ++
  "  flowref xref          <binary>  <arch> <targetHex>  <fileOffHex> <vaddrHex> <lenHex> [--search-trace]\n" ++
  "  flowref decompile-asm <listing> <arch> <fnVaddrHex> [--search-trace]   (objdump-style .asm text)\n" ++
  "  flowref xref-asm      <listing> <arch> <targetHex>  [--search-trace]   (objdump-style .asm text)\n\n" ++
  "DEMOS (built-in self-tests, no disk):\n" ++
  "  flowref demo                          list the demos\n" ++
  "  flowref demo basic  [--emit-c]        if + counting-loop → C\n" ++
  "  flowref demo deep                     iterative-deepening escalation\n" ++
  "  flowref demo params [--emit-c]        calling-convention parameter model\n\n" ++
  "MISC:\n" ++
  "  flowref <binary> <arch> <targetHex> <fileOffHex> <vaddrHex> <lenHex>   (legacy xref)\n" ++
  "  flowref --help | -h | --version\n\n" ++
  "ARGS:\n" ++
  "  arch        x86 (32-bit) | x64 (x86-64) | ppc (64-bit big-endian)\n" ++
  "  fnVaddrHex  virtual address of the function to decompile (e.g. 0x401010)\n" ++
  "  targetHex   address/constant to find references to (xref)\n" ++
  "  fileOffHex  start offset of the region in the file\n" ++
  "  vaddrHex    virtual/load address that fileOff maps to\n" ++
  "  lenHex      length of the region to disassemble\n\n" ++
  "FLAGS:\n" ++
  "  --emit-c        (with a demo) print ONLY the C translation unit to stdout,\n" ++
  "                  so it can be piped to a compiler:\n" ++
  "                    flowref demo basic --emit-c | gcc -xc -std=c11 -w -fsyntax-only -\n" ++
  "  --search-trace  print the iterative-deepening escalation chain to stderr\n" ++
  "  --arch=<a>      force the arch for the ELF short forms (else read from header)\n" ++
  "  --json          machine-readable output for list / decompile / xref (stdout)\n" ++
  "  --unsafe        emit C even for non-faithful functions (loops/memory/calls),\n" ++
  "                  with a 'NOT faithful — do not trust' banner (toggles strict off)\n" ++
  "  --help, -h      this help\n" ++
  "  --version       version string\n" ++
  "\nNOTE: decompile writes the C to stdout and all notes/traces to stderr, so\n" ++
  "  flowref decompile a.out main | gcc -xc -std=c11 -w -fsyntax-only -\n" ++
  "works with the resolution note still shown on the terminal.\n"

/-- Build the full compilable C translation unit for a function. Returns the C
text, the search trace, and a **faithful** flag: `true` iff the lift is exact
(straight-line, register-only leaf) so the result may be emitted as real output;
`false` means it must not be passed off as correct. -/
def emitC (a : A) (bits : Bits) (insns : Array Ins) (fnVa : Nat) : IO (String × Array TraceEntry × Bool) := do
  let nI := insns.size
  if nI == 0 then
    pure (cPreamble ++ "uint32_t sub_" ++ hex fnVa ++ "(void) { return 0; }\n", #[], false)
  else
  -- address → index
  let mut addr2idx : Std.HashMap Nat Nat := {}
  for i in [0:nI] do addr2idx := addr2idx.insert insns[i]!.addr i

  -- ===== Pass 0: calling-convention parameter model =====
  -- Recover the function's integer/pointer parameters from the calling
  -- convention chosen by (arch, width): SysV AMD64 for x86-64, cdecl for x86-32.
  -- This is what turns `sub_X(void)` into a real signature. See Flowref/Params.lean.
  let pm ← recoverParams a bits insns addr2idx
  -- The C parameter list, e.g. "uint32_t a0, uint32_t a1" (or "void").
  let paramList :=
    if pm.count == 0 then "void"
    else String.intercalate ", " (pm.names.map (fun nm => s!"uint32_t {nm}"))
  -- SysV: incoming arg registers bind to parameter names (a parameter is a
  -- def-at-entry); this is injected directly into the SSA use map in Pass 2
  -- below (the `[]`-reaching-def case), reusing the existing register-
  -- substitution path in `renderExprC` (so `mov eax, edi` → `eax = a0`).
  -- cdecl: incoming args are stack slots `[ebp+8]`/`[esp+4]`. After SSA/mem
  -- lowering a slot reads as `*(uint32_t*)((uintptr_t)(ebp + 8))`; we rewrite
  -- that exact C text to the parameter name `a{k}` as a final pass. Build the
  -- (needle, paramName) pairs once.
  let cdeclSlotRewrites : List (String × String) :=
    if pm.conv == .cdecl then
      -- Capstone may print the displacement in decimal (`ebp + 8`) or hex
      -- (`ebp + 0x8`); cover both forms of the lowered C text.
      (List.range pm.count).flatMap (fun k =>
        let eD := (cdeclEbpDisp k).toNat
        let sD := (cdeclEspDisp k).toNat
        [ (memToC s!"[ebp + {eD}]",       s!"a{k}"),
          (memToC s!"[ebp + 0x{hex eD}]", s!"a{k}"),
          (memToC s!"[esp + {sD}]",       s!"a{k}"),
          (memToC s!"[esp + 0x{hex sD}]", s!"a{k}") ])
    else []
  let applyCdecl := fun (s : String) =>
    cdeclSlotRewrites.foldl (fun acc (needle, nm) =>
      String.intercalate nm (acc.splitOn needle)) s

  -- ===== Pass 1: CFG (plain structural code) =====
  let mut isLeader : Array Bool := Array.replicate nI false
  isLeader := isLeader.set! 0 true
  for i in [0:nI] do
    let ins := insns[i]!
    match branchTarget a ins with
    | some t => match addr2idx[t]? with
        | some j => isLeader := isLeader.set! j true
        | none => pure ()
    | none => pure ()
    let terminates := isUncondJmp a ins ∨ (condBranchTarget a ins).isSome
    if terminates ∧ i+1 < nI then isLeader := isLeader.set! (i+1) true
  let mut blocks : Array BB := #[]
  let mut idx2blk : Array Nat := Array.replicate nI 0
  let mut bid := 0
  let mut k := 0
  while k < nI do
    let lo := k
    let mut j := k + 1
    while j < nI ∧ ¬ isLeader[j]! do j := j + 1
    for q in [lo:j] do idx2blk := idx2blk.set! q bid
    blocks := blocks.push { id := bid, lo, hi := j, succ := [] }
    bid := bid + 1
    k := j
  let nB := blocks.size
  blocks := blocks.map (fun b =>
    let last := insns[b.hi - 1]!
    let ft := if isUncondJmp a last ∨ b.hi ≥ nI then [] else [idx2blk[b.hi]!]
    let bt := match branchTarget a last with
      | some t => match addr2idx[t]? with | some q => [idx2blk[q]!] | none => ([] : List Nat)
      | none => ([] : List Nat)
    { b with succ := (ft ++ bt).eraseDups })
  let blkSucc := fun (b : Nat) => (blocks[b]?.map (·.succ)).getD []

  let reaches := fun (src dst : Nat) =>
    Id.run do
      let mut seen : Std.HashSet Nat := {}
      let mut stack := [src]
      while ¬ stack.isEmpty do
        match stack with
        | [] => pure ()
        | x :: rest =>
          stack := rest
          if ¬ seen.contains x then
            seen := seen.insert x
            if x == dst ∧ x != src then return true
            for s in blkSucc x do
              if s == dst then return true
              stack := s :: stack
      pure (seen.contains dst ∧ dst != src)

  -- ===== Pass 2: reaching definitions / SSA — PLAUSIBLE-DRIVEN + iterative deepening =====
  let defSites := (Array.range nI).filterMap (fun i =>
    (writesReg a insns[i]!).map (fun r => (i, r)))
  let mut ssaName : Std.HashMap Nat String := {}   -- def-index → "reg#k"
  do
    let mut verCount : Std.HashMap String Nat := {}
    for (i, r) in defSites do
      let v := (verCount.get? r).getD 0
      ssaName := ssaName.insert i s!"{r}#{v}"
      verCount := verCount.insert r (v+1)

  let mut useToVer : Std.HashMap Nat (List (String × String)) := {}  -- use-idx → [(reg, ssaName)]
  let mut trace : Array TraceEntry := #[]
  for j in [0:nI] do
    let usedRegs := readsRegs a insns[j]!
    for r in usedRegs do
      -- iterative-deepening, plausible-driven reaching-def resolution.
      let (defsR, _lvl, te) ← resolveReachingDef insns addr2idx a j r
      trace := trace.push te
      match defsR with
      | [] =>
        -- No reaching def inside the function ⇒ the value comes from the caller.
        -- Under SysV this read is live-on-entry: if `r` is an in-range arg
        -- register, bind it to its parameter name `a{k}` (a parameter is a
        -- def-at-entry). This is the same `[]`-witness the param model uses.
        match sysvParamForReg pm.count r with
        | some nm => useToVer := useToVer.insert j (((useToVer.get? j).getD []) ++ [(r, nm)])
        | none    => pure ()  -- genuine unknown source: leave as `r` (a local).
      | [only] =>
        let nm := cName ((ssaName.get? only).getD r)
        useToVer := useToVer.insert j (((useToVer.get? j).getD []) ++ [(r, nm)])
      | many =>
        -- φ across predecessors: lowered to a single declared local carrying r's
        -- current value (no φ in the emitted C — see the module docs).
        let baseLocal := cName (r ++ "_phi")
        useToVer := useToVer.insert j (((useToVer.get? j).getD []) ++ [(r, baseLocal)])
        let _ := many
        pure ()

  -- ===== Pass 4: control-flow structuring — PLAUSIBLE-DRIVEN =====
  let edges := (blocks.toList.flatMap (fun b => b.succ.map (fun s => (b.id, s))))
  let isBack := fun (b h : Nat) => h ≤ b ∧ reaches h b
  let backEdges := edges.filter (fun (b, h) => isBack b h)
  let loopHeaders := (backEdges.map (·.2)).eraseDups
  let loopProp := NamedBinder "w" (∀ w : Fin 4096,
    (match edges[w.val]? with
     | some (b, h) => decide (¬ isBack b h)
     | none => true) = true)
  let loopRes ← Testable.checkIO loopProp ({ numInst := 2000, quiet := true } : Plausible.Configuration)
  let condBlocks := blocks.toList.filterMap (fun b =>
    let last := insns[b.hi - 1]!
    if (condBranchTarget a last).isSome ∧ b.succ.length == 2 then some b.id else none)

  -- ===== collect declared locals: every SSA name + every register that appears =====
  -- x86 operand keywords that are not registers (size/segment specifiers).
  let kw := ["dword","qword","word","byte","tbyte","xmmword","ptr",
             "fs","gs","cs","ds","es","ss"]
  -- a C local name is legal iff non-empty, first char a letter/'_', not a keyword.
  let okLocal := fun (s : String) =>
    (! kw.contains s) && (match s.toList with
      | [] => false
      | c :: _ => (('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z') || c == '_'))
  let mut declSet : Std.HashMap String String := {}   -- cName → ctype
  -- Parameter names (`a0..aN`) are function arguments, not locals — never
  -- re-declare them (that would shadow/redefine the parameter and break compile).
  let declAdd := fun (m : Std.HashMap String String) (nm ty : String) =>
    let cn := cName nm
    if okLocal cn ∧ ¬ pm.names.contains cn then m.insert cn ty else m
  -- all SSA defs
  for (i, r) in defSites do
    let nm := (ssaName.get? i).getD r
    declSet := declAdd declSet nm (regCType r)
    -- Also declare the bare register: a written reg can simultaneously appear as
    -- a memory base/index in its own source operand (`mov rax, [rcx+rax*8]`),
    -- where `memToC` emits it un-versioned.
    declSet := declAdd declSet r (regCType r)
  -- φ locals + any read register. We always declare the *bare* register: memory
  -- operands (`memToC`) are emitted without SSA substitution, so a memory base
  -- like `rcx` appears verbatim and must be a declared local. When the read also
  -- has a recorded SSA version, declare that too (the substituted scalar path).
  for j in [0:nI] do
    for r in readsRegs a insns[j]! do
      if ¬ r.startsWith "0x" then
        declSet := declAdd declSet r (regCType r)
        match (useToVer.get? j).getD [] |>.lookup r with
        | some nm => declSet := declAdd declSet nm (regCType r)
        | none => pure ()
  -- the implicit return register
  let retReg := match a with | .x86 => "eax" | .ppc => "r3"
  declSet := declSet.insert (cName retReg) (regCType retReg)
  -- The value returned by a `ret` is the SSA version of the return register
  -- that *reaches* that `ret`, not the zero-initialised base local. With a
  -- single reaching def we wire the return to it (so `return 7;` survives);
  -- with zero or several (a φ across paths) we conservatively fall back to the
  -- base local. This is what makes simple functions provably equivalent.
  let retName := fun (q : Nat) =>
    match (reachingDefsB 4000 insns addr2idx a q retReg).1 with
    | [di] => cName ((ssaName.get? di).getD retReg)
    | _    => cName retReg

  -- ===== loop recovery from the plausible back-edge witnesses =====
  -- `backEdges`/`loopHeaders` (above) are the counterexamples to the `loopProp`
  -- plausible search, certified by `loopRes`. The structured emitter reuses THOSE
  -- witnesses — it does not run a second CFG analysis — to choose `while`/`do`:
  --   * `while` header: the back-edge target whose own conditional exits forward.
  --   * `do-while` header: the back-edge target whose conditional *tail* jumps back.
  -- Block-id branch targets used to classify the witnesses.
  let blkLast := fun (b : Nat) => insns[(blocks[b]!).hi - 1]!
  let condTgtBlk := fun (b : Nat) =>
    let li := blkLast b
    if (condBranchTarget a li).isSome then
      match branchTarget a li with | some t => (addr2idx[t]?).map (fun j => idx2blk[j]!) | none => none
    else none
  let uncondTgtBlk := fun (b : Nat) =>
    let li := blkLast b
    if isUncondJmp a li ∧ ¬ (li.mn.startsWith "ret" ∨ li.mn == "blr") then
      match branchTarget a li with | some t => (addr2idx[t]?).map (fun j => idx2blk[j]!) | none => none
    else none
  let whileHdr : Std.HashMap Nat (Nat × Nat) := Id.run do   -- header → (exitBlk, tailBlk)
    let mut m : Std.HashMap Nat (Nat × Nat) := {}
    for (tailB, hdr) in backEdges do
      if hdr < tailB then
        match condTgtBlk hdr with
        | some exitB => if exitB > tailB then m := m.insert hdr (exitB, tailB)
        | none => pure ()
    pure m
  let doWhileHdr : Std.HashMap Nat Nat := Id.run do          -- header → tailBlk
    let mut m : Std.HashMap Nat Nat := {}
    for (tailB, hdr) in backEdges do
      if hdr < tailB ∧ ¬ (whileHdr.get? hdr).isSome then
        match condTgtBlk tailB with
        | some t => if t == hdr then m := m.insert hdr tailB
        | none => pure ()
    pure m

  -- ===== declare-at-definition analysis (student-readable output) =====
  -- An SSA value is single-assignment, so we can declare it *where it is
  -- computed* (`uint32_t eax_0 = …;`) instead of in a big zeroed block up front.
  -- With structured control flow the declaration site sits inside an `if`/`while`
  -- scope, so this is sound ONLY when the def and every use live in the *same*
  -- basic block and that block is not a loop header (whose statements/condition
  -- straddle the loop braces). Cross-block / loop-carried values are declared at
  -- function top, where they are in scope everywhere. Uses come from the
  -- reaching-def witness map `useToVer`, so this too is witness-driven.
  let defIdxByName : Std.HashMap String Nat := Id.run do
    let mut m : Std.HashMap String Nat := {}
    for (i, r) in defSites do m := m.insert (cName ((ssaName.get? i).getD r)) i
    pure m
  let useIdxByName : Std.HashMap String (List Nat) := Id.run do
    let mut m : Std.HashMap String (List Nat) := {}
    for j in [0:nI] do
      for (_, nm) in (useToVer.get? j).getD [] do
        m := m.insert nm (j :: (m.get? nm).getD [])
      -- a `ret` consumes the return register's reaching def (wired by `retName`).
      if (insns[j]!.mn.startsWith "ret" ∨ insns[j]!.mn == "blr") then
        let rn := retName j
        m := m.insert rn (j :: (m.get? rn).getD [])
    pure m
  let inlineDef : Std.HashSet String := Id.run do
    let mut s : Std.HashSet String := {}
    for (nm, di) in defIdxByName.toList do
      let db := idx2blk[di]!
      let scopeSafe := ¬ (whileHdr.get? db).isSome ∧ ¬ (doWhileHdr.get? db).isSome
      let uses := (useIdxByName.get? nm).getD []
      if okLocal nm ∧ ¬ pm.names.contains nm ∧ scopeSafe then
        if uses.all (fun u => idx2blk[u]! == db ∧ u > di) then s := s.insert nm
    pure s

  -- Blocks that are the destination of some goto / conditional branch — only
  -- these need a `Lk:` label. Straight-line code then carries no labels at all.
  let labeledBlk : Std.HashSet Nat := Id.run do
    let mut s : Std.HashSet Nat := {}
    for q in [0:nI] do
      match branchTarget a insns[q]! with
      | some t => match addr2idx[t]? with | some jj => s := s.insert idx2blk[jj]! | none => pure ()
      | none => pure ()
    pure s

  -- ===== forward declarations for called subroutines =====
  let mut calledSubs : Std.HashSet Nat := {}
  for q in [0:nI] do
    let ins := insns[q]!
    if ins.mn == "call" ∨ (a == .ppc ∧ (ins.mn == "bl" ∨ ins.mn == "bctrl")) then
      match branchTarget a ins with
      | some t => calledSubs := calledSubs.insert t
      | none => pure ()

  -- ===== EMIT — structured control flow (NASA/JPL Power-of-Ten Rule 1) =====
  -- We render the plausible witness DAG as `if`/`while`/`do-while` (loop maps +
  -- `condBlocks` above) instead of goto+label wherever the CFG is reducible, and
  -- fall back to a labelled `goto` only for the irreducible remainder (so the
  -- unit always compiles). Unused labels are pruned afterwards.

  -- The C predicate for the conditional terminating block `b` (the cmp operands
  -- combined with the branch mnemonic).
  let predOf : Nat → String := fun (b : Nat) =>
    let bb := blocks[b]!
    let ins := insns[bb.hi - 1]!
    let cmpIdx := (Array.range (bb.hi - bb.lo)).toList.reverse.findSome? (fun off =>
      let p := bb.lo + (bb.hi - bb.lo - 1 - off)
      let cins := insns[p]!
      if cins.mn == "cmp" ∨ cins.mn == "test" ∨ cins.mn.startsWith "cmp" then some p else none)
    let pred : String := match cmpIdx with
      | some p =>
        let cins := insns[p]!
        let toks := (cins.ops.splitOn ",").map (·.trimAscii.toString)
        let subs := (useToVer.get? p).getD []
        let lower := fun (tk : String) =>
          if hasMem tk then memToC tk
          else if tk.startsWith "0x" ∨ tk.startsWith "-" then tk
          else (subs.lookup tk).map cName |>.getD (cName tk)
        match toks with
        | [x, y] =>
          let lx := lower x; let ly := lower y
          if cins.mn == "test" then s!"(({lx}) & ({ly}))"
          else
            let op := if ins.mn == "je" ∨ ins.mn == "jz" then "=="
              else if ins.mn == "jne" ∨ ins.mn == "jnz" then "!="
              else if ins.mn == "jl" ∨ ins.mn == "jb" then "<"
              else if ins.mn == "jle" ∨ ins.mn == "jbe" then "<="
              else if ins.mn == "jg" ∨ ins.mn == "ja" then ">"
              else if ins.mn == "jge" ∨ ins.mn == "jae" then ">="
              else "!="
            s!"((int32_t)({lx}) {op} (int32_t)({ly}))"
        | _ => "1 /* unknown predicate */"
      | none => "1 /* flag-based predicate unknown */"
    applyCdecl pred

  -- One non-terminator instruction → its C statement (or `none` to omit).
  let stmtOf : Nat → Option String := fun (q : Nat) =>
    let ins := insns[q]!
    if ins.mn == "cmp" ∨ ins.mn == "test" ∨ ins.mn == "nop" then none
    else if ins.mn == "call" ∨ (a == .ppc ∧ (ins.mn == "bl" ∨ ins.mn == "bctrl")) then
      match branchTarget a ins with
      | some t =>
        let args := if t == fnVa ∧ pm.count > 0 then String.intercalate ", " pm.names else ""
        some s!"{cName retReg} = sub_{hex t}({args});"
      | none => some "((uint32_t(*)(void))(uintptr_t)0)();  /* indirect call */"
    else match writesReg a ins with
      | some r =>
        let nm := cName ((ssaName.get? q).getD r)
        if okLocal nm then
          let subs := (useToVer.get? q).getD []
          let rhs := applyCdecl (renderExprC a ins subs)
          -- declare-at-definition; the declared type does the truncation a cast did.
          if inlineDef.contains nm then some s!"{regCType r} {nm} = {rhs};"
          else some s!"{nm} = ({regCType r})({rhs});"
        else none
      | none =>
        if hasMem ins.ops ∧ (ins.mn == "mov" ∨ ins.mn.startsWith "st") then
          match (ins.ops.splitOn ",").map (·.trimAscii.toString) with
          | [dst, src] =>
            if hasMem dst then
              let subs := (useToVer.get? q).getD []
              let lowSrc := if src.startsWith "0x" ∨ src.startsWith "-" then src
                else (subs.lookup src).map cName |>.getD (cName src)
              some s!"{memToC dst} = ({lowSrc});"
            else none
          | _ => none
        else none

  let padFor := fun (n : Nat) => String.join (List.replicate n "  ")

  let mut body : String := ""
  -- region stack: (kind, key, closeText); kind 0 = close `}` at start of block
  -- `key`; kind 1 = `do { … } while` closing at the END of tail block `key`.
  let mut stack : List (Nat × Nat × String) := []
  for b in [0:nB] do
    -- close any `if`/`while` regions that end at the start of this block.
    let mut closing := true
    while closing do
      match stack with
      | (0, key, txt) :: rest =>
        if key == b then stack := rest; body := body ++ padFor (stack.length + 1) ++ txt ++ "\n"
        else closing := false
      | _ => closing := false
    let bb := blocks[b]!
    let li := insns[bb.hi - 1]!
    let hasTerm := isUncondJmp a li ∨ (condBranchTarget a li).isSome
    let stmtHi := if hasTerm then bb.hi - 1 else bb.hi
    -- open a loop region if this block is a recognised header.
    let mut termConsumed := false
    match whileHdr.get? b with
    | some (exitB, _) =>
      body := body ++ padFor (stack.length + 1) ++ s!"while (!({predOf b})) " ++ "{\n"
      stack := (0, exitB, "}") :: stack
      termConsumed := true            -- the header conditional IS the loop test
    | none =>
      match doWhileHdr.get? b with
      | some tailB =>
        body := body ++ padFor (stack.length + 1) ++ "do {\n"
        stack := (1, tailB, "} while (0);") :: stack
      | none => pure ()
    let pad := padFor (stack.length + 1)
    if labeledBlk.contains b then body := body ++ s!"L{b}:;\n"
    -- straight-line statements
    for q in [bb.lo:stmtHi] do
      match stmtOf q with | some s => body := body ++ pad ++ s ++ "\n" | none => pure ()
    -- terminator
    if hasTerm ∧ ¬ termConsumed then
      let isDoTail := match stack with | (1, key, _) :: _ => key == b | _ => false
      if isDoTail then
        let cond := predOf b
        stack := stack.drop 1
        body := body ++ padFor (stack.length + 1) ++ "} while (" ++ cond ++ ");\n"
      else if (condBranchTarget a li).isSome then
        match condTgtBlk b with
        | some tb =>
          let nestOk : Bool := match stack with | (0, k, _) :: _ => decide (tb ≤ k) | _ => true
          if decide (tb > b) && nestOk then
            -- forward conditional → if-then over [b+1, tb): take the body when the
            -- branch is NOT taken.
            body := body ++ pad ++ s!"if (!({predOf b})) " ++ "{\n"
            stack := (0, tb, "}") :: stack
          else
            body := body ++ pad ++ s!"if ({predOf b}) goto L{tb};\n"
        | none => pure ()      -- conditional tail to external: fall through
      else if li.mn.startsWith "ret" ∨ li.mn == "blr" then
        body := body ++ pad ++ s!"return {retName (bb.hi - 1)};\n"
      else
        match uncondTgtBlk b with
        | some tb =>
          -- a back edge into a `while` header is the loop's implicit re-test: drop it.
          if (whileHdr.get? tb).isSome ∧ tb ≤ b then pure ()
          else body := body ++ pad ++ s!"goto L{tb};\n"
        | none => body := body ++ pad ++ s!"return {cName retReg};  /* indirect jump */\n"
  -- close any regions still open at function end (guarantees balanced braces).
  let mut closeAll := true
  while closeAll do
    match stack with
    | (_, _, txt) :: rest => stack := rest; body := body ++ padFor (stack.length + 1) ++ txt ++ "\n"
    | [] => closeAll := false
  -- trailing fall-through return only when the last instruction is not a terminator.
  let lastIsTerm := nI > 0 ∧
    (let li := insns[nI-1]!; isUncondJmp a li ∨ li.mn.startsWith "ret" ∨ li.mn == "blr")
  if ¬ lastIsTerm then body := body ++ s!"  return {retName (nI-1)};\n"
  body := body ++ "}\n"

  -- prune labels that no emitted `goto` targets (structuring removed most jumps).
  body := String.intercalate "\n" ((body.splitOn "\n").filter (fun line =>
    let t := line.trimAscii.toString
    if t.startsWith "L" ∧ t.endsWith ":;" then
      match ((t.dropEnd 2).drop 1).toNat? with
      | some n => contains body s!"goto L{n};"
      | none => true
    else true))

  -- ===== faithfulness gate =====
  -- Faithfulness is the bar, not a bonus. flowref's lift is *exact* only for a
  -- straight-line, register-only leaf: one basic block (no control flow to
  -- mis-structure), no memory (no aliasing), no calls (no unknown effects). For
  -- that class the SSA + emission reproduce the source's return value, and the
  -- equivalence oracle proves it. Anything else is NOT faithfully liftable yet —
  -- the caller refuses to print it as if it were correct (see `decompileInsns`).
  let hasCall := insns.any (fun i => i.mn == "call" ∨ (a == .ppc ∧ (i.mn == "bl" ∨ i.mn == "bctrl")))
  -- `lea` carries `[...]` syntax but performs address arithmetic, not a memory
  -- access — it does not disqualify a function from the faithful (register-only)
  -- class. Any other `[...]` operand is a real load/store.
  let hasMemOp := insns.any (fun i => i.mn != "lea" ∧ hasMem i.ops)
  let faithful := nB == 1 ∧ ¬ hasCall ∧ ¬ hasMemOp
  let mut out : String := cPreamble
  out := out ++ s!"\n/* flowref decompile @ 0x{hex fnVa} — {nI} insns, {nB} blocks, {defSites.size} SSA defs\n"
  out := out ++ s!"   loops (plausible back-edge: {loopRes.isFailure}): {loopHeaders}; conditionals: {condBlocks}\n"
  out := out ++ s!"   calling convention: {repr pm.conv}, recovered params: {pm.count}\n"
  if faithful then
    out := out ++ "   equivalence: faithful lift (straight-line register-only leaf) — provable by decompile-bench/equiv.sh */\n\n"
  else
    out := out ++ "   equivalence: NOT faithful — outside the liftable class (control flow / memory / calls); do not trust */\n\n"
  for t in calledSubs.toList do
    if t == fnVa ∧ pm.count > 0 then
      out := out ++ s!"uint32_t sub_{hex t}({paramList});\n"
    else
      out := out ++ s!"uint32_t sub_{hex t}(void);\n"
  out := out ++ "\nuint32_t sub_" ++ hex fnVa ++ s!"({paramList}) " ++ "{\n"
  -- declarations: only the locals that actually appear in the body and were not
  -- already declared at their definition site.
  let mut declLines : String := ""
  for (nm, ty) in declSet.toList do
    if ¬ inlineDef.contains nm ∧ wholeWordIn body nm then
      declLines := declLines ++ s!"  {ty} {nm} = 0;\n"
  out := out ++ declLines
  if ¬ declLines.isEmpty then out := out ++ "\n"
  out := out ++ body
  pure (out, trace, faithful)

/-- Extract the recovered C signature line (`uint32_t sub_…(…)`) from a TU, or
`""` if absent. Used for the `--json` `signature` field. -/
def signatureOf (c : String) : String :=
  match (c.splitOn "\nuint32_t sub_").getLast? with
  | some tail => ("uint32_t sub_" ++ ((tail.splitOn ")").headD "") ++ ")")
  | none => ""

/-- Pretty (commented) decompile to stdout, plus optional trace to stderr.
With `json`, emit a single `{signature, c, trace}` object instead of raw C.

With `strict` (the default, used by the real `decompile` command), a function
that is **not faithfully liftable** is a hard error: nothing is written to
stdout and the process exits non-zero — flowref never prints C it cannot stand
behind. `strict := false` is for the `demo` illustrations, which show the lift
mechanism with the `equivalence: NOT faithful` banner. -/
def decompileInsns (a : A) (bits : Bits) (insns : Array Ins) (fnVa : Nat)
    (showTrace : Bool) (json : Bool := false) (strict : Bool := true) : IO Unit := do
  let (c, trace, faithful) ← emitC a bits insns fnVa
  if strict ∧ ¬ faithful then
    let msg := "function is not faithfully liftable (control flow / memory / calls); flowref refuses to emit unverified C"
    if json then IO.println (Json.mkObj [("error", Json.str msg), ("faithful", Json.bool false)]).compress
    else IO.eprintln s!"error: {msg}"
    IO.Process.exit 5
  if json then
    let traceJson := trace.map (fun te =>
      let oc := match te.outcome with
        | .found w => s!"resolved (witness def-idx {w})"
        | .provablyNone => "provably-none"
        | .budgetHit => "budget-hit"
      Json.mkObj [("query", Json.str te.query), ("level", jn te.level), ("outcome", Json.str oc)])
    IO.println (Json.mkObj [("signature", Json.str (signatureOf c)),
      ("c", Json.str c), ("trace", Json.arr traceJson)]).compress
    return
  IO.print c
  if showTrace then
    IO.eprintln "=== iterative-deepening search trace ==="
    for te in trace do
      let oc := match te.outcome with
        | .found w => s!"resolved (witness def-idx {w})"
        | .provablyNone => "provably-none"
        | .budgetHit => "UNRESOLVED (budget hit)"
      IO.eprintln s!"  {te.query} → L{te.level} : {oc}"

/-- The synthetic self-test snippet (x86 at base 0x1000): a counting loop + an if. -/
def demoInsns : Array Ins :=
  let bytes : ByteArray := ByteArray.mk #[
    0xB8,0x00,0x00,0x00,0x00,
    0xBB,0x0A,0x00,0x00,0x00,
    0x39,0xD8,
    0x7D,0x06,
    0x83,0xC0,0x01,
    0xEB,0xF7,
    0x90,
    0x83,0xFB,0x0A,
    0x75,0x05,
    0xB9,0x01,0x00,0x00,0x00,
    0xC3 ]
  capstoneDecoder.decode .x86 (bytes, 0x1000)

/-- A deep self-test: `mov esi, 0x1000` then a long clobber-free run of `nop`s,
then `mov eax, [esi+4]` (a use of esi). The def→use walk must cross the whole
run, so the shallow L0 budget (64 steps) is hit (UNRESOLVED) and the query only
resolves once iterative deepening escalates to L1 (512 steps). This is the
demonstrable iterative-deepening case. `nNops` controls the chain length. -/
def demoDeepInsns (nNops : Nat) : Array Ins :=
  let prologue : Array UInt8 := #[0xBE, 0x00, 0x10, 0x00, 0x00]  -- mov esi, 0x1000
  let nops : Array UInt8 := Array.replicate nNops 0x90           -- nop * nNops
  let epilogue : Array UInt8 := #[0x8B, 0x46, 0x04, 0xC3]        -- mov eax,[esi+4]; ret
  let bytes : ByteArray := ByteArray.mk (prologue ++ nops ++ epilogue)
  capstoneDecoder.decode .x86 (bytes, 0x1000)

/-- Run the deep demo and report the escalation outcome for the `esi` use. -/
def demoDeep : IO Unit := do
  let insns := demoDeepInsns 100
  let nI := insns.size
  let mut addr2idx : Std.HashMap Nat Nat := {}
  for i in [0:nI] do addr2idx := addr2idx.insert insns[i]!.addr i
  -- the use is the penultimate instruction (`mov eax, [esi+4]`).
  let useIdx := nI - 2
  IO.println s!"=== iterative-deepening demo: {nI} insns, esi def at idx 0, use at idx {useIdx} ==="
  IO.println "Per-level outcome for reaching-def query (esi @ the use):"
  for lvl in ladder do
    let failure ← certifyReaching lvl insns addr2idx .x86 useIdx "esi"
    let (defs, budget) := reachingDefsB lvl.walkSteps insns addr2idx .x86 useIdx "esi"
    let status :=
      if ¬ defs.isEmpty then s!"RESOLVED (reaching def idx {defs}) plausible-found={failure}"
      else if budget then "UNRESOLVED (budget hit — escalate)"
      else "provably-none"
    IO.println s!"  L{lvl.idx} (walkSteps={lvl.walkSteps}, Fin {lvl.finBound}): {status}"
  -- the adaptive driver picks the first level that resolves it:
  let (defs, lvl, _te) ← resolveReachingDef insns addr2idx .x86 useIdx "esi"
  IO.println s!"\nAdaptive driver resolved esi@use at level L{lvl} with def(s) {defs}."
  IO.println "The shallow L0 search could NOT resolve it (budget hit); deepening did."

/-! ## Parameter-model demo (calling conventions)

Two synthetic functions exercise the parameter recovery:

* **x86-64 / System V** — `mov eax, edi ; add eax, esi ; ret`. Reads `edi`
  (arg0) and `esi` (arg1), both live-on-entry ⇒ 2 parameters.
* **x86-32 / cdecl** — standard prologue then `mov eax, [ebp + 8] ; …; ret`.
  Reads the first stack slot ⇒ 1 parameter.

The demo prints the recovered C signature for each (which `--demo-params --emit-c`
emits raw so it can be piped to a compiler). -/

/-- x86-64 SysV: `mov eax, edi ; add eax, esi ; ret` — uses arg0 (`edi`) and
arg1 (`esi`). -/
def demoSysvInsns : Array Ins :=
  let bytes : ByteArray := ByteArray.mk #[
    0x89, 0xF8,   -- mov eax, edi
    0x01, 0xF0,   -- add eax, esi
    0xC3 ]        -- ret
  capstoneDecodeBytes Capstone.Arch.x86 Capstone.Mode.b64 bytes 0x401000

/-- x86-32 cdecl: `push ebp ; mov ebp,esp ; mov eax,[ebp+8] ; pop ebp ; ret`
— reads the first cdecl stack slot ⇒ 1 parameter. -/
def demoCdeclInsns : Array Ins :=
  let bytes : ByteArray := ByteArray.mk #[
    0x55,               -- push ebp
    0x89, 0xE5,         -- mov ebp, esp
    0x8B, 0x45, 0x08,   -- mov eax, [ebp + 8]
    0x5D,               -- pop ebp
    0xC3 ]              -- ret
  capstoneDecodeBytes Capstone.Arch.x86 Capstone.Mode.b32 bytes 0x401100

/-- Run the parameter-model demo. With `emitC?` print only the C (for both
functions) so it can be piped to a compiler; otherwise print a human report. -/
def demoParams (emitC? : Bool) : IO Unit := do
  let (sysvC, _, _) ← emitC .x86 .b64 demoSysvInsns 0x401000
  let (cdeclC, _, _) ← emitC .x86 .b32 demoCdeclInsns 0x401100
  if emitC? then
    -- Two functions in one TU; rename the cdecl one so symbols don't collide.
    IO.print sysvC
    IO.print (String.intercalate "sub_401100b" (cdeclC.splitOn "sub_401100"))
  else
    IO.println "=== parameter-model demo: SysV x86-64 (2 params) ==="
    IO.println "synthetic: mov eax, edi ; add eax, esi ; ret"
    let sig := (sysvC.splitOn "\nuint32_t sub_401000").getLastD ""
    IO.println s!"recovered signature: uint32_t sub_401000{(sig.splitOn ")").headD ""})"
    IO.println ""
    IO.println "=== parameter-model demo: cdecl x86-32 (1 param) ==="
    IO.println "synthetic: push ebp; mov ebp,esp; mov eax,[ebp+8]; pop ebp; ret"
    let sig2 := (cdeclC.splitOn "\nuint32_t sub_401100").getLastD ""
    IO.println s!"recovered signature: uint32_t sub_401100{(sig2.splitOn ")").headD ""})"
    IO.println ""
    IO.println "(pipe `flowref demo params --emit-c` to gcc to confirm it compiles)"

/-- The basic self-test: synthetic `if` + counting loop, no disk. With
`emitCOnly`, print only the C translation unit (pipe to a compiler). -/
def runDemoBasic (emitCOnly showTrace : Bool) : IO Unit := do
  if emitCOnly then
    let (c, trace, _) ← emitC .x86 .b32 demoInsns 0x1000
    IO.print c
    if showTrace then
      IO.eprintln "=== iterative-deepening search trace (demo) ==="
      for te in trace do IO.eprintln s!"  {te.query} → L{te.level}"
  else
    IO.println "=== synthetic disassembly (x86, base 0x1000) ==="
    for i in demoInsns do IO.println s!"  0x{hex i.addr}: {i.mn} {i.ops}"
    IO.println ""
    -- a demo illustrates the lift mechanism; show it (banner flags it unverified).
    decompileInsns .x86 .b32 demoInsns 0x1000 showTrace (strict := false)

/-- Help for the `demo` subcommand family. -/
def demoHelp : String :=
  "flowref demo — built-in self-tests (no disk needed)\n\n" ++
  "  flowref demo basic  [--emit-c] [--search-trace]   if + counting-loop → C\n" ++
  "  flowref demo deep                                 iterative-deepening escalation\n" ++
  "  flowref demo params [--emit-c]                    calling-convention parameter model\n"

/-- `flowref list <bin>` — read the ELF and print the detected arch plus the
FUNC symbols (name, vaddr, size). This is the discovery menu you pick from for
`decompile <bin> <name>`. Fails cleanly if `bin` is not an ELF. -/
def runList (bin : String) (json : Bool := false) : IO Unit := do
  match ← readElf bin with
  | none =>
    let msg ← notElfMessage bin
    if json then IO.println (Json.mkObj [("error", Json.str msg)]).compress
    else IO.eprintln s!"error: {msg}"
    IO.Process.exit 3
  | some info =>
    let archTok := info.arch
    let cls := if info.is64 then "ELF64" else "ELF32"
    let endian := if info.littleEndian then "LE" else "BE"
    let fns := info.functions
    if json then
      let fnsJson := fns.map (fun fn => Json.mkObj
        [("name", Json.str fn.name), ("vaddr", jn fn.vaddr), ("size", jn fn.size)])
      IO.println (Json.mkObj [("file", Json.str bin), ("class", Json.str cls),
        ("endian", Json.str endian), ("arch", Json.str archTok),
        ("entry", jn info.entry), ("functionCount", jn fns.size),
        ("functions", Json.arr fnsJson)]).compress
      return
    let archShow := if archTok.isEmpty then s!"unknown (e_machine={info.machine})" else archTok
    IO.println s!"{bin}: {cls} {endian}  arch={archShow}  entry=0x{hex info.entry}  functions={fns.size}"
    if fns.isEmpty then
      IO.println "  (no FUNC symbols — binary may be stripped; use the explicit-region form)"
    else
      IO.println "  VADDR       SIZE    NAME"
      for fn in fns do
        IO.println s!"  0x{hex fn.vaddr}  {fn.size}\t{fn.name}"

def main (args : List String) : IO Unit := do
  let hasFlag := fun (f : String) => args.contains f
  let showTrace := hasFlag "--search-trace"
  let asJson := hasFlag "--json"
  -- `--unsafe` toggles OFF the faithful-or-refuse strict gate: emit the lift for
  -- non-faithful functions too (control flow / memory / calls), with the
  -- `equivalence: NOT faithful — do not trust` banner. Use as an oracle.
  let strict := ¬ hasFlag "--unsafe"
  -- `--arch=<tok>` forces the arch for the ELF-resolved short forms (rare:
  -- a misidentified e_machine). Otherwise the arch comes from the ELF header.
  let archOverride? := (args.find? (·.startsWith "--arch=")).map (·.drop 7 |>.toString)
  let positional := args.filter (fun s => ¬ s.startsWith "--")
  match args with
  | [] => IO.eprintln usageText; IO.Process.exit 2
  | _ =>
  if hasFlag "--help" ∨ hasFlag "-h" then IO.println usageText; return
  if hasFlag "--version" then IO.println flowrefVersion; return
  -- Legacy `--demo*` flags kept as aliases for the `demo` subcommand.
  if hasFlag "--demo-deep" then demoDeep; return
  if hasFlag "--demo-params" then demoParams (hasFlag "--emit-c"); return
  if hasFlag "--demo" then runDemoBasic (hasFlag "--emit-c") showTrace; return
  match positional with
  -- ── demo subcommand ─────────────────────────────────────────────────────
  | ["demo"] => IO.println demoHelp
  | "demo" :: "basic"  :: _ => runDemoBasic (hasFlag "--emit-c") showTrace
  | "demo" :: "deep"   :: _ => demoDeep
  | "demo" :: "params" :: _ => demoParams (hasFlag "--emit-c")
  | "demo" :: name :: _ =>
    IO.eprintln s!"unknown demo '{name}' (try: basic | deep | params)"; IO.Process.exit 2
  -- ── list (ELF discovery) ────────────────────────────────────────────────
  | "list" :: bin :: _ => guard (runList bin asJson)
  -- ── decompile ──────────────────────────────────────────────────────────
  -- ELF short form: resolve a symbol/address to a region from the headers.
  | ["decompile", bin, target] =>
    guard (runDecompileElf bin target archOverride? showTrace asJson strict)
  | "decompile" :: bin :: archS :: fnS :: foS :: vaS :: lenS :: _ =>
    guard (runDecompile (binaryFileAdapter bin archS foS vaS lenS) fnS showTrace asJson strict)
  | "decompile-asm" :: path :: archS :: fnS :: _ =>
    guard (runDecompile (asmFileAdapter archS path) fnS showTrace asJson strict)
  -- ── xref ───────────────────────────────────────────────────────────────
  -- ELF short form: <bin> <fnSym|fnAddr> <targetHex> — region from the ELF,
  -- target is what to find references to.
  | ["xref", bin, fnTarget, tgtS] =>
    guard (xrefElf bin fnTarget tgtS archOverride? showTrace asJson)
  | "xref" :: bin :: archS :: tgtS :: foS :: vaS :: lenS :: _ =>
    guard (xref (binaryFileAdapter bin archS foS vaS lenS) tgtS showTrace asJson)
  | "xref-asm" :: path :: archS :: tgtS :: _ =>
    guard (xref (asmFileAdapter archS path) tgtS showTrace asJson)
  -- ── legacy positional xref ─────────────────────────────────────────────
  | bin :: archS :: tgtS :: foS :: vaS :: lenS :: _ =>
    guard (xref (binaryFileAdapter bin archS foS vaS lenS) tgtS showTrace asJson)
  | _ => IO.eprintln usageText; IO.Process.exit 2
where
  /-- Run an analysis action, mapping any `IO` error to a clean message + exit 4.
  This keeps the untrusted-input failures (raised by the adapters) from dumping
  a stack trace. -/
  guard (act : IO Unit) : IO Unit := do
    try act catch e => IO.eprintln s!"error: {e.toString}"; IO.Process.exit 4
  /-- ELF-resolved decompile: derive (arch, fileOff, vaddr, len) from the ELF
  headers for `target` (a FUNC symbol or a `0x` address), report the resolution
  to stderr, then decompile that region. The function vaddr to carve is the
  resolved region's vaddr. -/
  runDecompileElf (bin target : String) (archOverride? : Option String)
      (showTrace json strict : Bool) : IO Unit := do
    let r ← elfResolveRegion bin target archOverride?
    let symNote := match r.symbol with | some s => s!" ({s})" | none => ""
    -- Resolution note goes to stderr, so JSON stdout stays a single clean object.
    IO.eprintln s!"resolved{symNote}: arch={r.arch} vaddr=0x{hex r.vaddr} fileOff=0x{hex r.fileOff} len=0x{hex r.len}"
    let (a, bits, insns) ← (elfBinaryAdapter r bin).run
    if insns.isEmpty then IO.eprintln "error: empty disassembly for the resolved region"; IO.Process.exit 3
    decompileInsns a bits insns r.vaddr showTrace json strict
    -- PPC64 ELFv1: annotate any TOC-relative loads in this function — the `r2`
    -- base is recovered from `.opd`, then each `ld off(r2)` / `addis r2,…` site
    -- is resolved to the absolute address it references. Notes go to stderr so
    -- the C on stdout stays pipe-clean.
    if r.arch == "ppc64" ∨ r.arch == "ppc64be" ∨ r.arch == "ppc64le" ∨ r.arch == "ppc" then
      match ← Flowref.readElfBytes bin with
      | none => pure ()
      | some eb => match eb.recoverR2? with
        | none => pure ()
        | some r2 =>
          let sites := Flowref.scanTocSites eb (Int.ofNat r2) insns
          if ¬ sites.isEmpty then
            IO.eprintln s!"=== TOC-resolved loads (r2=0x{hex r2} from .opd) ==="
            for w in sites do
              IO.eprintln s!"  @0x{hex w.vaddr}: {w.insn}  → 0x{hex w.resolved}"
  /-- ELF-resolved xref: resolve a function region from `(bin, fnTarget)`, then
  search it for def→use witnesses reaching `tgtS`. -/
  xrefElf (bin fnTarget tgtS : String) (archOverride? : Option String)
      (showTrace json : Bool) : IO Unit := do
    let r ← elfResolveRegion bin fnTarget archOverride?
    let symNote := match r.symbol with | some s => s!" ({s})" | none => ""
    IO.eprintln s!"resolved region{symNote}: arch={r.arch} vaddr=0x{hex r.vaddr} fileOff=0x{hex r.fileOff} len=0x{hex r.len}"
    -- PPC64 ELFv1: also resolve TOC-relative (`r2`) references. The module `r2`
    -- is recovered authoritatively from `.opd`; a `ld off(r2)` / `addis r2,…`
    -- site that lands on `target` is a reference the immediate-only walk cannot
    -- see (the address is in a `.toc1` cell, not built by `lis/addi`).
    runTocXref bin r.arch tgtS r json
    xref (elfBinaryAdapter r bin) tgtS showTrace json
  /-- PPC64 TOC-relative reference search. Recover the module `r2` from `.opd`,
  then scan the resolved region for `ld off(r2)` / `addis r2,…` sites whose
  TOC-resolved address equals `target`. Witnesses (and the recovered `r2`) are
  printed; in `--json` mode they go to stderr so the JSON stdout object from the
  immediate-walk `xref` stays a single clean record. A no-op for non-PPC. -/
  runTocXref (bin arch tgtS : String) (r : Flowref.ElfRegion) (json : Bool) : IO Unit := do
    if arch != "ppc64" ∧ arch != "ppc64be" ∧ arch != "ppc64le" ∧ arch != "ppc" then return
    let target : Int ← match parseImm? tgtS with
      | some v => pure v
      | none   => return            -- xref proper will report the bad target
    match ← Flowref.readElfBytes bin with
    | none => return
    | some eb =>
      match eb.recoverR2? with
      | none =>
        IO.eprintln "TOC: no .opd TOC base recovered (module may not use a TOC); skipping TOC resolution"
      | some r2 =>
        IO.eprintln s!"TOC: recovered r2/TOC base = 0x{hex r2} (from .opd)"
        -- decode the resolved region and scan it for TOC references to target.
        let (_a, _bits, insns) ← (elfBinaryAdapter r bin).run
        let wits := Flowref.scanTocXref eb (Int.ofNat r2) target insns
        if wits.isEmpty then
          IO.eprintln s!"TOC: no r2-relative site in this region resolves to 0x{hex target.toNat}"
        else
          let hdr := s!"TOC: {wits.size} r2-relative reference(s) to 0x{hex target.toNat}:"
          if json then IO.eprintln hdr else IO.println hdr
          for w in wits do
            let line := s!"  @0x{hex w.vaddr}: {w.insn}  → 0x{hex w.resolved}"
            if json then IO.eprintln line else IO.println line
  /-- Decompile whatever a `SourceAdapter` yields to compilable C. -/
  runDecompile (adapter : SourceAdapter) (fnS : String) (showTrace json strict : Bool) : IO Unit := do
    let fnVa ← match parseImm? fnS with
      | some v => if v < 0 then throw (IO.userError s!"fnVaddr must be non-negative, got '{fnS}'") else pure v.toNat
      | none => throw (IO.userError s!"invalid fnVaddr '{fnS}' (expected hex like 0x401010 or a decimal)")
    let (a, bits, insns) ← adapter.run
    if insns.isEmpty then IO.eprintln "error: empty disassembly for the given region"; IO.Process.exit 3
    decompileInsns a bits insns fnVa showTrace json strict
  /-- The ORIGINAL behaviour: a single-target def→use witness search, now with
  iterative deepening over the CFG-walk budget, over any `SourceAdapter`. -/
  xref (adapter : SourceAdapter) (tgtS : String) (showTrace json : Bool) : IO Unit := do
    let target : Int ← match parseImm? tgtS with
      | some v => pure v
      | none => throw (IO.userError s!"invalid target '{tgtS}' (expected hex like 0x401010 or a decimal)")
    let (a, _bits, insns) ← adapter.run
    if insns.isEmpty then IO.eprintln "error: empty disassembly for the given region"; IO.Process.exit 3
    let nI := insns.size
    let mut addr2idx : Std.HashMap Nat Nat := {}
    for i in [0:nI] do addr2idx := addr2idx.insert insns[i]!.addr i
    let succ := fun (i : Nat) =>
      let ins := insns[i]!
      let ft := if isUncondJmp a ins ∨ i+1 ≥ nI then [] else [i+1]
      let bt := match branchTarget a ins with
        | some t => (match addr2idx[t]? with | some j => [j] | none => ([] : List Nat))
        | none => ([] : List Nat)
      ft ++ bt
    -- walk with a step budget; report (hitAddr?, budgetExhausted?).
    let walk := fun (steps start : Nat) (reg : String) (val : Int) =>
      Id.run do
        let mut seen : Std.HashSet Nat := {}
        let mut stack := succ start
        let mut s := 0
        while ¬stack.isEmpty ∧ s < steps do
          s := s + 1
          match stack with
          | [] => pure ()
          | kk :: rest =>
            stack := rest
            if ¬ seen.contains kk ∧ kk < nI then
              seen := seen.insert kk
              let ins := insns[kk]!
              match useDisp a ins reg with
              | some disp => if val + disp == target then return (some ins.addr, false)
              | none => pure ()
              if ¬ clobbers a ins reg then stack := succ kk ++ stack
        pure (none, s ≥ steps ∧ ¬ stack.isEmpty)
    let defs := (Array.range nI).filterMap (fun i =>
      match defOf a insns[i]! with
      | some (r, v) => if (target - v).toNat < 0x10000 ∨ v == target then some (i, r, v) else none
      | none => none)
    if ¬ json then
      IO.println s!"insns={nI}, def-witness candidates={defs.size}, target=0x{hex target.toNat}"
    -- iterative deepening over the walk budget for the whole def set.
    let mut found := false
    let mut traceLines : Array String := #[]
    let mut witnesses : Array Json := #[]   -- witness records (for --json)
    for (i, rg, v) in defs do
      let mut resolved := false
      for lvl in ladder do
        if ¬ resolved then
          let (hit, budget) := walk lvl.walkSteps i rg v
          match hit with
          | some ua =>
            found := true; resolved := true
            traceLines := traceLines.push s!"def {rg}@0x{hex insns[i]!.addr} → use@0x{hex ua} resolved at L{lvl.idx}"
            witnesses := witnesses.push
              (Json.mkObj [("def", jn insns[i]!.addr), ("reg", Json.str rg),
                ("val", jn v.toNat), ("use", jn ua), ("level", jn lvl.idx)])
            if ¬ json then
              IO.println s!"  ~ def @0x{hex insns[i]!.addr} ({rg}={v}) → use @0x{hex ua}  [L{lvl.idx}]"
          | none =>
            if ¬ budget then resolved := true   -- provably none at this depth
            else if lvl.idx == ladder.size - 1 then
              traceLines := traceLines.push s!"def {rg}@0x{hex insns[i]!.addr} UNRESOLVED (budget hit at L{lvl.idx})"
    -- plausible certification that a witness exists among the defs (existence).
    let cfg : Plausible.Configuration := { numInst := 2000, quiet := true }
    let r ← Testable.checkIO
      (NamedBinder "w" (∀ w : Fin 4096,
        (match defs[w.val]? with
         | some (i, rr, v) => ((walk 4000 i rr v).1).isNone
         | none => true) = true)) cfg
    let foundAny := found || r.isFailure
    if json then
      IO.println (Json.mkObj [("insns", jn nI), ("candidates", jn defs.size),
        ("target", jn target.toNat), ("found", Json.bool foundAny),
        ("witnesses", Json.arr witnesses)]).compress
    else
      if foundAny then
        IO.println s!"FOUND a witness DAG to target (plausible counterexample: {r.isFailure})"
      else
        IO.println "no witness DAG reaches the target in this region"
      if showTrace then
        IO.eprintln "=== iterative-deepening search trace ==="
        for l in traceLines do IO.eprintln s!"  {l}"
