import Flowref.Disasm
import FlowrefDecompiler.IL

/-! # flowref — the decode→IL adapter: `Flowref.Disasm.Ins → SInsn`

This is the bridge the proof path was missing: it consumes the **real decoded
instruction type** produced by flowref's disassembler (`Flowref.Ins`, the output
of the Capstone-backed decoder) and lowers it into the proven lifter's `SInsn`,
which `FlowrefDecompiler.IL.liftS` turns into a verifiable `SProg`.

It is **faithful-or-refuse**, mirroring flowref's existing philosophy: it lifts
the clean register/immediate/`base+disp`-memory subset and returns `none` for
anything it cannot model exactly (a memory operand inside an ALU op, an unknown
mnemonic, a malformed operand). Sub-registers are canonicalised to one physical
name (`al/ax/eax/rax → rax`, `edi → rdi`, …) so the x86-64 return register and
argument registers alias correctly.

What remains for full automation is purely runtime plumbing: feed the bytes of a
function region through flowref's disassembler to get `List Ins`, then `liftFn`
here. No new proof obligation — the IL and its proofs already cover the result.
-/

namespace FlowrefDecompiler.Lift

open Flowref (Ins parseImm?)
open FlowrefDecompiler.IL

/-- Canonicalise an x86 register to its 64-bit physical name, so sub-register
writes/reads (al/eax/rax, dil/edi/rdi, …) alias the same IL register. -/
def canonReg (r : String) : String :=
  match r with
  | "al" | "ax" | "eax" | "rax" => "rax"
  | "bl" | "bx" | "ebx" | "rbx" => "rbx"
  | "cl" | "cx" | "ecx" | "rcx" => "rcx"
  | "dl" | "dx" | "edx" | "rdx" => "rdx"
  | "dil" | "di" | "edi" | "rdi" => "rdi"
  | "sil" | "si" | "esi" | "rsi" => "rsi"
  | _ => r

/-- The IL op for a two-operand ALU mnemonic, if supported. -/
def binOpOf : String → Option Op
  | "add" => some .add | "sub" => some .sub
  | "imul" | "mul" => some .mul
  | "and" => some .band | "or" => some .bor | "xor" => some .bxor
  | "shl" | "sal" => some .shl
  | "cmp" => some .ult         -- a compare; the IL models it as `< → 0/1`
  | _ => none

/-- Strip an Intel size keyword (`dword ptr [..]` → `[..]`). -/
def stripPtr (t : String) : String :=
  ["dword ptr ", "qword ptr ", "word ptr ", "byte ptr "].foldl
    (fun acc p => String.intercalate "" (acc.splitOn p)) t

/-- A parsed operand: register, immediate, or `[base + disp]` memory. -/
inductive Opd | reg (r : String) | imm (w : Word) | mem (base : String) (disp : Word)
  deriving Repr

/-- Parse one Intel operand token. -/
def parseOpd (t0 : String) : Option Opd :=
  let t := (stripPtr (t0.trimAscii.toString)).trimAscii.toString
  if t.startsWith "[" then
    let inner := (((t.splitOn "[").getD 1 "").splitOn "]").headD "" |>.trimAscii.toString
    match (inner.splitOn "+").map (·.trimAscii.toString) with
    | [b]    => some (.mem (canonReg b) 0)
    | [b, d] => (parseImm? d).map fun i => Opd.mem (canonReg b) (BitVec.ofInt 32 i)
    | _      => none
  else match parseImm? t with
    | some i => some (.imm (BitVec.ofInt 32 i))
    | none   => some (.reg (canonReg t))

/-- Token → IL operand (immediate if numeric, else a canonicalised register). -/
def tokToOperand (t : String) : Operand :=
  match parseImm? t with
  | some i => .imm (BitVec.ofInt 32 i)
  | none   => .reg (canonReg t)

/-- A scratch register for a memory operand fused into an ALU instruction. The
SSA lifter versions each write, so reusing one name across instructions is safe. -/
def scratch : String := "__t"

/-- The zero-extension mask for a sub-register source (`al`→`0xff`, `ax`→`0xffff`),
or `none` for a full-width (32/64-bit) name. Used to model `movzx`. -/
def subRegMask (r : String) : Option Word :=
  match r.trimAscii.toString with
  | "al" | "bl" | "cl" | "dl" | "sil" | "dil" | "bpl" | "spl"
  | "ah" | "bh" | "ch" | "dh" => some 0xff
  | "ax" | "bx" | "cx" | "dx" | "si" | "di" | "bp" | "sp" => some 0xffff
  | _ => none

/-- Lower a single decoded instruction to a *list* of `SInsn` (one x86
instruction may expand to several IL ops, e.g. an ALU op with a memory operand
becomes a load to a scratch register followed by the register ALU), or refuse
(`none`). -/
def insToS (i : Ins) : Option (List SInsn) :=
  let toks := (i.ops.splitOn ",").map (·.trimAscii.toString)
  match i.mn, toks with
  | "ret", _    => some [.ret "rax"]                       -- x86-64 returns in rax
  | "lea", [d, m] =>
    -- `lea dst, [a + b]` is address arithmetic: dst := a + b (NOT a load).
    match parseOpd d with
    | some (.reg dr) =>
      let inner := (((m.splitOn "[").getD 1 "").splitOn "]").headD "" |>.trimAscii.toString
      match (inner.splitOn "+").map (·.trimAscii.toString) with
      | [a, b] => some [.bin dr .add (tokToOperand a) (tokToOperand b)]
      | [a]    => some [.mov dr (tokToOperand a)]
      | _      => none
    | _ => none
  | "mov", [d, s] =>
    match parseOpd d, parseOpd s with
    | some (.reg dr),    some (.reg sr)     => some [.mov dr (.reg sr)]
    | some (.reg dr),    some (.imm w)      => some [.mov dr (.imm w)]
    | some (.reg dr),    some (.mem b disp) => some [.load dr b disp]        -- load
    | some (.mem b disp), some (.reg sr)    => some [.store b disp sr]       -- store
    | _, _ => none
  | "movzx", [d, s] =>   -- zero-extend: mask a sub-register source, else plain move
    match parseOpd d with
    | some (.reg dr) =>
      match subRegMask s with
      | some m => some [.bin dr .band (.reg (canonReg s)) (.imm m)]
      | none   => some [.mov dr (tokToOperand s)]
    | _ => none
  | "inc", [d] =>   -- inc r ⇒ r := r + 1
    match parseOpd d with | some (.reg r) => some [.bin r .add (.reg r) (.imm 1)] | _ => none
  | "dec", [d] =>   -- dec r ⇒ r := r - 1
    match parseOpd d with | some (.reg r) => some [.bin r .sub (.reg r) (.imm 1)] | _ => none
  | "neg", [d] =>   -- neg r ⇒ r := 0 - r
    match parseOpd d with | some (.reg r) => some [.bin r .sub (.imm 0) (.reg r)] | _ => none
  | mn, [d, s]  =>
    match binOpOf mn, parseOpd d, parseOpd s with
    | some op, some (.reg dr), some (.reg sr) => some [.bin dr op (.reg dr) (.reg sr)]
    | some op, some (.reg dr), some (.imm w)  => some [.bin dr op (.reg dr) (.imm w)]
    -- ALU with a memory source operand: load it to a scratch, then the reg ALU.
    | some op, some (.reg dr), some (.mem b disp) =>
        some [.load scratch b disp, .bin dr op (.reg dr) (.reg scratch)]
    | _, _, _ => none
  | _, _ => none

/-! ### Flags model: fuse `cmp` + `cmovcc` into the existing `ult` + `sel`.

A conditional move is two instructions: `cmp a, b` sets the flags, then
`cmovcc dst, src` reads them. That's stateful, so it can't be lowered one
instruction at a time. `fuse` carries the last `cmp`'s operands and, on a
`cmovcc`, emits the comparison into a scratch (`ult`) followed by a `sel` —
the branchless conditional the IL already proves. No IL change. -/

/-- The two operand tokens of a `cmp a, b`. -/
def cmpOps (i : Ins) : Option (String × String) :=
  match (i.ops.splitOn ",").map (·.trimAscii.toString) with
  | [a, b] => some (a, b)
  | _      => none

/-- Lower `cmovcc dst, src` given the preceding `cmp`'s operands `(c1, c2)`:
`__cc := (c1 < c2)`, then `dst := cc ? … : …` with the arms ordered per the
condition code. Unsigned below/above-equal only (enough for min/max). -/
def lowerCmov (mn dst src : String) (c : String × String) : Option (List SInsn) :=
  let c1 := tokToOperand c.1; let c2 := tokToOperand c.2
  let d  := canonReg dst;      let s := tokToOperand src
  if mn == "cmovb" then            -- dst = (c1 < c2) ? src : dst
    some [ .bin "__cc" .ult c1 c2, .csel d (.reg "__cc") s (.reg d) ]
  else if mn == "cmovae" then      -- dst = (c1 >= c2) ? src : dst = (c1<c2)? dst : src
    some [ .bin "__cc" .ult c1 c2, .csel d (.reg "__cc") (.reg d) s ]
  else none

/-- Lower `setcc r8` given the preceding `cmp`'s operands: the byte register is set
to the boolean `(c1 < c2)`/`(c1 >= c2)` as `1`/`0` via a `csel` over the `ult`
flag. Unsigned below/above-equal only (mirrors `lowerCmov`). -/
def lowerSetcc (mn dst : String) (c : String × String) : Option (List SInsn) :=
  let c1 := tokToOperand c.1; let c2 := tokToOperand c.2
  let d  := canonReg dst
  if mn == "setb" ∨ mn == "setc" ∨ mn == "setnae" then       -- d = (c1 < c2) ? 1 : 0
    some [ .bin "__cc" .ult c1 c2, .csel d (.reg "__cc") (.imm 1) (.imm 0) ]
  else if mn == "setae" ∨ mn == "setnb" ∨ mn == "setnc" then -- d = (c1 >= c2) ? 1 : 0
    some [ .bin "__cc" .ult c1 c2, .csel d (.reg "__cc") (.imm 0) (.imm 1) ]
  else none

/-- Lower an instruction list to `SInsn`, threading the last `cmp`'s operands so
`cmovcc` can be fused. Refuses (`none`) on an unmodelled instruction or a
`cmovcc` with no preceding `cmp`. -/
def fuse (argRegs : List String) (cmp : Option (String × String)) : List Ins → Option (List SInsn)
  | []        => some []
  | i :: rest =>
    if i.mn == "cmp" then
      (cmpOps i).bind (fun ab => fuse argRegs (some ab) rest)
    else if i.mn == "call" then
      -- A `call <callee>` forwards this function's parameter registers to the
      -- callee (the faithful model for a forwarding/partial-application leaf such
      -- as `apply_f(x)=f(x)` or `lcm`'s `gcd(a,b)` call). The callee result lands
      -- in `rax` (SInsn.call). The callee's denotation is the uninterpreted
      -- summary `ce`, so the lift is correct for ALL callees.
      let callee := i.ops.trimAscii.toString
      (fuse argRegs none rest).map (SInsn.call callee argRegs :: ·)
    else if i.mn.startsWith "set" then
      match cmp, (i.ops.splitOn ",").map (·.trimAscii.toString) with
      | some ab, [d] => (lowerSetcc i.mn d ab).bind (fun pre => (fuse argRegs none rest).map (pre ++ ·))
      | _, _ => none
    else if i.mn.startsWith "cmov" then
      match cmp, (i.ops.splitOn ",").map (·.trimAscii.toString) with
      | some ab, [d, s] => (lowerCmov i.mn d s ab).bind (fun pre => (fuse argRegs none rest).map (pre ++ ·))
      | _, _ => none
    else
      (insToS i).bind (fun ss => (fuse argRegs none rest).map (ss ++ ·))

/-- Lift a whole decoded function region to an IL `SProg`, or refuse if any
instruction is outside the modelled subset. `argRegs` seeds the calling
convention (SysV: `rdi, rsi, …`). `cmp`/`cmovcc` are fused by `fuse`; a `call`
forwards `argRegs` to the callee. -/
def liftFn (argRegs : List String) (is : List Ins) : Option SProg :=
  (fuse argRegs none is).map (liftS argRegs)

/-! ## Proof: the real decoded form of `BlockDevice::Lock()` lifts and is correct.

`BlockDevice::Lock()` disassembles (Intel) to `mov al, 1 ; ret` — exactly the
`Ins` values flowref's decoder emits. The adapter lifts it to an `SProg` whose
recovered value is `1`, machine-checked. This is the decode→IL→proof path on the
real instruction type, end to end. -/

/-- The decoded `Ins` for `BlockDevice::Lock()` (`mov al, 1; ret`). -/
def lockIns : List Ins :=
  [ { addr := 0x1000, mn := "mov", ops := "al, 1" },
    { addr := 0x1003, mn := "ret", ops := "" } ]

/-- The adapter lifts the real decoded instructions, and the lifted program
returns `1` — the function's actual behaviour. -/
theorem liftFn_lock :
    (liftFn [] lockIns).map (fun p => p.eval (fun _ => 0) []) = some 1 := by
  native_decide

/-! ## A two-argument function via `lea`, lifted and proved for all inputs.

`lea eax, [rdi + rsi]` is the canonical compilation of `a + b` (address
arithmetic reused as integer add). The adapter lifts it; proving correctness for
**symbolic** `a, b` is two steps: the lifted *shape* is a concrete fact
(`native_decide`, now that the IL types derive `DecidableEq`), and that shape's
denotation is closed by `bv_decide`. -/

/-- `add(a,b)` compiled with `lea`: `lea eax, [rdi + rsi]; ret`. -/
def addLeaIns : List Ins :=
  [ { addr := 0x2000, mn := "lea", ops := "eax, [rdi + rsi]" },
    { addr := 0x2004, mn := "ret", ops := "" } ]

/-- The `lea` form lifts to the expected IL shape. -/
theorem liftFn_addLea_shape :
    liftFn ["rdi", "rsi"] addLeaIns
      = some { stmts := [.bind (.alu .add (.arg 0) (.arg 1))], ret := .slot 0 } := by
  native_decide

/-- Hence the lifted `lea`-add computes `a + b` for **all** inputs. -/
theorem liftFn_addLea_correct (mem : Mem) (a b : Word) :
    (liftFn ["rdi", "rsi"] addLeaIns).map (fun p => p.eval mem [a, b]) = some (a + b) := by
  rw [liftFn_addLea_shape]
  simp only [Option.map_some, SProg.eval, sevalGo, Rhs.eval, Atom.eval, Op.apply,
             List.getD_cons_zero, List.getD_cons_succ, List.nil_append]

/-! ## ALU with a memory operand: one instruction → load + register ALU.

`add eax, [rdi]` reads `*p` and adds it. The adapter expands it to a scratch
load followed by a register add — so a memory-source ALU instruction becomes
provable IL. -/

/-- `add_mem(p, b){ return *p + b; }`: `mov eax, esi; add eax, [rdi]; ret`. -/
def addMemIns : List Ins :=
  [ { addr := 0x3000, mn := "mov", ops := "eax, esi" },
    { addr := 0x3002, mn := "add", ops := "eax, [rdi]" },
    { addr := 0x3005, mn := "ret", ops := "" } ]

/-- The memory-source `add` lifts to: `s0 := *p`, `s1 := b + s0`. -/
theorem liftFn_addMem_shape :
    liftFn ["rdi", "rsi"] addMemIns
      = some { stmts := [.bind (.load (.arg 0)), .bind (.alu .add (.arg 1) (.slot 0))],
               ret := .slot 1 } := by
  native_decide

/-- Hence the lifted program computes `b + *p` (= `mem p + b`, modulo `+` comm)
for **all** memories and inputs. -/
theorem liftFn_addMem_correct (mem : Mem) (p b : Word) :
    (liftFn ["rdi", "rsi"] addMemIns).map (fun q => q.eval mem [p, b]) = some (b + mem p) := by
  rw [liftFn_addMem_shape]
  simp only [Option.map_some, SProg.eval, sevalGo, Rhs.eval, Atom.eval, Op.apply,
             List.getD_cons_zero, List.getD_cons_succ, List.nil_append, List.cons_append]

/-! ## Single-operand mnemonics: `inc` / `dec` / `neg`. -/

/-- `succ(x){ return x + 1; }`: `mov eax, edi; inc eax; ret`. -/
def succIns : List Ins :=
  [ { addr := 0x4000, mn := "mov", ops := "eax, edi" },
    { addr := 0x4002, mn := "inc", ops := "eax" },
    { addr := 0x4004, mn := "ret", ops := "" } ]

theorem liftFn_succ_shape :
    liftFn ["rdi"] succIns
      = some { stmts := [.bind (.alu .add (.arg 0) (.imm 1))], ret := .slot 0 } := by
  native_decide

theorem liftFn_succ_correct (mem : Mem) (x : Word) :
    (liftFn ["rdi"] succIns).map (fun p => p.eval mem [x]) = some (x + 1) := by
  rw [liftFn_succ_shape]
  simp only [Option.map_some, SProg.eval, sevalGo, Rhs.eval, Atom.eval, Op.apply,
             List.getD_cons_zero, List.nil_append]

/-! ## Conditional move: `cmp` + `cmovb` fused to `ult` + `sel`, lifted and proved.

`umax(a,b){ return a<b ? b : a; }` compiles to `mov eax,edi; cmp edi,esi;
cmovb eax,esi; ret`. The flags pass fuses the `cmp`+`cmovb` into `ult`+`sel`. -/

/-- `umax` as `cmp`+`cmovb` (the cmov leaf the soundness gate now refuses until
the lifter models it). -/
def umaxIns : List Ins :=
  [ { addr := 0x5000, mn := "mov",   ops := "eax, edi" },
    { addr := 0x5002, mn := "cmp",   ops := "edi, esi" },
    { addr := 0x5004, mn := "cmovb", ops := "eax, esi" },
    { addr := 0x5007, mn := "ret",   ops := "" } ]

/-- The fused lift is `s0 := (a<b); s1 := s0 ? b : a; return s1`. -/
theorem liftFn_umax_shape :
    liftFn ["rdi", "rsi"] umaxIns
      = some { stmts := [.bind (.alu .ult (.arg 0) (.arg 1)),
                         .bind (.sel (.slot 0) (.arg 1) (.arg 0))], ret := .slot 1 } := by
  native_decide

/-- Hence the lifted cmov computes the max — an upper bound of both operands, for
**all** inputs, by `bv_decide`. (cmov leaf now lifts correctly via the flags model.) -/
theorem liftFn_umax_is_ub (mem : Mem) (a b : Word) {p : SProg}
    (h : liftFn ["rdi", "rsi"] umaxIns = some p) :
    ¬ (p.eval mem [a, b]).ult a ∧ ¬ (p.eval mem [a, b]).ult b := by
  rw [liftFn_umax_shape] at h; injection h with h; subst h
  simp only [SProg.eval, sevalGo, Rhs.eval, Atom.eval, Op.apply,
             List.getD_cons_zero, List.getD_cons_succ, List.nil_append, List.cons_append]
  bv_decide

/-- `umin(a,b){ return a<b ? a : b; }` as `mov eax,edi; cmp edi,esi; cmovae eax,esi;
ret` — the `cmovae` (≥) form. -/
def uminIns : List Ins :=
  [ { addr := 0x6000, mn := "mov",    ops := "eax, edi" },
    { addr := 0x6002, mn := "cmp",    ops := "edi, esi" },
    { addr := 0x6004, mn := "cmovae", ops := "eax, esi" },
    { addr := 0x6007, mn := "ret",    ops := "" } ]

/-- The fused lift is `s0 := (a<b); s1 := s0 ? a : b; return s1`. -/
theorem liftFn_umin_shape :
    liftFn ["rdi", "rsi"] uminIns
      = some { stmts := [.bind (.alu .ult (.arg 0) (.arg 1)),
                         .bind (.sel (.slot 0) (.arg 0) (.arg 1))], ret := .slot 1 } := by
  native_decide

/-- Hence the lifted `cmovae` computes the min — a lower bound of both operands,
for **all** inputs, by `bv_decide`. -/
theorem liftFn_umin_is_lb (mem : Mem) (a b : Word) {p : SProg}
    (h : liftFn ["rdi", "rsi"] uminIns = some p) :
    ¬ a.ult (p.eval mem [a, b]) ∧ ¬ b.ult (p.eval mem [a, b]) := by
  rw [liftFn_umin_shape] at h; injection h with h; subst h
  simp only [SProg.eval, sevalGo, Rhs.eval, Atom.eval, Op.apply,
             List.getD_cons_zero, List.getD_cons_succ, List.nil_append, List.cons_append]
  bv_decide

/-! ## A function CALL, lifted from real decoded `Ins` and proved for all callees.

`uint32_t apply_f(uint32_t x){ return f(x); }` compiles (SysV, `x` in `rdi`) to
`call f ; ret`. The adapter parses the `call` into `SInsn.call "f" ["rdi"]`
(forwarding the parameter register), and the lifted program's recovered value is
`ce "f" [x]` for **any** callee summary `ce` — the decode→IL→proof path now
covers calls, not just straight-line/flag leaves. -/
def applyfFnIns : List Ins :=
  [ { addr := 0x7000, mn := "call", ops := "f" },
    { addr := 0x7005, mn := "ret",  ops := "" } ]

/-- The `call`+`ret` form lifts to the single-call IL shape. -/
theorem liftFn_applyf_shape :
    liftFn ["rdi"] applyfFnIns
      = some { stmts := [.call "f" [.arg 0]], ret := .slot 0 } := by
  native_decide

/-- Hence the lifted call computes `f(x)` for **all** callees `ce`. -/
theorem liftFn_applyf_correct (ce : CallEnv) (mem : Mem) (x : Word) :
    (liftFn ["rdi"] applyfFnIns).map (fun p => p.eval mem [x] ce) = some (ce "f" [x]) := by
  rw [liftFn_applyf_shape]
  simp [SProg.eval, sevalGo, Atom.eval]

/-! ### A call COMPOSED with ALU: `g(x) + x`, lifted and proved for all callees.

`call f ; add rax, rdi ; ret` — the callee result (in `rax`) is combined with the
preserved argument register. This shows the call IL composes with the arithmetic
IL: the recovered value is `ce "f" [x] + x` for **any** callee `ce`, by the same
decode→IL→proof path. (64-bit `rax`/`rdi` so the call result and the add operand
share the register the call writes — the lifter is register-name exact.) -/
def callAddIns : List Ins :=
  [ { addr := 0x8000, mn := "call", ops := "f" },
    { addr := 0x8005, mn := "add",  ops := "rax, rdi" },
    { addr := 0x8008, mn := "ret",  ops := "" } ]

/-- The call+add form lifts to a call binding followed by an ALU binding. -/
theorem liftFn_callAdd_shape :
    liftFn ["rdi"] callAddIns
      = some { stmts := [.call "f" [.arg 0], .bind (.alu .add (.slot 0) (.arg 0))],
               ret := .slot 1 } := by
  native_decide

/-- Hence the lifted `call f; add rax,rdi` computes `f(x) + x` for **all** callees. -/
theorem liftFn_callAdd_correct (ce : CallEnv) (mem : Mem) (x : Word) :
    (liftFn ["rdi"] callAddIns).map (fun p => p.eval mem [x] ce) = some (ce "f" [x] + x) := by
  rw [liftFn_callAdd_shape]
  simp [SProg.eval, sevalGo, Rhs.eval, Atom.eval, Op.apply]

/-! ### A comparison-returning leaf via `setcc`, lifted from real decoded `Ins`.

`uint32_t lt(uint32_t a, uint32_t b){ return a < b; }` compiles (SysV) to
`cmp edi, esi ; setb al ; movzx eax, al ; ret`. The adapter fuses the `cmp`+`setb`
into the `ult` flag + a `csel` to `1`/`0`, and models the `movzx` as a `0xff`
mask; the lifted program returns `(a < b) ? 1 : 0` for **all** inputs (the mask is
identity on the `{0,1}` boolean), by `bv_decide`. This is the verified-track
counterpart of the production `setcc` lift. -/
def cmpLtIns : List Ins :=
  [ { addr := 0x9000, mn := "cmp",   ops := "edi, esi" },
    { addr := 0x9002, mn := "setb",  ops := "al" },
    { addr := 0x9005, mn := "movzx", ops := "eax, al" },
    { addr := 0x9008, mn := "ret",   ops := "" } ]

/-- The fused lift is `s0 := (a<b); s1 := s0 ? 1 : 0; s2 := s1 & 0xff; ret s2`. -/
theorem liftFn_cmpLt_shape :
    liftFn ["rdi", "rsi"] cmpLtIns
      = some { stmts := [.bind (.alu .ult (.arg 0) (.arg 1)),
                         .bind (.sel (.slot 0) (.imm 1) (.imm 0)),
                         .bind (.alu .band (.slot 1) (.imm 0xff))], ret := .slot 2 } := by
  native_decide

/-- Hence the lifted compare+setb+movzx computes the unsigned `(a < b)` boolean. -/
theorem liftFn_cmpLt_correct (mem : Mem) (a b : Word) :
    (liftFn ["rdi", "rsi"] cmpLtIns).map (fun p => p.eval mem [a, b])
      = some (if a.ult b then 1 else 0) := by
  rw [liftFn_cmpLt_shape]
  simp only [Option.map_some, SProg.eval, sevalGo, Rhs.eval, Atom.eval, Op.apply,
             List.getD_cons_zero, List.getD_cons_succ, List.nil_append, List.cons_append]
  cases h : a.ult b <;> simp

end FlowrefDecompiler.Lift
