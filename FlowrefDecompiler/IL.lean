import Std.Tactic.BVDecide
import LeanSlang

/-! # flowref IL — a BitVec SSA core, proved with `bv_decide` (no oracle)

This is the proof target I proposed: a tiny, total, SSA expression language whose
denotation is a plain Lean function over `BitVec 32`. Because every value is a
fixed-width two's-complement word, equivalence obligations are *decided* by
`bv_decide` (bitblast → SAT) — a real machine-checked theorem, replacing the
`plausible` random-tuple search in `EquivCheck.lean`. -/

namespace FlowrefDecompiler.IL

abbrev Word := BitVec 32

/-- The operations flowref already lifts for leaf functions. -/
inductive Op | add | sub | mul | band | bor | bxor | shl | ult
  deriving DecidableEq, Repr

/-- An operand: a function argument, an earlier SSA slot, or an immediate.
This is exactly the shape of the lifted C (`eax_1 = eax_0 + a1`): `arg` = a
parameter, `slot` = a prior `eax_n`, `imm` = a literal. -/
inductive Atom | arg (i : Nat) | slot (i : Nat) | imm (w : Word)
  deriving Repr

/-- One SSA binding: `slot_next := op a b`. -/
structure Bind where
  op : Op
  a  : Atom
  b  : Atom
  deriving Repr

/-- A leaf function: ordered SSA bindings + the returned atom. -/
structure Prog where
  binds : List Bind
  ret   : Atom
  deriving Repr

@[simp] def Op.apply : Op → Word → Word → Word
  | .add,  x, y => x + y
  | .sub,  x, y => x - y
  | .mul,  x, y => x * y
  | .band, x, y => x &&& y
  | .bor,  x, y => x ||| y
  | .bxor, x, y => x ^^^ y
  | .shl,  x, y => x <<< y
  | .ult,  x, y => if x.ult y then 1 else 0   -- unsigned compare → C-style 0/1

@[simp] def Atom.eval (args slots : List Word) : Atom → Word
  | .arg i  => args.getD i 0
  | .slot i => slots.getD i 0
  | .imm w  => w

/-- Thread the SSA slots left-to-right; when bindings are exhausted, read `ret`. -/
@[simp] def evalGo (args : List Word) (ret : Atom) : List Bind → List Word → Word
  | [],      slots => ret.eval args slots
  | b :: bs, slots =>
      evalGo args ret bs (slots ++ [b.op.apply (b.a.eval args slots) (b.b.eval args slots)])

/-- Evaluate a program against an argument list. -/
@[simp] def Prog.eval (p : Prog) (args : List Word) : Word :=
  evalGo args p.ret p.binds []

/-! ## The demo functions, lifted into the IL.

These mirror `decompile-bench/equiv-demo.sh` exactly. -/

open Op Atom

/-- `uint32_t p_add(a,b){ return a + b; }` → `eax_0 = a0; eax_1 = eax_0 + a1`. -/
def p_add : Prog := { binds := [⟨add, arg 0, arg 1⟩], ret := slot 0 }
/-- `uint32_t p_xor(a,b){ return a ^ b; }` -/
def p_xor : Prog := { binds := [⟨bxor, arg 0, arg 1⟩], ret := slot 0 }
/-- `uint32_t p_mul(a,b){ return a * b; }` -/
def p_mul : Prog := { binds := [⟨mul, arg 0, arg 1⟩], ret := slot 0 }
/-- `uint32_t kxor(){ uint32_t x = 0xff; return x ^ 0x0f; }` -/
def kxor  : Prog := { binds := [⟨bxor, imm 0xff, imm 0x0f⟩], ret := slot 0 }
/-- `uint32_t kchain(){ x=10; x=x+5; x=x-3; return x; }` -/
def kchain : Prog :=
  { binds := [⟨add, imm 10, imm 0⟩, ⟨add, slot 0, imm 5⟩, ⟨sub, slot 1, imm 3⟩], ret := slot 2 }

/-! ## Real proofs — `bv_decide`, not a tuple search.

Each theorem is `∀ args, lift args = spec args`, discharged by bitblasting. For
the parameterised ones this is the universally-quantified statement the oracle
could only *sample*. -/

theorem p_add_correct (a b : Word) : p_add.eval [a, b] = a + b := by
  simp [p_add, Prog.eval, evalGo]

theorem p_xor_correct (a b : Word) : p_xor.eval [a, b] = a ^^^ b := by
  simp [p_xor, Prog.eval, evalGo]

theorem p_mul_correct (a b : Word) : p_mul.eval [a, b] = a * b := by
  simp [p_mul, Prog.eval, evalGo]

theorem kxor_correct : kxor.eval [] = 240 := by
  simp [kxor, Prog.eval, evalGo]

theorem kchain_correct : kchain.eval [] = 12 := by
  simp [kchain, Prog.eval, evalGo]

/-- A property the random oracle would *never* certify but `bv_decide` proves:
`p_add` and the swapped-arg version are equal for **all** 2^64 inputs. -/
theorem p_add_comm (a b : Word) : p_add.eval [a, b] = p_add.eval [b, a] := by
  simp only [p_add, Prog.eval, evalGo, Atom.eval, Op.apply,
             List.getD_cons_zero, List.getD_cons_succ, List.nil_append]
  bv_decide

/-! ## Slang backend: render to the real lean-slang AST, proved meaning-preserving.

`render` lowers an IL program to `LeanSlang.SlangExpr` — the same AST
`LeanSlang.Emit` pretty-prints to `slangc`-accepted source — and we prove the
render preserves meaning against `LeanSlang.evalU32`, the BitVec semantics that
ships with lean-slang. SSA slots are inlined into the expression; `arg i`
becomes the shader parameter named `aᵢ`.

The payoff: instead of `EquivCheck.lean` shelling out to `cc` + `dlopen` to
*run* the emitted code, the **emitted artifact is the proof object** — nothing
compiles, nothing executes. The only trusted edge left is `libslang`'s
Slang→SPIR-V translation, which is Khronos's problem, not ours. -/

open LeanSlang

/-- Map an IL op to the exact operator string `LeanSlang.Emit` prints (and
`LeanSlang.binOpU32` interprets) — so render, printer, and semantics agree. -/
@[simp] def Op.slangOp : Op → String
  | .add => "+" | .sub => "-" | .mul => "*"
  | .band => "&" | .bor => "|" | .bxor => "^" | .shl => "<<" | .ult => "<"

/-- The Slang parameter name for argument `i`. -/
@[simp] def argName (i : Nat) : String := "a" ++ toString i

/-- Lower an atom: args → shader params, slots → their rendered expr, imm → a
`uint` literal. -/
@[simp] def Atom.toSlang (slots : List SlangExpr) : Atom → SlangExpr
  | .arg i  => .var (argName i)
  | .slot i => slots.getD i (.litUint 0)
  | .imm w  => .litUint w.toNat

/-- Inline the SSA slots left-to-right, then render the returned atom. -/
@[simp] def renderGo (ret : Atom) : List Bind → List SlangExpr → SlangExpr
  | [],      slots => ret.toSlang slots
  | b :: bs, slots =>
      renderGo ret bs (slots ++ [.bin b.op.slangOp (b.a.toSlang slots) (b.b.toSlang slots)])

/-- IL program → one scalar `LeanSlang.SlangExpr`. -/
@[simp] def Prog.render (p : Prog) : SlangExpr := renderGo p.ret p.binds []

/-- Two-argument environment: `a0 ↦ a`, `a1 ↦ b`, everything else `0`. -/
def env2 (a b : Word) : UEnv := fun n => if n = "a0" then a else if n = "a1" then b else 0

/-! ### render-correctness: the emitted Slang means exactly what the IL means.

`evalU32` returns `Option` (it is partial outside the uint fragment); these
theorems land on `some _`, certifying the render stays inside that fragment. -/

theorem p_add_render (a b : Word) :
    (p_add.render).evalU32 (env2 a b) = some (p_add.eval [a, b]) := by
  simp +decide [p_add, env2]

theorem p_xor_render (a b : Word) :
    (p_xor.render).evalU32 (env2 a b) = some (p_xor.eval [a, b]) := by
  simp +decide [p_xor, env2]

theorem kchain_render :
    (kchain.render).evalU32 (env2 0 0) = some (kchain.eval []) := by
  simp +decide

/-- End to end: the rendered Slang for `p_add` computes `a + b` for **all**
inputs — render-correctness composed with the IL spec. -/
theorem p_add_render_spec (a b : Word) :
    (p_add.render).evalU32 (env2 a b) = some (a + b) := by
  simp +decide [p_add, env2]

/-! ## Memory: read-only loads — growing the class past register-only leaves.

The corpus measurement (random 500-function Decompile-Bench sample) found ~0%
of real functions are register-only leaves; the binding constraint is memory.
This adds a `Word`-addressed load: a straight-line function may now dereference
pointers (no stores / calls / branches yet) — the nearest reachable real-corpus
tier. `bv_decide` still discharges equivalence: memory reads appear as
applications of an opaque `Mem`, abstracted uniformly on both sides. -/

/-- A word-addressed memory: address → 32-bit value. -/
abbrev Mem := Word → Word

/-- A binding right-hand side: an ALU op, or a load `*(uint32_t*)addr`. -/
inductive Rhs
  | alu  (op : Op) (a b : Atom)
  | load (addr : Atom)
  | sel  (c x y : Atom)   -- branchless conditional move: `c ≠ 0 ? x : y`
  deriving Repr

/-- A leaf function with read-only memory. -/
structure MProg where
  binds : List Rhs
  ret   : Atom
  deriving Repr

@[simp] def Rhs.eval (mem : Mem) (args slots : List Word) : Rhs → Word
  | .alu op a b => op.apply (a.eval args slots) (b.eval args slots)
  | .load addr  => mem (addr.eval args slots)
  | .sel c x y  => if c.eval args slots ≠ 0 then x.eval args slots else y.eval args slots

/-- Thread the SSA slots left-to-right under a fixed memory, then read `ret`. -/
@[simp] def mevalGo (mem : Mem) (args : List Word) (ret : Atom) : List Rhs → List Word → Word
  | [],      slots => ret.eval args slots
  | r :: rs, slots => mevalGo mem args ret rs (slots ++ [r.eval mem args slots])

@[simp] def MProg.eval (mem : Mem) (p : MProg) (args : List Word) : Word :=
  mevalGo mem args p.ret p.binds []

open Rhs

/-- `uint32_t load_add(uint32_t* p){ return p[0] + p[1]; }` — reads the words at
`p` and `p+4`. Straight-line, two loads, no store/call/branch. -/
def load_add : MProg :=
  { binds := [ load (arg 0)                 -- slot0 = *p
             , alu add (arg 0) (imm 4)       -- slot1 = p + 4
             , load (slot 1)                 -- slot2 = *(p+4)
             , alu add (slot 0) (slot 2) ]   -- slot3 = slot0 + slot2
  , ret := slot 3 }

/-- The lift means exactly `mem[p] + mem[p+4]`, for **all** memories and `p`. -/
theorem load_add_correct (mem : Mem) (p : Word) :
    load_add.eval mem [p] = mem p + mem (p + 4) := by
  simp [load_add, MProg.eval, mevalGo]

/-- Equivalence under memory: summing the two loads in the other order gives the
same value — `bv_decide`, with the loads abstracted as opaque terms. -/
theorem load_add_comm (mem : Mem) (p : Word) :
    load_add.eval mem [p] = mem (p + 4) + mem p := by
  simp only [load_add, MProg.eval, mevalGo, Rhs.eval, Atom.eval, Op.apply,
             List.getD_cons_zero, List.getD_cons_succ, List.nil_append, List.cons_append]
  bv_decide

/-! ### Rendering memory to Slang, proved meaning-preserving.

A load renders to a Slang buffer read `mem[addr]` (`SlangExpr.index`), and we
prove the render preserves meaning against `LeanSlang.evalU32M` — the
memory-aware semantics. The buffer stays abstract, so the theorem holds for all
memories; nothing is compiled or run. -/

/-- Lower an Rhs: ALU → `bin`, load → the buffer read `mem[addr]`. -/
@[simp] def Rhs.toSlang (slots : List SlangExpr) : Rhs → SlangExpr
  | .alu op a b => .bin op.slangOp (a.toSlang slots) (b.toSlang slots)
  | .load addr  => .index (.var "mem") (addr.toSlang slots)
  | .sel c x y  => .ternary (c.toSlang slots) (x.toSlang slots) (y.toSlang slots)

/-- Inline the SSA slots left-to-right, then render the returned atom. -/
@[simp] def mrenderGo (ret : Atom) : List Rhs → List SlangExpr → SlangExpr
  | [],      slots => ret.toSlang slots
  | r :: rs, slots => mrenderGo ret rs (slots ++ [r.toSlang slots])

/-- Memory-IL program → one `LeanSlang.SlangExpr` (reads become `mem[…]`). -/
@[simp] def MProg.render (p : MProg) : SlangExpr := mrenderGo p.ret p.binds []

/-- IL memory → the Slang buffer environment for the buffer named `mem`. -/
def memEnv (mem : Mem) : MEnv := fun buf a => if buf = "mem" then mem a else 0

/-- render-correctness with memory: the emitted Slang (with `mem[…]` reads)
means exactly what the memory-IL means, for **all** memories. -/
theorem load_add_render (mem : Mem) (p : Word) :
    (load_add.render).evalU32M (env2 p 0) (memEnv mem) = some (load_add.eval mem [p]) := by
  simp +decide [load_add, env2, memEnv, MProg.eval, mevalGo]

/-! ## Stores: memory as threaded state, with aliasing reasoning.

A store mutates memory, so it is a *statement*, not a value-binding: evaluation
now threads `(slots, mem)` state. The payoff is that `bv_decide` reasons about
**aliasing** — proving `store_two` returns `a + b` requires knowing the two
stored addresses `p` and `p+4` are distinct, which `bv_decide` decides. -/

/-- A statement: bind a value into the next SSA slot, or store a value to memory. -/
inductive Stmt
  | bind  (rhs : Rhs)
  | store (addr val : Atom)
  deriving Repr

/-- A leaf function with mutable memory. -/
structure SProg where
  stmts : List Stmt
  ret   : Atom
  deriving Repr

/-- Point update of a memory at one address. -/
@[simp] def Mem.upd (mem : Mem) (addr val : Word) : Mem := fun x => if x = addr then val else mem x

/-- Thread `(slots, mem)` through the statements, then read `ret`. -/
@[simp] def sevalGo (args : List Word) (ret : Atom) : List Stmt → List Word → Mem → Word
  | [],                 slots, _   => ret.eval args slots
  | .bind rhs  :: rest, slots, mem => sevalGo args ret rest (slots ++ [rhs.eval mem args slots]) mem
  | .store a v :: rest, slots, mem => sevalGo args ret rest slots (mem.upd (a.eval args slots) (v.eval args slots))

@[simp] def SProg.eval (mem : Mem) (p : SProg) (args : List Word) : Word :=
  sevalGo args p.ret p.stmts [] mem

/-- `uint32_t store_two(uint32_t* p, uint32_t a, uint32_t b){ p[0]=a; p[1]=b;
    return p[0] + p[1]; }` — distinct addresses, so the result is `a + b`. -/
def store_two : SProg :=
  { stmts := [ .store (arg 0) (arg 1)          -- *p = a
             , .bind (alu add (arg 0) (imm 4))  -- slot0 = p + 4
             , .store (slot 0) (arg 2)          -- *(p+4) = b
             , .bind (load (arg 0))             -- slot1 = *p
             , .bind (load (slot 0))            -- slot2 = *(p+4)
             , .bind (alu add (slot 1) (slot 2)) ] -- slot3 = slot1 + slot2
  , ret := slot 3 }

/-- The second store does not clobber the first read: `p ≠ p+4`, so the result is
`a + b` for **all** memories — the no-aliasing fact is discharged by `bv_decide`. -/
theorem store_two_correct (mem : Mem) (p a b : Word) :
    store_two.eval mem [p, a, b] = a + b := by
  simp only [store_two, SProg.eval, sevalGo, Rhs.eval, Atom.eval, Op.apply, Mem.upd,
             List.getD_cons_zero, List.getD_cons_succ, List.nil_append, List.cons_append]
  bv_decide

/-! ### Rendering stores to Slang statements, proved meaning-preserving.

Stores are statements, so this renderer emits a `List SlangStmt` (named SSA
locals + `mem[idx] = val` assigns + a `return`) rather than one inlined
expression, and we prove it against `LeanSlang.evalStmtsU32M` — the statement
semantics. Slots become named locals `sᵢ`; stores become buffer assigns. -/

/-- The Slang local name for SSA slot `i`. -/
@[simp] def slotName (i : Nat) : String := "s" ++ toString i

/-- Atom → Slang expression for the statement path: slots are *named locals*. -/
@[simp] def Atom.toSlangS : Atom → SlangExpr
  | .arg i  => .var (argName i)
  | .slot i => .var (slotName i)
  | .imm w  => .litUint w.toNat

/-- Rhs → Slang expression (ALU → `bin`, load → `mem[addr]`). -/
@[simp] def Rhs.toSlangS : Rhs → SlangExpr
  | .alu op a b => .bin op.slangOp a.toSlangS b.toSlangS
  | .load addr  => .index (.var "mem") addr.toSlangS
  | .sel c x y  => .ternary c.toSlangS x.toSlangS y.toSlangS

/-- Emit statements, naming each bound slot `sₖ`; stores don't advance `k`. -/
@[simp] def srenderGo (k : Nat) : List Stmt → List SlangStmt
  | [] => []
  | .bind rhs  :: rest => .declare (.scalar .uint) (slotName k) (some rhs.toSlangS) :: srenderGo (k+1) rest
  | .store a v :: rest => .assign (.index (.var "mem") a.toSlangS) v.toSlangS :: srenderGo k rest

/-- Memory-IL program → a Slang statement body ending in `return ret;`. -/
@[simp] def SProg.render (p : SProg) : List SlangStmt :=
  srenderGo 0 p.stmts ++ [.ret (some p.ret.toSlangS)]

/-- render-correctness for stores: the emitted Slang statement body means exactly
what the memory-IL means, for **all** memories (aliasing closed by `bv_decide`). -/
theorem store_two_render (mem : Mem) (p a b : Word) :
    evalStmtsU32M
      (fun n => if n = "a0" then p else if n = "a1" then a else if n = "a2" then b else 0)
      (memEnv mem) (store_two.render)
      = some (store_two.eval mem [p, a, b]) := by
  simp +decide only [store_two, SProg.render, srenderGo, Rhs.toSlangS, Atom.toSlangS,
             Op.slangOp, slotName, argName, evalStmtsU32M, SlangExpr.evalU32M, binOpU32,
             UEnv.set, MEnv.store, memEnv, SProg.eval, sevalGo, Rhs.eval, Atom.eval, Op.apply,
             Mem.upd, List.getD_cons_zero, List.getD_cons_succ, List.nil_append, List.cons_append,
             reduceIte, Option.some.injEq,]
  bv_decide

/-! ## Control flow: branchless select (cmov), proved with bv_decide.

The proof-friendly entry into control flow is a conditional *move*: `c ≠ 0 ? x : y`
— branchless, so it bitblasts. Combined with the `ult` comparison it expresses
`max`/`min`, the canonical leaf-function conditionals (compilers emit `cmov`,
not a branch). It renders to a Slang `ternary`, proved against `evalU32M`. -/

/-- `uint32_t umax(uint32_t a, uint32_t b){ return (a < b) ? b : a; }`. -/
def umax : MProg :=
  { binds := [ alu ult (arg 0) (arg 1)       -- slot0 = (a < b) ? 1 : 0
             , sel (slot 0) (arg 1) (arg 0) ] -- slot1 = slot0 ? b : a
  , ret := slot 1 }

/-- The result is an upper bound of both operands — the defining property of
`max`, for **all** inputs, by `bv_decide`. (Memory is irrelevant here.) -/
theorem umax_is_ub (mem : Mem) (a b : Word) :
    ¬ (umax.eval mem [a, b]).ult a ∧ ¬ (umax.eval mem [a, b]).ult b := by
  simp only [umax, MProg.eval, mevalGo, Rhs.eval, Atom.eval, Op.apply,
             List.getD_cons_zero, List.getD_cons_succ, List.nil_append, List.cons_append]
  bv_decide

/-- render-correctness: the emitted Slang `ternary` means exactly `umax.eval`. -/
theorem umax_render (mem : Mem) (a b : Word) :
    (umax.render).evalU32M (env2 a b) (memEnv mem) = some (umax.eval mem [a, b]) := by
  simp +decide [umax, env2, MProg.eval, mevalGo]

/-! ### Branching `if`/return: rendering a terminal select as control flow.

A terminal conditional can render two ways: an expression `ternary` (above), or
a branching statement `if (c) return x; else return y;`. This proves the latter
form against `LeanSlang.evalStmtsU32M` — real `SlangStmt.ifThen` control flow,
meaning-preserving against the same IL `sel`. -/

/-- A terminal select rendered as a branching `if`/return statement body. -/
@[simp] def selBranch (c x y : Atom) : List SlangStmt :=
  [ .ifThen c.toSlangS [ .ret (some x.toSlangS) ] [ .ret (some y.toSlangS) ] ]

/-- `uint32_t cond_sel(uint32_t c, uint32_t x, uint32_t y){ return c ? x : y; }`. -/
def cond_sel : MProg := { binds := [ sel (arg 0) (arg 1) (arg 2) ], ret := slot 0 }

/-- The branching `if`/return render means exactly the IL select, for all inputs. -/
theorem cond_sel_render_branch (mem : Mem) (c x y : Word) :
    evalStmtsU32M
      (fun n => if n = "a0" then c else if n = "a1" then x else if n = "a2" then y else 0)
      (memEnv mem) (selBranch (arg 0) (arg 1) (arg 2))
      = some (cond_sel.eval mem [c, x, y]) := by
  simp only [cond_sel, selBranch, Atom.toSlangS, argName, evalStmtsU32M, SlangExpr.evalU32M,
             MProg.eval, mevalGo, Rhs.eval, Atom.eval,
             List.getD_cons_zero, List.getD_cons_succ, List.nil_append]
  exact (apply_ite some (c ≠ 0) x y).symm

/-! ## Bounded loops: a fixed trip count unrolls to straight-line IL.

A `while`/`for` with a *symbolic* bound needs a loop invariant + induction —
outside what `bv_decide` discharges. But a loop with a *constant* trip count is
**unrolled** into straight-line bindings, which `bv_decide` proves like any
other leaf. This is faithful: flowref unrolls fixed-count loops, so the proof
obligation is the unrolled body. (Symbolic-bound loops are the next regime, and
require a different technique — noted, not faked.) -/

/-- `uint32_t times8(uint32_t x){ for (i=0;i<3;i++) x += x; return x; }` —
the 3-iteration loop unrolled to three doubling bindings. -/
def times8 : Prog :=
  { binds := [ ⟨add, arg 0, arg 0⟩      -- iter 0: 2x
             , ⟨add, slot 0, slot 0⟩    -- iter 1: 4x
             , ⟨add, slot 1, slot 1⟩ ]  -- iter 2: 8x
  , ret := slot 2 }

/-- The unrolled loop computes `x <<< 3` (= 8·x), for **all** `x`, by `bv_decide` —
the closed form of the bounded loop. -/
theorem times8_correct (x : Word) : times8.eval [x] = 8 * x := by
  simp only [times8, Prog.eval, evalGo, Atom.eval, Op.apply,
             List.getD_cons_zero, List.getD_cons_succ, List.nil_append, List.cons_append]
  bv_decide

/-- render-correctness: the emitted Slang for the unrolled loop means exactly
`times8.eval` — bounded loops reuse the existing expression render. -/
theorem times8_render (x : Word) :
    (times8.render).evalU32 (env2 x 0) = some (times8.eval [x]) := by
  simp +decide [times8, env2, Prog.eval, evalGo]

/-! ## Symbolic-bound loops: correctness by induction (beyond bv_decide).

A loop whose trip count `n` is a runtime value cannot be unrolled, so `bv_decide`
— which bitblasts a *finite* term — cannot close it. The honest technique is to
state a loop invariant and prove it by induction on `n`; the per-iteration
arithmetic is still discharged automatically (here by `bv_omega`). This is a
different, necessary regime from the finite fragment above, and we label it as
such rather than pretend `bv_decide` reaches it. -/

/-- `uint32_t addn(uint32_t x, uint32_t n){ for (i=0;i<n;i++) x += 1; return x; }`,
modelled as a fold over the runtime trip count `n`. -/
def addLoop : Nat → Word → Word
  | 0,     x => x
  | n + 1, x => addLoop n x + 1

/-- The loop adds `n` to `x`, for **all** trip counts `n` and inputs `x` — proved
by induction on the symbolic `n`, the step closed by `bv_omega`. Not `bv_decide`:
`n` is unbounded, so the term is not finite. -/
theorem addLoop_correct (n : Nat) (x : Word) : addLoop n x = x + BitVec.ofNat 32 n := by
  induction n with
  | zero => simp [addLoop]
  | succ k ih => rw [addLoop, ih]; bv_omega

/-- Render-correctness for the loop, via its **closed form**: a decompiler may
strength-reduce `for(i<n) x+=1` to `x + n`, and the emitted Slang `(a0 + a1)`
provably equals the loop for **all** trip counts. This composes the induction
proof (`addLoop_correct`) with the expression render — the loop's meaning,
rendered to Slang, machine-checked end to end. -/
theorem addLoop_render (x n : Word) :
    (p_add.render).evalU32 (env2 x n) = some (addLoop n.toNat x) := by
  have h : addLoop n.toNat x = x + n := by rw [addLoop_correct]; bv_omega
  rw [h]; simp +decide [p_add, env2]

/-! ## Composition: a realistic leaf combining every construct.

Each tier above was proved in isolation; a real lifted function uses them
together. `clamp_min` loads `*p`, computes `min(v, *p)` via compare + select,
stores it back, then returns the read-back value — exercising load, `ult`,
`sel`, store, and read-after-write in one body. Both the spec and the
statement-level render-correctness are still closed by `bv_decide`, showing the
fragment composes, not just its pieces. -/

/-- `uint32_t clamp_min(uint32_t* p, uint32_t v){ uint x=*p; uint r=(v<x)?v:x;
    *p=r; return *p; }`. -/
def clamp_min : SProg :=
  { stmts := [ .bind (load (arg 0))                  -- s0 = *p
             , .bind (alu ult (arg 1) (slot 0))       -- s1 = (v < *p) ? 1 : 0
             , .bind (sel (slot 1) (arg 1) (slot 0))  -- s2 = (v < *p) ? v : *p  = min
             , .store (arg 0) (slot 2)                -- *p = s2
             , .bind (load (arg 0)) ]                 -- s3 = *p  (= s2; same address)
  , ret := slot 3 }

/-- The result is a lower bound of both `v` and `*p` — the defining property of
`min`, for **all** memories and inputs, by `bv_decide` (read-after-write and the
opaque load both handled). -/
theorem clamp_min_is_lb (mem : Mem) (p v : Word) :
    (clamp_min.eval mem [p, v]).ule v ∧ (clamp_min.eval mem [p, v]).ule (mem p) := by
  simp only [clamp_min, SProg.eval, sevalGo, Rhs.eval, Atom.eval, Op.apply, Mem.upd,
             List.getD_cons_zero, List.getD_cons_succ, List.nil_append, List.cons_append]
  bv_decide

/-- render-correctness for the composite: the emitted Slang statement body (load,
ternary, store, read-back) means exactly `clamp_min.eval`, for all memories. -/
theorem clamp_min_render (mem : Mem) (p v : Word) :
    evalStmtsU32M
      (fun n => if n = "a0" then p else if n = "a1" then v else 0)
      (memEnv mem) (clamp_min.render)
      = some (clamp_min.eval mem [p, v]) := by
  simp +decide only [clamp_min, SProg.render, srenderGo, Rhs.toSlangS, Atom.toSlangS,
             Op.slangOp, slotName, argName, evalStmtsU32M, SlangExpr.evalU32M, binOpU32,
             UEnv.set, MEnv.store, memEnv, SProg.eval, sevalGo, Rhs.eval, Atom.eval, Op.apply,
             Mem.upd, List.getD_cons_zero, List.getD_cons_succ, List.nil_append, List.cons_append,
             reduceIte]

/-! ## Function calls: the ~87% unlock, callee as an uninterpreted summary.

The corpus measurement found ~87% of real functions *call* another — the single
biggest gap. A call to a known callee is modelled here as application of an
**uninterpreted summary** `ce : CallEnv` (callee name → denotation); `bv_decide`
abstracts each `ce f args` as an opaque term, exactly as it did for memory
loads, so a function that calls and combines results is still provable for **all**
possible callees. (Render to Slang `call` needs a function env in lean-slang's
evaluator — a signature change there — so it is the next increment.) -/

/-- A callee environment: a callee name + arguments denote a result word. -/
abbrev CallEnv := String → List Word → Word

/-- A call-extended binding RHS: an ALU op, or a call to a named callee. -/
inductive CRhs
  | alu  (op : Op) (a b : Atom)
  | call (callee : String) (args : List Atom)
  deriving Repr

/-- A leaf function that may call other functions. -/
structure CProg where
  binds : List CRhs
  ret   : Atom
  deriving Repr

@[simp] def CRhs.eval (ce : CallEnv) (args slots : List Word) : CRhs → Word
  | .alu op a b => op.apply (a.eval args slots) (b.eval args slots)
  | .call f as  => ce f (as.map (·.eval args slots))

@[simp] def cevalGo (ce : CallEnv) (args : List Word) (ret : Atom) : List CRhs → List Word → Word
  | [],      slots => ret.eval args slots
  | r :: rs, slots => cevalGo ce args ret rs (slots ++ [r.eval ce args slots])

@[simp] def CProg.eval (ce : CallEnv) (p : CProg) (args : List Word) : Word :=
  cevalGo ce args p.ret p.binds []

/-- `uint32_t double_call(uint32_t x){ return f(x) + f(x); }`. -/
def double_call : CProg :=
  { binds := [ .call "f" [arg 0]                -- s0 = f(x)
             , .call "f" [arg 0]                -- s1 = f(x)
             , .alu add (slot 0) (slot 1) ]     -- s2 = s0 + s1
  , ret := slot 2 }

/-- For **any** callee `f`, `f(x) + f(x) = 2·f(x)` — the call result is abstracted
as an opaque term by `bv_decide`, so the proof holds whatever `f` computes. -/
theorem double_call_correct (ce : CallEnv) (x : Word) :
    double_call.eval ce [x] = 2 * ce "f" [x] := by
  simp only [double_call, CProg.eval, cevalGo, CRhs.eval, Atom.eval, Op.apply,
             List.map_cons, List.map_nil, List.getD_cons_zero, List.getD_cons_succ,
             List.nil_append, List.cons_append]
  bv_decide

/-! ### Compositional calls: a concrete callee proven end to end.

`double_call_correct` abstracts the callee. Here we instead supply a *specific*
callee — its own IL program — and thread its denotation in as the `CallEnv`, so
the whole composition closes to a concrete form. This is the whole-program step:
caller + callee proven together, not the caller alone. -/

/-- The callee `uint32_t f(uint32_t z){ return z + z; }`, as its own IL program. -/
def f_double : CProg := { binds := [ .alu add (arg 0) (arg 0) ], ret := slot 0 }

/-- A call environment in which `"f"` is `f_double` (which itself calls nothing,
so its inner environment is irrelevant). -/
def withF : CallEnv := fun name args =>
  if name = "f" then f_double.eval (fun _ _ => 0) args else 0

/-- With the concrete callee `f(z) = 2z`, `double_call` computes `4·x` for **all**
`x` — caller and callee composed and proved to a closed form by `bv_decide`. -/
theorem double_call_with_f (x : Word) :
    double_call.eval withF [x] = 4 * x := by
  simp only [double_call, withF, f_double, CProg.eval, cevalGo, CRhs.eval, Atom.eval, Op.apply,
             List.map_cons, List.map_nil, List.getD_cons_zero, List.getD_cons_succ,
             List.nil_append, List.cons_append, reduceIte]
  bv_decide

/-! ### Rendering calls to Slang, proved against `evalU32F`.

A call renders to a Slang `call` expression; ALU/slots render as before. The
render is proved meaning-preserving against `LeanSlang.evalU32F` — the
call-aware semantics — with the callee left abstract. -/

/-- Lower a call-binding RHS: ALU → `bin`, call → a Slang `call` expression. -/
@[simp] def CRhs.toSlang (slots : List SlangExpr) : CRhs → SlangExpr
  | .alu op a b => .bin op.slangOp (a.toSlang slots) (b.toSlang slots)
  | .call f as  => .call f (as.map (·.toSlang slots))

/-- Inline the SSA slots left-to-right, then render the returned atom. -/
@[simp] def crenderGo (ret : Atom) : List CRhs → List SlangExpr → SlangExpr
  | [],      slots => ret.toSlang slots
  | r :: rs, slots => crenderGo ret rs (slots ++ [r.toSlang slots])

/-- Call-IL program → one `LeanSlang.SlangExpr` (calls become Slang `call`s). -/
@[simp] def CProg.render (p : CProg) : SlangExpr := crenderGo p.ret p.binds []

/-- render-correctness for calls: the emitted Slang `call` expression means
exactly `double_call.eval`, for **all** callees (the `CallEnv` is reused as the
Slang `FEnv`). -/
theorem double_call_render (ce : CallEnv) (x : Word) :
    (double_call.render).evalU32F (env2 x 0) ce = some (double_call.eval ce [x]) := by
  simp +decide only [double_call, CProg.render, crenderGo, CRhs.toSlang, Atom.toSlang, Op.slangOp,
             argName, env2, SlangExpr.evalU32F, binOpU32, CProg.eval, cevalGo, CRhs.eval, Atom.eval,
             Op.apply, List.map_cons, List.map_nil, List.getD_cons_zero, List.getD_cons_succ,
             List.nil_append, List.cons_append, if_true, if_false]

/-! ## First real Decompile-Bench function through the proof path.

Everything above is synthetic. This is an actual function from the
`LLM4Binary/decompile-bench` corpus — `BlockDevice::Lock()`, whose real
disassembly (from the corpus `asm` column) is:

```
    movb $0x1, %al
    retq
```

i.e. it loads the constant `1` into the return register and returns. Lifted to
the IL it is "return 1"; we prove the recovered value (spec) and that the
emitted Slang agrees. The lift here is transcribed by hand from the real asm —
the automated `Flowref.Disasm.Ins → Prog` bridge (the corpus harness) is the
remaining infrastructure, but the *proof path itself* now demonstrably handles a
real corpus function, not just hand-built demos. -/

/-- `BlockDevice::Lock()` lifted: `movb $0x1, %al; ret` ⇒ returns `1`. -/
def blockdevice_lock : Prog := { binds := [], ret := imm 1 }

/-- The recovered value matches the function's behaviour: it returns `1`. -/
theorem blockdevice_lock_correct : blockdevice_lock.eval [] = 1 := by
  simp [blockdevice_lock, Prog.eval, evalGo]

/-- render-correctness on the real function: the emitted Slang returns `1` too. -/
theorem blockdevice_lock_render :
    (blockdevice_lock.render).evalU32 (fun _ => 0) = some (blockdevice_lock.eval []) := by
  simp [blockdevice_lock, Prog.eval, evalGo]

/-! ## The lift bridge: decoded instructions → IL, in Lean.

The remaining harness infrastructure is the *lift* from decoded instructions to
`Prog`. Capstone produces the instruction list; this is the other half — a
minimal but real SSA lifter for straight-line register code: track each
register's current value-source, emit a binding per ALU op (a fresh SSA slot),
and treat `mov` as a copy. Run on the **real** `BlockDevice::Lock()` instruction
sequence it reproduces the hand-lift, now mechanically. Arg-register mapping and
the `Flowref.Disasm.Ins` adapter are the next pieces; this is the core. -/

/-- A decoded operand: a register name or an immediate. -/
inductive Operand | reg (r : String) | imm (w : Word)
  deriving Repr

/-- A decoded straight-line instruction (the shape a decoder hands us). -/
inductive LInsn
  | mov (dst : String) (src : Operand)            -- dst := src   (copy)
  | bin (dst : String) (op : Op) (a b : Operand)  -- dst := op a b
  | ret (src : String)                            -- return register `src`
  deriving Repr

/-- Lifter state: register → current IL source, emitted bindings, next slot. -/
structure LSt where
  regs  : List (String × Atom) := []
  binds : List Bind            := []
  n     : Nat                  := 0
  retA  : Atom                 := .imm 0

/-- Current IL source of register `r` (unmapped ⇒ treated as immediate 0; real
arg-register init is the next step). -/
@[simp] def LSt.get (s : LSt) (r : String) : Atom :=
  ((s.regs.find? (·.1 = r)).map (·.2)).getD (.imm 0)

/-- Resolve an operand to an IL atom. -/
@[simp] def LSt.opnd (s : LSt) : Operand → Atom
  | .reg r => s.get r
  | .imm w => .imm w

/-- Lift one instruction, threading the state. -/
@[simp] def LSt.step (s : LSt) : LInsn → LSt
  | .mov d src    => { s with regs := (d, s.opnd src) :: s.regs }
  | .bin d op a b => { regs := (d, .slot s.n) :: s.regs,
                       binds := s.binds ++ [⟨op, s.opnd a, s.opnd b⟩], n := s.n + 1, retA := s.retA }
  | .ret r        => { s with retA := s.get r }

/-- Lift a decoded sequence to an IL program. `argRegs` seeds the calling
convention: the i-th register holds argument `i` on entry (SysV: `edi, esi, …`). -/
@[simp] def lift (argRegs : List String) (is : List LInsn) : Prog :=
  let s := is.foldl LSt.step { regs := argRegs.mapIdx (fun i r => (r, Atom.arg i)) }
  { binds := s.binds, ret := s.retA }

/-- The real `BlockDevice::Lock()` instructions: `movb $0x1, %al; ret`. -/
def lockInsns : List LInsn := [ .mov "al" (.imm 1), .ret "al" ]

/-- The lifter mechanically reproduces the hand-lift, and the result returns `1` —
the first real corpus function lifted by code, not by hand. -/
theorem lift_lock_correct : (lift [] lockInsns).eval [] = 1 := by decide

/-- The canonical SysV compilation of `uint32_t add(uint32_t a, uint32_t b){
    return a + b; }`: `mov %edi, %eax; add %esi, %eax; ret`. -/
def addInsns : List LInsn :=
  [ .mov "eax" (.reg "edi"), .bin "eax" add (.reg "eax") (.reg "esi"), .ret "eax" ]

/-- With arg-register seeding, the lifter recovers `a + b` for **all** `a, b` —
a two-argument function lifted from its instructions and proved by `bv_decide`. -/
theorem lift_add_correct (a b : Word) : (lift ["edi", "esi"] addInsns).eval [a, b] = a + b := by
  rw [show lift ["edi", "esi"] addInsns = p_add from rfl]; exact p_add_correct a b

end FlowrefDecompiler.IL
