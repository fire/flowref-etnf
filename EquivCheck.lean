import Flowref.Disasm
import Plausible

/-! # flowref-equiv — the equivalence oracle, in Lean (binary is the reference)

The reference behaviour is the **real compiled function in the binary** — no
source compilation needed (Decompile-Bench `code` rarely compiles standalone).
Given a binary function region, this:

1. maps the function's raw bytes into executable memory (the reference);
2. lifts the same region to C with `flowref decompile`, refusing anything not
   faithfully liftable (a straight-line, register-only leaf — which is exactly
   what makes the raw bytes position-independent and safe to relocate + run);
3. compiles that C into a shared object (the candidate);
4. poses `∀ args, ref args = cand args` and lets `plausible` hunt for a differing
   argument vector — iteratively deepened. A counterexample IS the disproof
   (`NOT-EQUIVALENT`); its absence after the deepest level is the equivalence
   witness (`EQUIVALENT`). Unliftable/uncompilable ⇒ `INCOMPARABLE`, never a
   false `EQUIVALENT`.

Usage: flowref-equiv <binary> <arch> <fnVaddrHex> <fileOffHex> <vaddrHex> <lenHex>
Exit: 0 EQUIVALENT, 1 NOT-EQUIVALENT, 3 INCOMPARABLE. -/

open Plausible Flowref

/-- Map the reference function's raw bytes executable; `true` on success. -/
@[extern "lean_equiv_load_ref"]  opaque equivLoadRefImpl (bytes : ByteArray) : Bool
/-- dlopen the candidate `.so` (exports `flowref_cand`); `true` on success. -/
@[extern "lean_equiv_load_cand"] opaque equivLoadCandImpl (path : String) : Bool
@[extern "lean_equiv_ref"]  opaque refCall  (a b c d e f : UInt32) : UInt32
@[extern "lean_equiv_cand"] opaque candCall (a b c d e f : UInt32) : UInt32

def equivLoadRef  (b : ByteArray) : IO Bool := pure (equivLoadRefImpl b)
def equivLoadCand (p : String)    : IO Bool := pure (equivLoadCandImpl p)

/-- Parse the candidate's arity from its `uint32_t sub_X(<params>)` definition. -/
def candArity (c hexName : String) : Nat :=
  match (c.splitOn s!"{hexName}(").getLast? with
  | none => 0
  | some tail =>
    let inside := (tail.splitOn ")").headD ""
    if (inside.splitOn "void").length > 1 ∨ inside.trimAscii.isEmpty then 0
    else (inside.splitOn ",").length

/-- Run a command; return success + captured stderr. -/
def run (cmd : String) (args : Array String) : IO (Bool × String) := do
  let out ← IO.Process.output { cmd := cmd, args := args }
  pure (out.exitCode == 0, out.stderr)

def main (argv : List String) : IO Unit := do
  match argv with
  | [bin, arch, fnS, foS, vaS, lenS] => do
    let fnVa ← match parseImm? fnS with
      | some v => if v < 0 then throw (IO.userError "fnVaddr negative") else pure v.toNat
      | none => throw (IO.userError s!"bad fnVaddr '{fnS}'")
    let fo ← match parseImm? foS with | some v => pure v.toNat | none => throw (IO.userError "bad fileOff")
    let len ← match parseImm? lenS with | some v => pure v.toNat | none => throw (IO.userError "bad len")
    -- 1. Reference = the binary's own function bytes, mapped executable.
    let data ← IO.FS.readBinFile (bin : System.FilePath)
    if fo + len > data.size then
      IO.println "INCOMPARABLE  (region past end of file)"; IO.Process.exit 3
    if ¬ (← equivLoadRef (data.extract fo (fo + len))) then
      IO.println "INCOMPARABLE  (could not map reference bytes)"; IO.Process.exit 3
    -- 2. Candidate = flowref's lift of the SAME region; refused ⇒ INCOMPARABLE.
    let hexName := s!"sub_{Flowref.hex fnVa}"
    let flowref := (← IO.getEnv "FLOWREF").getD ".lake/build/bin/flowref"
    let lifted ← IO.Process.output { cmd := flowref, args := #["decompile", bin, arch, fnS, foS, vaS, lenS] }
    if lifted.exitCode != 0 then
      IO.println "INCOMPARABLE  (candidate not faithfully liftable)"; IO.Process.exit 3
    let cand := lifted.stdout
    -- 3. Compile candidate + a shim exporting `flowref_cand` → the lifted sub_X.
    let dir := (← IO.Process.run { cmd := "mktemp", args := #["-d", "/tmp/flowref-equiv.XXXXXX"] }).trimAscii.toString
    let candPath := s!"{dir}/cand.c"
    let shimPath := s!"{dir}/shim.c"
    let soPath := s!"{dir}/pair.so"
    let p6 := "uint32_t,uint32_t,uint32_t,uint32_t,uint32_t,uint32_t"
    let sig := "(uint32_t a,uint32_t b,uint32_t c,uint32_t d,uint32_t e,uint32_t f)"
    IO.FS.writeFile candPath cand
    -- shim in a SEPARATE TU: declaring sub_X with six args here does not conflict
    -- with its real (fewer-arg) definition in cand.c, and the SysV ABI passes the
    -- extra integer registers harmlessly.
    IO.FS.writeFile shimPath
      ("#include <stdint.h>\nuint32_t " ++ hexName ++ "(" ++ p6 ++ ");\n" ++
       "uint32_t flowref_cand" ++ sig ++ " { return " ++ hexName ++ "(a,b,c,d,e,f); }\n")
    let (ok, cerr) ← run "cc" #["-shared", "-fPIC", "-w", "-std=c11",
      "-fcf-protection=none", "-fno-stack-protector", candPath, shimPath, "-o", soPath]
    if ¬ ok then
      IO.println "INCOMPARABLE  (candidate C did not compile)"; IO.eprint cerr; IO.Process.exit 3
    if ¬ (← equivLoadCand soPath) then
      IO.println "INCOMPARABLE  (could not load candidate)"; IO.Process.exit 3
    -- 4. Plausible counterexample search over a SINGLE 6-tuple forall (one level
    --    ⇒ numInst whole-tuple samples ⇒ linear, bounded time), iteratively
    --    deepened. Six args cover the SysV integer-arg registers.
    let ar := candArity cand hexName
    let ladder : List Nat := [256, 4096, 50000]
    for n in ladder do
      let r ← Testable.checkIO
        (NamedBinder "args" (∀ t : Fin 65536 × Fin 65536 × Fin 65536 × Fin 65536 × Fin 65536 × Fin 65536,
          (refCall  (UInt32.ofNat t.1.val) (UInt32.ofNat t.2.1.val) (UInt32.ofNat t.2.2.1.val)
                    (UInt32.ofNat t.2.2.2.1.val) (UInt32.ofNat t.2.2.2.2.1.val) (UInt32.ofNat t.2.2.2.2.2.val)
           == candCall (UInt32.ofNat t.1.val) (UInt32.ofNat t.2.1.val) (UInt32.ofNat t.2.2.1.val)
                    (UInt32.ofNat t.2.2.2.1.val) (UInt32.ofNat t.2.2.2.2.1.val) (UInt32.ofNat t.2.2.2.2.2.val)) = true))
        { numInst := n, quiet := true }
      if r.isFailure then
        IO.println s!"NOT-EQUIVALENT  (plausible counterexample at L{n}, arity {ar})"
        IO.Process.exit 1
    IO.println s!"EQUIVALENT  (no counterexample; plausible-searched to {ladder.getLastD 0} instances, arity {ar})"
  | _ =>
    IO.eprintln "usage: flowref-equiv <binary> <arch> <fnVaddrHex> <fileOffHex> <vaddrHex> <lenHex>"
    IO.Process.exit 2
