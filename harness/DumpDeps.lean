/-
DumpDeps.lean — FAITHFUL declaration-level dependency extractor for Mathlib.

Goal: emit `decl_deps.jsonl` in the project root, ONE JSON object per line, for
every non-internal declaration whose defining module is under `Mathlib`:

  {"name": <fully-qualified>, "module": <module>, "kind": <theorem|def|axiom|other>,
   "type_deps": [<constants used in the TYPE>],
   "value_deps": [<constants used in the proof/VALUE term>]}

The union of type_deps ++ value_deps is the faithful kernel dependency set — it
INCLUDES proof-synthesized edges (simp/omega/typeclass/tactic-invoked lemmas),
which is exactly what the statement-only "approx" extractor misses.

Streams output with an IO handle (do NOT build one giant String: there are
~200k declarations). If an API name has drifted on this toolchain, the fixes are
1-liners: getUsedConstants / getUsedConstantsAsSet ; env.const2ModIdx ;
env.header.moduleNames. Keep the OUTPUT SCHEMA above identical.
-/
import Mathlib
import Lean
open Lean

def constKind : ConstantInfo → String
  | .thmInfo _   => "theorem"
  | .defnInfo _  => "def"
  | .axiomInfo _ => "axiom"
  | _            => "other"

/-- constants referenced in an expression (faithful kernel references) -/
def exprDeps (e : Expr) : Array Name :=
  Lean.Expr.getUsedConstants e

def jsonArr (a : Array Name) : String :=
  "[" ++ String.intercalate "," (a.toList.map (fun m => "\"" ++ m.toString ++ "\"")) ++ "]"

run_cmd do
  let env ← getEnv
  let modNames := env.header.moduleNames
  let h ← IO.FS.Handle.mk "decl_deps.jsonl" IO.FS.Mode.write
  let mut count : Nat := 0
  for (n, ci) in env.constants.toList do
    if n.isInternal || n.hasMacroScopes then continue
    let some idx := env.const2ModIdx[n]? | continue
    let modName := modNames[idx.toNat]!
    let mod := modName.toString
    if !("Mathlib".isPrefixOf mod) then continue
    let tdeps := exprDeps ci.type
    let vdeps := match ci.value? with | some v => exprDeps v | none => #[]
    let line := "{\"name\":\"" ++ n.toString ++ "\",\"module\":\"" ++ mod ++
      "\",\"kind\":\"" ++ constKind ci ++ "\",\"type_deps\":" ++ jsonArr tdeps ++
      ",\"value_deps\":" ++ jsonArr vdeps ++ "}\n"
    h.putStr line
    count := count + 1
  h.flush
  IO.println s!"DumpDeps: wrote decl_deps.jsonl with {count} Mathlib declarations"
