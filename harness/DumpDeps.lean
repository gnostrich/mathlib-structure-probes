/-
DumpDeps.lean — faithful declaration-level dependency extractor.
Run inside a project that imports Mathlib (the certified-positivity artifact repo,
or any Mathlib-pinned project). Emits decl_deps.jsonl : one line per Mathlib
declaration = {"name", "module", "kind", "type_deps":[...], "value_deps":[...]}.

NOTE: exact Lean 4 API names drift across toolchains. This targets the module
system era (public import). If a method name mismatches your `lean-toolchain`,
the fixes are 1-liners (getUsedConstants / getUsedConstantsAsSet; module lookup
via const2ModIdx + header.moduleNames). Prefer LeanDojo tracing if you want a
zero-fiddle path; this is the lightweight native option.
-/
import Mathlib
import Lean
open Lean

def constKind : ConstantInfo → String
  | .thmInfo _   => "theorem"
  | .defnInfo _  => "def"
  | .axiomInfo _ => "axiom"
  | _            => "other"

/-- constants referenced in an expression -/
def exprDeps (e : Expr) : Array Name :=
  (Lean.Expr.getUsedConstants e)

run_cmd do
  let env ← getEnv
  let modNames := env.header.moduleNames
  let mut out : Array String := #[]
  for (n, ci) in env.constants.toList do
    if n.isInternal || n.hasMacroScopes then continue
    -- module of this declaration
    let some idx := env.const2ModIdx[n]? | continue
    let modName := modNames[idx.toNat]!
    let mod := modName.toString
    if !("Mathlib".isPrefixOf mod) then continue
    let tdeps := exprDeps ci.type
    let vdeps := match ci.value? with | some v => exprDeps v | none => #[]
    let jarr (a : Array Name) : String :=
      "[" ++ String.intercalate "," (a.toList.map (fun m => "\"" ++ m.toString ++ "\"")) ++ "]"
    let line := "{\"name\":\"" ++ n.toString ++ "\",\"module\":\"" ++ mod ++
      "\",\"kind\":\"" ++ constKind ci ++ "\",\"type_deps\":" ++ jarr tdeps ++
      ",\"value_deps\":" ++ jarr vdeps ++ "}"
    out := out.push line
  IO.FS.writeFile "decl_deps.jsonl" (String.intercalate "\n" out.toList)
  IO.println s!"wrote decl_deps.jsonl : {out.size} Mathlib declarations"
