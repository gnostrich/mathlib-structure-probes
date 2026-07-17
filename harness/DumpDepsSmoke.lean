/-
DumpDepsSmoke.lean — FAST validation of the faithful dump pipeline.

Imports only a small slice of Mathlib so it builds quickly (does NOT need the
whole `import Mathlib`), and writes `decl_deps_smoke.jsonl` in the same schema as
DumpDeps.lean, restricted to declarations defined in the imported slice. Purpose:
confirm the metaprogram compiles on this toolchain and that the produced file is
retrievable, before/at the same time as the full run.
-/
import Mathlib.Topology.Basic
import Lean
open Lean

def smokeKind : ConstantInfo → String
  | .thmInfo _   => "theorem"
  | .defnInfo _  => "def"
  | .axiomInfo _ => "axiom"
  | _            => "other"

def smokeArr (a : Array Name) : String :=
  "[" ++ String.intercalate "," (a.toList.map (fun m => "\"" ++ m.toString ++ "\"")) ++ "]"

run_cmd do
  let env ← getEnv
  let modNames := env.header.moduleNames
  let h ← IO.FS.Handle.mk "decl_deps_smoke.jsonl" IO.FS.Mode.write
  let mut count : Nat := 0
  for (n, ci) in env.constants.toList do
    if n.isInternal || n.hasMacroScopes then continue
    let some idx := env.const2ModIdx[n]? | continue
    let mod := (modNames[idx.toNat]!).toString
    if !("Mathlib".isPrefixOf mod) then continue
    let tdeps := Lean.Expr.getUsedConstants ci.type
    let vdeps := match ci.value? with | some v => Lean.Expr.getUsedConstants v | none => #[]
    let line := "{\"name\":\"" ++ n.toString ++ "\",\"module\":\"" ++ mod ++
      "\",\"kind\":\"" ++ smokeKind ci ++ "\",\"type_deps\":" ++ smokeArr tdeps ++
      ",\"value_deps\":" ++ smokeArr vdeps ++ "}\n"
    h.putStr line
    count := count + 1
  h.flush
  IO.println s!"DumpDepsSmoke: wrote decl_deps_smoke.jsonl with {count} declarations"
