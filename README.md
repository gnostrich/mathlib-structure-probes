# NeurReps loop-veto kit — context + harness for the decl-level test

Purpose: everything needed to run the **decisive** test of the "loop-residue as
incorruptible significance veto over Mathlib" idea in Claude Code, against the
real declaration-level dependency graph and wired to the certified generator as
it was actually built.

## Honest access caveat (read first)
The certified generator itself (the Lean object: `GramState`/`expand`/inertia
meter, Suzuki zeta-kernel PD window) was built in the chat "Gauge-covariant free
energy and state transitions" and lives in **`certified-positivity-artifact.zip`**
in *that* chat's outputs. Chat sandboxes do not persist across sessions, so it is
NOT embedded here and I did not reconstruct the Lean source (that would be a fake
of the real thing). `docs/04-provenance-and-manifest.md` lists exactly which
external files to drop into the repo.

## What IS in here (all faithful)
- `docs/` — the idea, the surviving delta, the closest-work sweep, the corrected
  pre-registration, provenance, and how the loop-veto connects to the generator.
- `harness/mathlib_slide_loop_pretest.py` — the coarse module-level pre-test I
  actually ran this session (+ `RESULTS-module-pretest.md`). Result: no wall;
  loop is a distinct axis from centrality. This is the skeleton for the real test.
- `harness/DumpDeps.lean` — native faithful decl-dependency extractor (needs a
  Mathlib build in the repo).
- `harness/decl_dep_extract.py` — no-build APPROX fallback (statement-reference
  graph from source) + postprocessor.
- `harness/loop_veto_test.py` — the decisive dissociation + significance-join +
  floor hooks, pre-registration baked in as asserts.

## Run order in Claude Code
1. Drop in `certified-positivity-artifact.zip` (see manifest) and `lake build`.
2. Get the real decl graph: either run `DumpDeps.lean` in the built env, or trace
   with LeanDojo (recommended, robust). Fallback: `decl_dep_extract.py`.
3. `loop_veto_test.py` — runs H1 (loop ⟂ slide), H2 (loop predicts significance
   beyond slide — the payoff), H3 (incorruptibility: gaming foil + warm/cold floor).
4. Only if H2 clears its pre-registered bar, wire the meter into the generator's
   expansion-point selection (docs/05).
