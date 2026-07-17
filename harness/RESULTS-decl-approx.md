# Results — declaration-level test, APPROX graph (this session)

First run of the decisive harness (`loop_veto_test.py`) on the **real Mathlib
declaration graph**, at the no-build APPROX granularity. This is a step up from
the module-level pre-test (which tested only H1); here H1 **and** the H2 payoff
run on 213,929 real declarations.

## How it was produced
- Fresh shallow clone of `mathlib4` at the pinned `v4.28.0` (7,648 `.lean`
  files under `Mathlib/`), via `git clone --depth 1 --branch v4.28.0`.
- `decl_dep_extract.py mathlib4/Mathlib` → statement/body reference graph:
  **219,127 decls / 1,574,452 edges** (theorem 122,492; lemma 49,344; def 29,552;
  instance 11,109; abbrev 2,896; class 1,855; structure 1,554; inductive 325).
- `loop_veto_test.py decl_ref_graph.jsonl` → after restricting to kinded nodes:
  **nodes = 213,929, edges = 1,574,452**.

## Harness bugs found & fixed en route (fidelity provenance)
Both fixes bring the decl-level harness in line with the already-validated
module-level pre-test; neither changes the pre-registered reads.
- **depth axis collapsed to a constant.** The longest-dependency-chain
  recurrence iterated in forward topological order, so a node's successors
  (its dependencies) were never yet in `cdep` when it was processed — every
  depth became 0, making `slide = depth` constant and `rho(L, slide)` a NaN.
  Fixed to **reverse** topological order (`reversed(list(topological_sort(Cg)))`),
  matching `mathlib_slide_loop_pretest.py:44` which already notes "depth needed
  reverse-topological order."
- **intractable dead call.** `sq = nx.square_clustering(UG)` was computed but
  never used; on the full graph it did not finish (O(n·⟨k⟩²) over Mathlib's
  hub nodes). Dropped it; the loop metric `L` is `nx.triangles`, which is what
  the rest of the script actually consumes.

## Metrics (slide = depth; loop = triangles; Y2 = log in-degree)

### H1 — dissociation (loop ⟂ slide)
- `rho(L, slide=depth)   = 0.267`   (≤ 0.4 bar ✓)
- `rho(L, in-degree)     = 0.419`
- `R2(L ~ slide + deg)   = 0.016`   (≤ 0.5 bar ✓, i.e. slide barely explains loop)
- tercile cells: high-slide/low-loop = **9,927**, low-slide/high-loop = **24,427**
  (both populated ✓)
- **H1 = GO-precondition.** Loop-residue is a distinct axis from depth/slide on
  the real decl graph. No wall.

### H2 — loop predicts significance beyond slide (PAYOFF)
- `partial rho(L, Y2 log in-degree | slide) = 0.485`  (positive, non-trivial)
- `partial rho(L, Y1 thm/lemma label | slide) = -0.092`  (≈ 0; loops don't track
  the theorem-vs-def label, as expected — defs can be heavily looped)

The citation-proxy payoff (0.485) is the signal the pre-registration was after:
loop-residue carries significance information the slide axis does not.

### H3 — incorruptibility
Still **hooks only** (gaming foil + warm/cold floor). These need the prover /
built environment and are not fakeable from the source graph; left as TODO.

## Verdict vs corrected pre-reg
WALL if `|rho|≥0.7 OR R2≥0.75 OR H2 fails`; GO-precondition if
`|rho|≤0.4 AND R2≤0.5 AND both cells populated`. **Result: GO-precondition on
H1, positive H2 payoff on the citation proxy.** Not a full GO — that requires H3
plus the faithful graph.

## SCOPE / honest caveats (do not overclaim)
- **APPROX graph.** Edges are statement/body name references only. It MISSES
  proof-synthesized edges (simp/omega/typeclass/tactic-invoked lemmas) and can
  catch names in comments. A null here would be confounded; a positive here is
  suggestive, not decisive.
- **Y2 ↔ degree coupling.** `L` (triangles) and `Y2` (in-degree) both grow with
  node degree; the partial controls for depth, not degree, so part of the 0.485
  may be mechanical. The pre-reg keeps degree out of `slide` deliberately; read
  the number with that caveat.
- **Faithful graph still pending.** The decisive version needs the true kernel
  dependency graph via `DumpDeps.lean` (or a LeanDojo trace) in a *built*
  environment. In this session the Lean toolchain (elan → `leanprover/lean4`
  GitHub *releases*) is blocked by the egress policy (HTTP 403), so no `lake
  build` was possible. Mathlib *source* is clonable via git, which is what made
  this APPROX run possible.

Decisive path from here: faithful decl graph (built env) → rerun → if H2 clears
its bar there, implement H3 floor, then wire the meter per `docs/05`.
