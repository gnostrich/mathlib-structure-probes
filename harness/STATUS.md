# Harness status (what's validated vs what needs your env)

- mathlib_slide_loop_pretest.py — RAN this session on full module graph. Real result
  in RESULTS-module-pretest.md. Faithful at module granularity.
- decl_dep_extract.py — RAN this session on FULL Mathlib source (v4.28.0, shallow
  clone): 219,127 decls / 1,574,452 edges. Qualified names OK.
  APPROX (statement refs only, misses proof edges). Run full: 
  `python decl_dep_extract.py mathlib4/Mathlib --out decl_ref_graph.jsonl`
- DumpDeps.lean — NOT compiled here. Faithful method; needs a built env. The Lean
  toolchain (elan -> leanprover/lean4 GitHub releases) is blocked by the session
  egress policy (HTTP 403), so no `lake build` was possible this session. Mathlib
  SOURCE is clonable via git, which is what enabled the approx run above.
- loop_veto_test.py — RAN this session on the FULL approx decl graph (213,929
  nodes). H1 = GO-precondition; H2 citation-proxy payoff partial rho = 0.485. Real
  numbers (approx granularity) in RESULTS-decl-approx.md. Two bugs fixed en route
  (reverse-topo depth; dropped unused/intractable square_clustering). H3 hooks
  still TODO (need the prover). Faithful graph run still pending a built env.

Decisive path: DumpDeps.lean (or LeanDojo) -> decl_deps.jsonl -> loop_veto_test.py
-> if H1 GO-precondition AND H2 clears, implement H3 floor, then wire per docs/05.
