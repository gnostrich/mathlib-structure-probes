# Harness status (what's validated vs what needs your env)

- mathlib_slide_loop_pretest.py — RAN this session on full module graph. Real result
  in RESULTS-module-pretest.md. Faithful at module granularity.
- decl_dep_extract.py — smoke-tested (non-crash, sane magnitude) on
  Mathlib/Analysis/SpecialFunctions: 4,239 decls / 7,271 edges, qualified names OK.
  APPROX (statement refs only, misses proof edges). Run full: 
  `python decl_dep_extract.py mathlib4/Mathlib --out decl_ref_graph.jsonl`
- DumpDeps.lean — NOT compiled here (no Mathlib build in sandbox). Faithful method.
  Run inside the built artifact repo. Adjust API name if toolchain differs.
- loop_veto_test.py — non-crash validated on the approx graph (H1/H2 pipeline runs;
  H3 hooks are TODO needing the prover). Numbers printed in smoke run are NOT
  evidence (tiny approx subgraph). Run on the FULL faithful graph for the real test.

Decisive path: DumpDeps.lean (or LeanDojo) -> decl_deps.jsonl -> loop_veto_test.py
-> if H1 GO-precondition AND H2 clears, implement H3 floor, then wire per docs/05.
