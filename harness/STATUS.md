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
  (reverse-topo depth; dropped unused/intractable square_clustering).
- loop_veto_test.py (UPDATED) — added the H2 DEGREE CONFOUND CONTROL (task 4) and
  implemented the H3 foils (task 5), then re-ran on the same approx graph. Full log
  in `veto_ext.log`; writeup in `RESULTS-decl-approx-H2confound-H3.md`. Headlines:
  * H2's 0.485 COLLAPSES to -0.046 once undirected degree (the triangle driver) is
    controlled -> on the approx graph H2 DOES NOT CLEAR (payoff was a degree artifact).
  * H3(a) gaming foil PASS: 0/3000 distant A∧B conjunctions credited; 0/2000 real
    endpoints changed. H3(b) warm/cold: warm payoff collapses under degree control;
    only the reuse-stripped L_cold residue keeps a weak ~0.19-0.23 partial (suggestive,
    not a bar; static proxy — a prover reproof is still needed to certify L_cold).
  * OVERALL on this substrate: AMBIGUOUS -> DO NOT WIRE.
- Faithful graph run STILL pending a built env: the Lean toolchain (github releases
  403), api.github.com (403) and the Mathlib olean cache (mathlib4.blob.core.windows.net,
  502) are policy-blocked at the egress gateway. Policy binds at session start, so a
  fresh session on an updated egress policy is required to retry the faithful build.

Decisive path: DumpDeps.lean (or LeanDojo) -> decl_deps.jsonl -> loop_veto_test.py
-> if H1 GO-precondition AND H2 clears (degree-controlled) AND H3 foils hold, wire per docs/05.
NOTE: on the approx graph H2 does NOT clear the degree control, so wiring is NOT yet warranted.
