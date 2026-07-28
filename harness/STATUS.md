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
- REPLICATION: the H2 degree-collapse + H3 results reproduce on an independent v2
  approx extractor (newer Mathlib commit 9944fe29, 229,502 decls): baseline
  rho(L,Y2|depth)=0.554 -> degree-controlled 0.087 (collapses); H3(a) 0/3000;
  L_cold ~0.14-0.18. Same verdict. Log: veto_ext_v2approx.log.
- FAITHFUL DECL GRAPH — DONE via Aristotle. Local build was egress-blocked (github
  releases 403, api.github.com 403, mathlib4.blob.core.windows.net 502). Instead ran
  DumpDeps.lean inside Aristotle's (Harmonic) built Mathlib v4.28.0 env and pulled
  decl_deps.jsonl back via get_files() (see aristotle_faithful_dump.py). Two independent
  jobs returned BYTE-IDENTICAL output (md5 9f3a3c36...): 333,044 decls / 7,523,067 edges,
  avg 28.7 value-deps (proof-synthesized edges present). Graph kept out of repo (395MB).
- FAITHFUL DECISIVE RUN (loop_veto_test.py on decl_deps.jsonl) — the payoff FLIPS:
  * H2 baseline 0.539 -> degree-controlled 0.372 => CLEARS (approx graphs collapsed to
    ~0). Residual-corr cross-check agrees (0.372). Loop-residue carries significance
    beyond depth AND degree on real proof structure -- the pre-registered claim.
  * H3(a) PASS (0/3000 foils). H3(b) L_cold own-degree-controlled 0.146 (min2) / 0.305
    (min3) -> the incorruptible residue also carries signal here.
  * H1 dissociation rho(L,depth)=0.528 > 0.40 precondition -> AMBIGUOUS by the STRICT
    pre-reg gate (not a payoff failure). OVERALL: AMBIGUOUS -> DO NOT WIRE.
  Full log: veto_faithful.log; writeup + cross-substrate table: RESULTS-faithful.md.
  Read: substantively POSITIVE (payoff holds on faithful, refuted on approx), but not a
  clean GO because loop/depth co-vary above the fixed 0.40 bar. Next: a less depth-
  entangled loop metric (birth-simplex / non-backtracking residue), re-run, then wire
  per docs/05 only if H1 drops below 0.40 with H2 still up.

Decisive path: DumpDeps.lean (or LeanDojo) -> decl_deps.jsonl -> loop_veto_test.py
-> if H1 GO-precondition AND H2 clears (degree-controlled) AND H3 foils hold, wire per docs/05.
NOTE: on the approx graph H2 does NOT clear the degree control, so wiring is NOT yet warranted.

- PROBE 16 — term-space failure anisotropy (probe16/, first probe to measure TERMS rather than the
  dependency graph). Pre-registered before the run; occupancy sweep first (NOT OCCUPIED on the
  question, [occupied] on every component — mCoq, typeclass/instance literature, Gandhi ITP 2025;
  margin recorded as thin). Perturbed 245 corpus theorems from Algebra/Group/Basic + Order/Basic
  along the six type-theoretic directions D1-D6 at depths 1-3, replaying each ORIGINAL proof under
  the perturbed statement; 275 files, 880 logs, Mathlib 8f9d9cff (v4.28.0).
  * VERDICT: **CEILING (not a null)** — 94.6% of measurable cells fail at depth 1, 95.1% ever fail;
    both pre-registered ceiling triggers fire. Depths NOT re-tuned. CLOSED.
  * The anisotropy test would not have passed either: A_obs=52.0 vs A_shuffled=48.3 = 1.08x against
    a required 3x (A is inflated only because V_D~0; the permutation control exposes it).
  * Instrument is sound, not blind: harness-validity cell PASSES decisively (decorative-structure
    trivialities mean R=1.000 vs hypothesis-laden theorems 0.133, Mann-Whitney p=1.25e-12); canary
    failures 0/275; duplicate-shard fidelity 0/230 disagreements.
  * Measured substrate facts: 98% of hypothesis deletions and 93% of single-step class weakenings
    break immediately; only 11/159 theorems tolerate ANY perturbation. Four of the six directions
    barely exist here (D3 and D5 zero measurable cells, D4 nine, D6 two) — Mathlib's core is already
    universe-polymorphic with almost no finiteness assumptions, so the "6-tuple" is a 2-tuple.
  Files: probe16/SWEEP.md, PREREG-term-anisotropy.md, probe16.py, probe16_analyze.py,
  p16_analysis.log, RESULTS-term-anisotropy.md.

- PROBE 17 — rfl-locus confirmation run (probe17/). Pre-registered and committed before D or S was
  computed. Two checks against the paper's own machinery (arXiv:2603.20396) on Mathlib 8f9d9cff
  (v4.28.0), route (a) real dependency extraction (DumpDeps.lean, type AND value deps):
  * CHECK A — D = AUC(their declaration-level longest-path depth -> substantive) = **0.6508**.
  * CHECK B — S = fraction of module-level variance in definitional fraction explained by subject
    = **0.0770** (2,563 modules >=20 thms, 26 subjects, unweighted; 0.0427 all modules, 0.0733
    size-weighted).
  * VERDICT: **PARTIAL. TERMINAL, CLOSED.** Not <=0.60 (CONFIRMED), not >=0.75 (DEPTH-REDUCIBLE),
    S far below 0.80 so SUBJECT-REDUCIBLE is decisively excluded. Report both, claim nothing beyond.
  * Check B passes cleanly and is the informative half: the clustering is NOT subject matter.
    [proven] Check A is where it fails to clear: the module-import proxy said 0.556, the paper's
    real depth says 0.651 — more entangled, and barely above the 0.621 statement-length baseline.
  * Classes never merged: AUC(depth -> strict rfl) 0.3103, AUC(depth -> by simp) 0.4517;
    S(strict) 0.0770, S(simp) 0.0712. All of D's excess over 0.5 is carried by strict rfl; the
    simp class is depth-indifferent.
  * Harness-validity cell PASSES: Logic+Init 0.1796 vs Analysis 0.0659; max depth 192 (within an
    order of magnitude of ~300); 467,680 vertices vs their 463,719 (0.85% apart).
  * Five discrepancies reported, not smoothed: prior probe's 7.34%/185,429 NOT reproduced (10.76%
    over 170,326 here); depth 192 vs ~300; zero non-trivial SCCs vs their ~60; their named largest
    unwrapped element ranks 6,067 (soft, pre-declared non-VOID-bearing); elaborated-term
    cross-check only ~2.4x. Classification is source text, so 10.76% is a FLOOR.
  * No importance signal, no conjecturer, no novelty claim vs arXiv:2603.20396. [proven-negative]
    for the confirmation attempt. One round; no follow-ups.
  Files: probe17/PREREG-rfl-locus.md, RESULTS-rfl-locus.md, probe17_rfl_locus.py,
  probe17_perclass.py, p17_run.log, p17_perclass.log, p17_report.json.
