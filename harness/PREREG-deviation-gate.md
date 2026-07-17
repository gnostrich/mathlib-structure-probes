# PRE-REGISTRATION — back-guess/back-actual deviation gate (structure vs noise)

STATUS: pre-registered. Definitions, tests, and locked lines fixed BELOW before results.
This session MEASURES ONLY — it does NOT build a flow, hypergraph model, or conjecturer. The
gate decides whether the "train the Gibbs reverse-flow on back-guess/back-actual deviation"
design is worth starting. **Intrinsic only — NO git commit dates anywhere.**

Ground truth confirmed: (a) depth-from-axioms computed & validated (AUC 0.81 vs external fame);
(b) faithful decl graph (333,044 / 7,523,067) available; (c) no reverse-flow/deviation code exists.

## PROXY DISCLOSURE (load-bearing)

The real Gibbs reverse-flow object (`GramState`/`expand`/`checkPDq`/positivity in
`output-final_aristotle`) acts on **Gram matrices, not Mathlib declarations** — it is not wired
to this graph and cannot be run on it. So `back-guessed` is a **PROXY**, pinned below. Per the
asymmetry: **ALIVE on the proxy is trustworthy (structure found is structure found); DEAD on the
proxy is PROVISIONAL** ("dead for this proxy; retest if the full object is ever wired"), NOT a
permanent kill.

## The two orderings (both intrinsic to the graph)

- **back-actual** (ground truth): the depth-peel order. `depth(v)` = longest prerequisite chain
  (max over dependencies), computed on the SCC condensation. A node's build position = its depth
  level. This IS a topological order.
- **back-guessed** (PROXY for the Gibbs reverse-flow): the **mean-generation** flow order
  `g(v) = 1 + mean_{d: v→d} g(d)` (g=0 at sources), computed by the same topological DP as depth
  but with MEAN instead of MAX. This is the expected build-depth under uniform random descent of
  the dependency DAG — a diffusion/relaxation "settling" order. It respects topology (a
  dependency has strictly smaller g), and differs from depth exactly by dependency-tree SHAPE
  (long-thin vs bushy). Labeled a proxy; a spectral/diffusion alternative is a future variant.

## Forced-order control (the crux)

Both orders respect the DAG, so they agree on ALL topologically-comparable pairs (forced, zero
information). The deviation of interest is the part NOT forced: the residual of `back-guessed`
after removing `back-actual`. Concretely: **deviation(v) = residual of rank(g(v)) after linear
regression on rank(depth(v))**. Report raw agreement `Spearman(g, depth)` AND this residual; the
residual is the decisive object. (depth is the scalar level-function of the topological partial
order, so residualizing on it removes the forced skeleton.)

## Four structure-vs-noise tests (all pre-registered; report all)

1. **Magnitude:** unforced fraction = `1 − R²(rank g ~ rank depth)`. Near 0 → g≡depth → nothing
   unforced → DEAD. Line: **≥ 0.15**.
2. **Concentration:** is |deviation| concentrated or uniform? Metric = fraction of total
   |deviation| mass held by the top-decile of nodes. A Gaussian/uniform (noise) residual holds
   ≈0.26 in its top decile. Line: **≥ 0.40** (concentrated = structured).
3. **Reproducibility:** perturb tie-breaks (add small rank-noise to depth and g, recompute
   deviation); `Spearman(deviation, deviation_perturbed)` must persist. Line: **≥ 0.70**.
4. **Higher-order (hypergraph signal):** do high-|deviation| nodes CLUSTER (co-occur in graph
   regions/modules) beyond chance? Metric = mean same-top-decile rate among module-mates of
   top-decile-deviation nodes, vs the same for random decile (ratio). Line: **≥ 1.5×** chance =
   cluster structure (this specifically justifies the hypergraph formulation).

## Pre-registered reads (locked now)

- **ALIVE:** magnitude ≥ 0.15 AND concentration ≥ 0.40 AND reproducibility ≥ 0.70. → structured,
  reproducible unforced order-content exists → the hypergraph-flow design is warranted; recommend
  building it next session. Bonus: test 4 ≥ 1.5× → justifies the hypergraph specifically.
- **DEAD:** magnitude < 0.15 OR concentration < 0.40 (uniform/noise) OR reproducibility < 0.70.
  → guess and truth differ only by forced topology + noise → nothing learnable → back-then-forward
  collapses to forward (known to fail). **Provisional on the proxy** (see disclosure) — write as
  "DEAD for this proxy; ALIVE remains possible only if the real Gibbs object is wired and retested."
- **AMBIGUOUS:** otherwise → report, do not recommend building.

## Discipline rails
- Intrinsic only — NO commit dates.
- The topological control is mandatory: report residual-after-depth, not raw disagreement, as the verdict.
- MEASURE ONLY — no flow/hypergraph/conjecturer built this session.
- `back-guessed` is a proxy — ALIVE trustworthy, DEAD provisional (pinned above).
- One measurement, pre-committed lines, no tuning.
