# PRE-REGISTRATION — order-holonomy gate (antisymmetric residual, Hodge curl)

STATUS: pre-registered. Observable, controls, and locked lines fixed BELOW before results.
Intrinsic (NO commit dates). MEASURE ONLY — build nothing. This corrects the deviation gate:
the decisive object is the ANTISYMMETRIC (circulation) residual, not magnitude/spatial concentration.

## Why the literal "guess-vs-actual order holonomy" is degenerate (stated, then avoided)

`back-actual` (depth) and `back-guessed` (mean-gen g) are node scalars; their residual `r(v)` is a
node scalar. The circulation of any node scalar around a closed loop telescopes to **identically 0**
(a gradient field has zero curl). So the literal measurement is a tautological zero, NOT an
empirical result. We demonstrate this (compute it, expect ~1e-12), then measure the well-posed
observable below. (This is a well-posedness correction, not a reinterpretation to survive: the
well-posed observable below has its OWN pre-committed DEAD and is honored as a real kill.)

## The well-posed observable — Hodge curl of the dependency comparison flow

On the directed dependency graph, put a unit comparison flow on each edge: `f(u→v) = 1` ("u is
accumulated after its prerequisite v"). Hodge / least-squares decomposition:
```
minimize over node-potential φ:  || f − grad φ ||²     (grad φ)(u→v) = φ(u) − φ(v)
gradient part  = grad φ*         = the rankable/topological hierarchy (FORCED order)
curl residual  = f − grad φ*     = the circulation that NO global order can realize
curl_fraction  = ||curl||² / ||f||²   (fraction of the comparison flow that is antisymmetric/rotational)
```
`curl_fraction` **IS** the antisymmetric residual after quotienting the forced gradient (topology) —
by construction, not by a proxy. Solved via `scipy.sparse.linalg.lsqr` on the incidence matrix
(cap iters; report solver convergence). No Gibbs proxy needed → verdict is NOT proxy-provisional.

## Two controls (both binding; the second is the discriminator)

1. **Topology quotient:** the gradient part IS the forced topological order; `curl_fraction` is the
   residual after removing it. (Built in.)
2. **Module conditioning:** recompute the decomposition using ONLY intra-module edges →
   `curl_fraction_intra`. If circulation is purely cross-module (coarse-topological reconvergence),
   intra-module curl collapses; if genuine circulation persists within modules, it survives.

## Pre-registered reads (LOCKED — a null is a REAL kill, not a prompt to reinterpret again)

- **ALIVE:** `curl_fraction ≥ 0.15` AND `curl_fraction_intra ≥ 0.5 × curl_fraction` (survives module
  conditioning) AND reproducible (stable across two independent lsqr solves / edge-orderings).
  → genuine antisymmetric order-content that survives both controls → holonomy-flow design warranted.
- **DEAD (REAL, non-provisional):** `curl_fraction < 0.15` (the accumulation order is essentially a
  clean gradient/hierarchy) OR `curl_fraction_intra < 0.5 × curl_fraction` (circulation is only
  cross-module coarse topology, vanishes under module conditioning). → no intra-region circulation to
  learn → back-then-forward collapses to forward. **This is a clean kill and the thread ends here** —
  the framing dies on this number; no third reinterpretation.
- **AMBIGUOUS:** otherwise → report, recommend nothing.

## Rails
- Report `curl_fraction` (and intra-module) as decisive; the old magnitude/spatial T4 is context only.
- The observable is intrinsic (real dependency flow), so DEAD is a genuine kill — hold it.
- MEASURE ONLY. The "equilibrium not a loss" framing (find the flow stationary w.r.t. accumulation
  order; note the trivial fixed point = pure topological order self-consists for free, carrying no
  info — which is WHY we measure the topology-quotiented curl) motivates WHAT to measure; it does not
  license building anything or pre-judging the answer.
