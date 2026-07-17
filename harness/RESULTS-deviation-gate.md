# RESULTS — back-guess/back-actual deviation gate (structure vs noise)

Pre-registration: `PREREG-deviation-gate.md` (committed before results; four test lines locked).
Intrinsic measurement (no commit dates). Faithful graph (333,044 / 7,523,067). Script:
`deviation_gate.py`; log: `deviation_gate.log`. **`back-guessed` is a PROXY** (mean-generation
flow order) for the unwired Gibbs reverse-flow — so a DEAD is provisional, an ALIVE trustworthy.

## Definitions

- **back-actual** = depth (longest prerequisite chain, max-generation) — the true depth-peel order.
- **back-guessed** (proxy) = `g(v) = 1 + mean_{v→d} g(d)` — mean-generation flow/settling order.
- **deviation(v)** = residual of `rank(g)` after regressing on `rank(depth)` (forced-order control:
  depth is the topological level function, so this is the unforced part).

## Results

| test | value | locked line | pass? |
|------|:---:|:---:|:---:|
| raw agreement Spearman(g, depth) | 0.644 | — | — |
| **T1 magnitude** 1−R²(rank g ~ rank depth) | **0.585** | ≥ 0.15 | PASS |
| **T2 concentration** top-decile \|dev\| mass | **0.253** | ≥ 0.40 | **FAIL** (Gaussian-noise ≈ 0.258) |
| **T3 reproducibility** Spearman(dev, dev_perturbed) | **0.999** | ≥ 0.70 | PASS |
| **T4 clusters** top-dev module-concentration vs null | **3.23×** (0.323 vs 0.100) | ≥ 1.5 | cluster-structure |

## Verdict — mechanically DEAD, but the DEAD is INTERNALLY CONTRADICTED → **AMBIGUOUS**

By the locked lines (ALIVE = all of T1,T2,T3), **T2 failed → the pre-registered trigger is DEAD.**
I report that honestly. **But the DEAD's semantic content — "guess and truth differ only by forced
topology + noise, nothing learnable" — is directly refuted by T3 and T4:**

- **T3 = 0.999:** the deviation is essentially deterministic under tie-break perturbation — it is
  NOT noise; it is a stable function of graph structure.
- **T4 = 3.23×:** high-deviation nodes are spatially **clustered by module** far above chance — the
  deviation is a coherent per-region property, exactly the cluster-signal that would justify a
  hypergraph formulation.

The contradiction is a **pre-registration design flaw**, reported plainly: **T2 measures
magnitude-concentration (is the deviation heavy-tailed across nodes?), which is NOT the same as
structure-vs-noise.** Here the deviation is **magnitude-diffuse** (spread across many nodes, so T2
reads "uniform") yet **reproducible and spatially clustered** (T3, T4 → structured). A diffuse-but-
structured signal fails T2 while being genuinely non-noise. So T2 was the wrong discriminator; T3
and T4 are the informative ones, and they say **structure exists.**

**Honest call:** this is **AMBIGUOUS**, not a clean DEAD and not a clean ALIVE.
- Not a clean ALIVE: the pre-registered T2 line failed; I hold the line I set.
- Not a real DEAD: the noise hypothesis is refuted (T3 reproducible, T4 3.2× clustered). There IS
  reproducible, region-structured unforced order-content between the flow-proxy order and depth.
- Plus the standing proxy caveat: this is the mean-generation proxy, not the real Gibbs object.

## Recommendation (for next session)

**Do NOT build the hypergraph flow yet, and do NOT kill the thread.** Instead re-run this gate with
a **corrected structure discriminator** — replace the magnitude-concentration test (T2) with a
**spatial-autocorrelation / cluster test** (T4 is already the right shape and passes at 3.2×) as the
decisive line. If the reproducible module-clustering survives a properly pre-registered spatial
test (and ideally under a second, more diffusion-faithful `back-guessed` proxy), THEN the
hypergraph-flow design is warranted. The current evidence leans **structure-exists** but did not
clear the pre-registered battery because that battery mis-specified the concentration test.

Net: the design is **not dead** (reproducible, clustered deviation is real), but it is **not yet
green-lit** (locked ALIVE not met; verdict provisional on a proxy). One corrected measurement
decides it.
