# RESULTS — order-holonomy gate (Hodge curl of the dependency comparison flow)

Pre-registration: `PREREG-holonomy-gate.md` (committed before results; lines locked). Intrinsic
(no proxy, no commit dates). Faithful graph (333,044 / 7,523,067). Script: `holonomy_gate.py`;
log: `holonomy_gate.log`.

## Tautology check (demonstrated, not just asserted)

curl_fraction of a pure node-potential flow = **7.6e-05 ≈ 0** → confirms that the *literal*
"holonomy of the guess-vs-actual node-order residual" is identically zero (a gradient has no curl).
The literal measurement carries no information; the well-posed observable below is what was measured.

## The well-posed observable

| quantity | value |
|----------|:---:|
| **curl_fraction (global)** — antisymmetric residual after quotienting the topological gradient | **0.076** |
| curl_fraction (intra-module, control) | 0.149 (ratio intra/global = 1.96) |
| curl_fraction (reordered edges, reproducibility) | 0.076 (Δ = 4.8e-9) |

(The global lsqr hit its iteration cap, so 0.076 is an **upper bound** — more iterations fit the
gradient better and would only *lower* the curl. The kill is robust to non-convergence.)

## Verdict — **DEAD (real, non-provisional). The thread ends here.**

The locked decisive line was `curl_fraction (global) ≥ 0.15`. It is **0.076 (≤ 0.076)** — the unit
dependency comparison flow is **~92% a clean gradient/hierarchy**, with only ~7.6% circulation. Per
the pre-registration this is a **DEAD**: the accumulation order is essentially a clean hierarchy, so
back-then-forward collapses to forward (already known to fail). Because the observable is intrinsic
(the real dependency graph, no Gibbs proxy), **this DEAD is not proxy-provisional — it is a genuine
kill**, and I honor it without reinterpretation.

**Honest reporting of the non-zero part (not an escape hatch):** the circulation is not literally
zero — it is real (7.6%), perfectly reproducible (Δ = 5e-9), and it actually *survives* module
conditioning (intra-module curl 0.149 is ~2× the global; the control that could have killed it as
"cross-module coarse topology" instead shows circulation concentrates *within* modules). But the
**pre-committed magnitude bar was global curl ≥ 0.15, and 0.076 fails it.** I am not going to spin
"survives module conditioning" or "intra-module ≈ 0.15" into an AMBIGUOUS re-run — that is exactly
the motivated reinterpretation the pre-registration forbade. The framing said it would die on this
number; the number is 0.076; it dies. **The order-holonomy / back-then-forward design is closed.**

## What this closes, and what stands

Closed: the "train a Gibbs reverse-flow on back-guess/back-actual deviation" thread. Mathlib's
accumulation order is a predominantly clean hierarchy; there is no substantial, learnable
non-topological circulation in it.

Standing results from the arc (independent, durable):
- **Importance ≠ reuse/loops** — reuse AUC 0.52 ≈ chance vs exogenous fame (`RESULTS-compression-importance.md`).
- **Importance ≈ foundational depth** (AUC 0.81); de-gamed compression adds nothing beyond depth
  (`RESULTS-phase0-normloop.md`, `RESULTS-compression-mdl.md`).
- **Method:** partial-Spearman is inert under extreme class imbalance (perfect ranker → ρ≈0.04);
  use AUC + permutation.
- **Order structure:** the dependency order is ~92% pure hierarchy (this file).

The honest net: **depth is the one validated structural correlate of importance; loops, reuse,
compression-beyond-depth, discrete style-modes, and order-holonomy were each tested and did not
survive.** That is where the evidence stands.
