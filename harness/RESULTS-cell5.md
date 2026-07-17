# RESULTS — cell 5: intrinsic atomicity self-selection (real Schur gate on the graph)

Pre-registration: `PREREG-cell5.md` (committed before results; line locked at curl ≥ 0.20 ALIVE /
≤ 0.10 DEAD). This is the one legitimate reopening move of the program: a BUILD wiring the real
`GramState`/`expand` Schur gate (from `aristotle_3` Lean source) to the Mathlib dependency graph and
letting the gate self-select sites by its own atomicity criterion. Script: `cell5_gate.py`; log:
`cell5_gate.log`.

## The real gate, and confirmation it ran on the bridge

- **Real Schur criterion** (verified against the Lean source `R_A1.lean`:
  `schur A b d = d − dotProduct b (A⁻¹ *ᵥ b)`), computed exactly — not a reimplemented proxy.
- **Bridge (graph → Gram data):** incidence kernel `K(u,v) = |({u}∪deps(u)) ∩ ({v}∪deps(v))|` — a
  genuine PSD Gram matrix (`A Aᵀ`) the gate consumes, `K(v,v) = outdeg+1 > 0`.
- **Confirmation:** the actual `singleton → expand(argmax schur) → …` ran on three bounded regions
  (PartialOrder N=89, Submersive N=108, Defs N=100), admitting every site via the exact Schur gate.
  The real `expand` demonstrably executes on the bridge and produces a self-selected order.

## Why the self-selected ORDER is not the observable (built into the design)

A produced total order is a node-scalar potential → curl identically 0 (tautology, confirmed at
4e-04). The operator-valued content the scalar proxies discarded lives in the object's
context-dependent **Schur preference field** `s(u→v) = schur_add(u|v) − schur_add(v|u) =
[K(u,u)−K(v,v)] + K(u,v)²·(1/K(u,u) − 1/K(v,v))`. The first bracket is a potential; the second
(edge-specific) term is the operator-valued, potentially non-integrable part. Its Hodge curl is the
observable.

## Result

| quantity | curl_fraction |
|----------|:---:|
| tautology (pure node-potential flow) | 4.4e-04 (~0) |
| potential-only part `K(u,u)−K(v,v)` | 1.8e-04 (~0 → any curl is the operator cross-term) |
| **Schur preference field `s`** | **0.0009** |
| scalar-proxy baseline (mean-generation order) | 0.076 |
| intra-module (module control) | 0.0058 (ratio 6.16) |
| reproducibility (edge reorder) | 0.0009 (Δ = 3.8e-08) |

## Verdict — **DEAD.** Cell 5 closed on the real gate. Program epitaph.

`curl_fraction(s) = 0.0009` — the real atomicity gate's preference field is **~99.9% gradient**, and
**85× below the crude scalar proxy (0.076)** it was meant to beat. The operator-valued cross-term
contributes essentially no circulation. Per the locked line (≤ 0.10 → DEAD), this is a clean kill:
**the object's own intrinsic self-selection criterion, run with the real Schur gate, picks an even
*more* perfectly-hierarchical order than the mean-generation proxy did.**

**Faithfulness assessment (prominent, per the rails):**
- The **Schur gate is the real formula** (exact, verified against the Lean def) and the real `expand`
  demonstrably ran on the bridge → this is NOT proxy-provisional on the *criterion* side, unlike the
  mean-generation gate.
- The one residual is the **kernel**: incidence-overlap (a principled, graph-intrinsic PSD Gram) vs
  the object's analytic `V5_1.G` kernel. But `V5_1.G` is defined on real sites in `[0,b]` with **no
  correspondence to Mathlib declarations** — there is no faithful mapping, even in principle. So the
  only escape from DEAD would require the object's power to live entirely in a kernel that cannot be
  put on the graph at all — which is itself the honest conclusion: **the OV Gibbs object is not a graph
  object; wiring it to Mathlib's dependency structure yields a near-perfect gradient, nothing to learn.**
  The DEAD is as non-provisional as this substrate allows.

The result is also mechanistically expected: the substrate was measured ~92% gradient
(`RESULTS-holonomy-gate.md`), so the atomicity gate self-selecting a near-gradient order is the
predicted outcome. This converts the last "but the real object might…" from an open hypothesis into a
**closed, non-provisional result.**

## Program epitaph (what stands after the full arc)

- **The one validated structural correlate of importance is depth** (longest-prerequisite-chain;
  AUC 0.81 vs exogenous fame).
- Everything else was pre-registered, tested, and did not survive: loops = reuse ≠ importance
  (AUC 0.52 ≈ chance); compression adds nothing beyond depth; discrete style/taste = continuous smear;
  order-holonomy = clean hierarchy (curl ≤ 0.076); and now the **real OV atomicity gate self-selects an
  even-more-perfect gradient (curl 0.0009)**. Plus the methods result: partial-Spearman is inert under
  extreme class imbalance; use AUC + permutation.
- The honest end: Mathlib's proof-dependency structure is a near-pure hierarchy whose one legible
  human-meaningful coordinate is depth. The operator-valued / circulation program finds no structure in
  it that a single scalar potential does not already carry.
