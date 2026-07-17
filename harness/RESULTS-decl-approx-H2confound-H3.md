# RESULTS — degree confound on H2 + H3 foils (approx decl graph)

Substrate: the **approximate** declaration reference graph of Mathlib `v4.28.0`
(`213,929` decls / `1,574,452` edges after restricting to declared nodes),
i.e. statement/body references only — it **misses proof-synthesized edges**
(simp/omega/typeclass/tactic-invoked lemmas). A faithful (built-env) graph is
still pending an unblocked Lean toolchain (see "Environment block" below). All
numbers below are reproducible with a fixed RNG seed:

```
python harness/loop_veto_test.py decl_ref_graph_mathlib.jsonl
```

This document covers the two tasks that do **not** require a Lean build:
**Task 4 (degree confound control on H2)** and **Task 5 (H3 foils)**. H1 is
unchanged from the prior run (GO-precondition).

---

## H1 (unchanged) — dissociation = GO-precondition
- `rho(L, slide=depth) = 0.267`, `rho(L, in-degree) = 0.419`
- `R2(L ~ slide+deg) = 0.016`
- off-diagonal terciles populated: high-slide/low-loop = 9,927, low-slide/high-loop = 24,427

Loop-residue L (triangle count) is a distinct axis from slide/depth. Precondition holds.

---

## Task 4 — H2 does NOT survive a proper degree control

The prior session reported the H2 payoff as `partial rho(L, Y2 | depth) = 0.485`
(Y2 = log in-degree = in-library citation proxy). The handoff flagged the open
confound: **L (triangles) and Y2 (in-degree) both grow with node degree**, and
the baseline partial controls depth only.

Adding degree controls (multiple-control partial Spearman on ranks):

| control set                                   | partial rho(L, Y2 \| controls) |
|-----------------------------------------------|:------------------------------:|
| depth only (baseline)                         | **0.485** |
| depth + log **out**-degree                    | 0.567 |
| depth + log **undirected**-degree             | **−0.046** |
| depth + log out + log undirected              | 0.104 |
| depth + log **in**-degree (near-circular floor) | 0.014 |
| residual-corr method (regress both on {depth, log-udeg}) | −0.046 |

**Read.** The honest control is **undirected degree** — the quantity a node's
triangle count `L` mechanically scales with (a node in many triangles has high
in+out degree). Under that control the payoff **collapses from 0.485 to −0.046**,
and the residual-correlation cross-check agrees (−0.046). The `out-degree`-only
control going *up* to 0.567 is a red herring: out-degree is proof *breadth*, not
the triangle driver, so partialing it out removes shared "breadth" variance and
inflates the spurious L–Y2 link. Controlling `in`-degree is near-circular
(Y2 *is* log in-degree) and is reported only as a floor.

**Per the pre-registration's own criterion** ("if it collapses to ~0 under a
degree control, H2 has not really cleared"): on the approx graph **H2 has NOT
cleared**. The 0.485 was largely a node-degree artifact. Y1 (theorem/lemma label)
was ≈0 at baseline and stays ≈0 under every control, as before.

---

## Task 5 — H3 incorruptibility foils

The graph-only harness cannot re-run the Lean prover, so H3(a)/(b) are realised
as **graph-theoretic operationalisations** of the pre-registered foils, run on
the decl graph. They are honest structural proxies, not prover reproofs.

### H3(a) gaming foil — cheap cross-region conjunctions → **PASS**
A conjunction `A ∧ B` is modelled as a node `C` with out-edges `C→A`, `C→B`
(it "uses" A and B). In the undirected complex, `C` sits in a triangle **iff
A ~ B**. We sample 3,000 **distant** pairs (non-adjacent *and* no common
neighbour, i.e. graph distance ≥ 3), inject the foils, and recompute triangles:

- foils receiving ANY loop credit (triangles > 0): **0 / 3000 (0.00%)**
- real endpoints whose loop credit CHANGED after injection: **0 / 2000**
- (context: median triangle count of real loop-bearing decls = 8; foils sit at the floor 0)

So a cheap conjunction of two unrelated lemmas gets **zero** loop credit and
**cannot inflate** any existing node's credit (a foil can only add the single
triangle `C–A–B`, which requires `A~B`). The triangle-based loop meter is not
gamed by the Schur–MASA-style fake-success construction. **PASS.**

### H3(b) warm/cold floor — reuse-shortcut minimisation (proxy; needs prover to certify)
Pre-reg: only the loop residue surviving **minimal independent reproof**
(`L_cold`) gets veto authority; `L_warm − L_cold` is path debt. A faithful split
needs the prover; the pre-reg says so. The best prover-free structural proxy:

> a directed edge `u→v` is a **reuse shortcut** if `v` is reachable from `u`
> via ≥ `REDUNDANCY_MIN` **distinct** 2-hop intermediates `w` (`u→w→v`). Strip
> those edges → cold graph → `L_cold = triangles(cold)`.

The naive "strip *any* 2-hop-redundant edge" is **degenerate**: a directed
triangle `a→b→c, a→c` has its closing edge `a→c` redundant via `b` *by
definition*, so it removes the closing edge of **every** triangle and drives
`L_cold → 0` mechanically (observed: 7.8M → 1,317). Requiring **multiple**
independent intermediates lets bare/essential triangles (exactly one
intermediate per edge) survive, and strips only genuinely reused shortcuts:

| REDUNDANCY_MIN | cold survival | Spearman(L_warm,L_cold) | rho(L_cold,Y2\|depth) | \| +WARM-udeg | \| +COLD-udeg |
|:---:|:---:|:---:|:---:|:---:|:---:|
| 2 | 6.9% | 0.594 | 0.512 | 0.326 | **0.186** |
| 3 | 14.4% | 0.713 | 0.588 | 0.343 | **0.226** |

**Read.** The honest control for `L_cold` is its **own** (cold) undirected
degree. Where the warm metric's payoff *collapsed* to −0.046 under degree
control, the reuse-stripped `L_cold` residue keeps a **weak positive** partial
(**≈0.19–0.23**) even under its own degree control. That is *suggestive* — the
incorruptible residue may carry a little signal the raw metric doesn't — but it
is **well below any GO bar**, on the approx graph, and via a static proxy. It is
**not** a cleared H2. A built-env minimal reproof is required to certify
`L_cold` as the true incorruptible residue.

---

## Overall verdict on this substrate

- **H1**: GO-precondition ✓
- **H2**: baseline 0.485 → **degree-controlled −0.046 → DOES NOT CLEAR** (payoff was largely a degree artifact)
- **H3(a)**: PASS (distant `A∧B` foils not credited; real credit unchanged)
- **H3(b)**: warm payoff collapses under degree control; only `L_cold` keeps a weak ~0.19–0.23 residual (suggestive, not a bar; static proxy)
- **OVERALL: AMBIGUOUS → DO NOT WIRE.** The wiring step (docs/05) is gated on H2
  clearing on the **faithful** graph AND H3 holding; H2 does not clear on the
  approx graph, so per the pre-registration we do **not** proceed to wiring.

This is the honest read: the previously headline `0.485` was not robust to the
degree confound the handoff itself flagged. Whether the *faithful* (proof-edge)
graph — which the approx graph is a weak, edge-missing proxy of — behaves
differently is the open question, and it needs a built Lean environment.

---

## Environment block (why the faithful run still didn't happen)

The faithful graph needs a Lean toolchain + Mathlib oleans. In this session the
required downloads are **policy-blocked at the egress gateway** (git-clone and
`raw.githubusercontent.com` work; the release/asset/cache hosts do not):

| host / path                                             | result |
|---------------------------------------------------------|--------|
| `github.com/.../releases/download/*` (elan + lean toolchain) | HTTP **403** |
| `api.github.com` (asset-API fallback)                   | HTTP **403** |
| `objects.githubusercontent.com` / `release-assets.githubusercontent.com` | reachable but only via a signed URL minted by the blocked hosts |
| `mathlib4.blob.core.windows.net` (`lake exe cache get` oleans) | **502** (policy denial, per proxy status) |
| `releases.lean-lang.org` (Lean mirror)                  | 302-redirects **back to** the blocked github path |
| `github.com` via git, `raw.githubusercontent.com`, pypi | **OK** |

The egress policy binds at **session start**, so enabling access mid-session does
not reach the already-running container — a **fresh session** on the updated
environment is required. Hosts to allowlist for the faithful build: `github.com`
release-download paths, `api.github.com`, `*.githubusercontent.com`, and
`*.blob.core.windows.net`.
