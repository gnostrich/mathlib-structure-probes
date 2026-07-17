# PRE-REGISTRATION — degree-normalized judge robustness (Phase 0) + retrodictive conjecturer (Phase 1)

STATUS: pre-registered. Metrics + thresholds fixed BELOW, before running. No post-hoc
tuning. Committed before Phase 0/1 results land. Discipline rails (held throughout):
1. the loop metric is **non-learned** and **degree-normalized by construction** (never
   tuned to pass; the moment it is tuned, it is fakeable);
2. predicted-potential (forward) and realized-residue (backward) must be **the same meter**
   run in two directions, not two different scores — that sameness is the single-authority
   property that makes the librarian incorruptible and is the actual delta over Fermat.

Ground truth at pre-registration (from repo preamble): no degree-normalized-by-construction
loop metric is committed (only raw `nx.triangles` and the failed birth-simplex); the judge's
H2 (+0.372) is triangle-only, post-hoc degree-controlled; no frontier/conjecturer code exists.

---

## Phase 0 — degree-normalized judge robustness (THE GATE; runs regardless)

The session proved raw counts are degree-captured (birth-simplex `rho(B,degree)=0.805`, its
degree-controlled H2 went negative). So the one clean lever is a loop coordinate that is
degree-normalized **in the definition**, not by residualizing after the fact.

**Pre-registered metric `Lnorm(v)` — configuration-model triangle residue.** For undirected
degree `k_v` and observed triangles `T_v`, let the degree-preserving (configuration-model)
expectation be
```
E_v = 0.5 * ( (Σ_{i∈N(v)} d_i)^2 − Σ_{i∈N(v)} d_i^2 ) / (2m),   d_i = k_i − 1  (excess degree), m = #edges
Lnorm(v) = (T_v − E_v) / sqrt(E_v + 1)      # z-score-like excess-loopiness, degree-normalized by construction
```
This is non-backtracking (triangles are), degree-normalized by construction (the null absorbs
degree), and is the triangle-order case of "triangle-clustering's normalization generalized to
longer cycles" (length-4+ non-backtracking cycles are intractable at 7.5M edges — documented,
not silently skipped). Secondary reports: ratio `T_v/(E_v+1)` and local clustering coeff `C_v`.

**Recompute the decisive test with `Lnorm`** on the faithful graph, thresholds identical to
`docs/03`:
- `rho(Lnorm, degree)` — confirm the metric is actually degree-decoupled (should be LOW, unlike
  birth-simplex's 0.805; otherwise the metric failed its own design goal).
- H1: `rho(Lnorm, depth)` (dissociation; GO wants ≤0.40, wall ≥0.70).
- H2: partial `rho(Lnorm, Y | controls)` for **Y2 = log in-degree (citation, degree-linked)**
  AND **Y1 = theorem/lemma label (degree-independent Y)**, controls = {depth} and {depth, log-deg}.
- H3(a): distant `A∧B` foil gets `E≈0, T=0 → Lnorm≈0` (not credited) — assert.

**Pre-registered read:**
- **PASS** if degree-controlled partial `rho(Lnorm, Y | depth, deg) ≳ 0.3` with correct sign,
  AND it does not depend solely on the degree-linked Y (i.e. some signal survives against a
  degree-independent Y, or at minimum the Y2 result is not fully explained by degree). Judge is
  real and robust → proceed to Phase 1.
- **FAIL** if it collapses to ~0 (or negative), or holds only for the degree-linked Y2 and is
  ~0 for every degree-independent Y. Then the judge signal was metric/degree-fragile all along:
  a clean publishable NEGATIVE — stop, write it up, do NOT build the conjecturer on a dead
  coordinate.

Both judge and conjecturer inherit `Lnorm`, so Phase 0 is non-negotiable and comes first.

---

## Phase 1 — retrodictive conjecturer (the undone piece; only if Phase 0 PASSES)

Claim under test: **statement-level predicted loop-potential (computable BEFORE any proof)
predicts which theorems, once proven, carry high realized loop-residue.** The signal lives in
proof-synthesized edges you only see after proving, so the forward proxy is strictly weaker than
the backward measurement; whether it survives that gap is the open question.

**Retrodictive design (no prover needed for the core test):**
- Snapshot the faithful graph at an older mathlib4 tag `T0`. For each theorem added after `T0`,
  compute **predicted-potential** = the SAME `Lnorm` meter evaluated using only its TYPE's
  references to objects that existed at `T0` (which regions it would bridge) — never its proof.
- Compute each such theorem's **realized-residue** = `Lnorm` in the CURRENT faithful graph
  (full proof edges).
- **Pre-registered payoff:** partial `Spearman(predicted-potential, realized-residue | degree,
  depth) > 0`, non-trivially (target ≳ 0.2). This one number IS the conjecturer thesis: can you
  rank what is worth attempting before proving it.
- **Baselines it must beat:** random frontier selection; a pure-degree ranker; a pure-subject
  ranker. If predicted-potential does not beat "pick high-degree candidates," the conjecturer
  adds nothing over connectivity.
- **Anti-gaming (H3 forward):** inject synthetic trivial cross-region statements (`A∧B`, distant
  A,B); the predicted-potential ranker must NOT rank them highly. If it does, statement-level
  bridging is gameable and the conjecturer is corruptible.

**Read:** Phase 0 pass + Phase 1 pass = judge and conjecturer both real → greenlight Phase 2.
Phase 0 pass + Phase 1 fail = judge real, conjecturer can't see the proof-edge signal from the
statement (a sharp, honest negative about the forward/backward gap that saves prover compute).

---

## Phase 2 — closed-loop prover demo (only if Phase 1 clears)

Take top-K frontier candidates by predicted-potential, hand to Aristotle, measure: (a) provable
fraction; (b) whether proven high-realized-residue results are judged interesting by human
spot-check vs a random-frontier control. Expensive; gated behind Phase 1 so no prover compute is
spent on an unvalidated ranker.

## Verdict grid (pre-committed)
| outcome | meaning |
|---|---|
| Phase 0 pass + Phase 1 pass | incorruptible directed-librarian validated on measurement → Phase 2 |
| Phase 0 pass + Phase 1 fail | judge real, conjecturer doesn't work (forward/backward gap) — honest negative, saves prover |
| Phase 0 fail | loop signal was a triangle/degree artifact; both fall; write the negative and stop |
