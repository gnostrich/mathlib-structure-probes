# PRE-REGISTRATION — de-gamed (MDL) compression vs the exogenous importance anchor

STATUS: pre-registered. Metric, gates, thresholds, and the THREE outcomes fixed BELOW before
results. Committed before the analysis. One narrow question: **does a de-gamed compression
coordinate predict human importance BEYOND plain depth, or does importance reduce to
foundational depth?** No tuning the metric to keep the number up.

Ground truth confirmed at pre-registration (from RESULTS-compression-importance.md): (a) current
`C = log(1+transitive-descendants)`, gate passed `rho(C,in-degree)=−0.04`, AUC(C)=0.827,
AUC(depth)=0.814, C-beyond-depth AUC=0.616; (b) `rho(C,depth)=0.961`; (c) `C` gameable — ~32% of
synthetic A∧B foils hit the top decile; (d) anchor = 185 exact famous-theorem decl matches,
0.056% prevalence.

## The de-gamed metric `C_mdl` (minimum-description-length; conjunction cannot inflate it)

Let `D(v)` = transitive-descendant count (out-reachable set), estimated by bottom-k MinHash
(k = 160, larger than before to cut the variance of the difference below). Define the
**shared/irreducible content `v` binds**:

```
C_mdl_raw(v) = max(0,  Σ_{c : v→c} D(c)  −  D(v) )
C_mdl(v)     = log(1 + C_mdl_raw(v))
```

Rationale (MDL): `Σ_c D(c)` counts each descendant once per child-subtree it lies in; `D(v)`
counts the UNION once. Their difference is the descendant content **shared by ≥2 of `v`'s direct
dependencies** — the overlap `v` charges once by existing. A conjunction `A∧B` of DISTANT
(disjoint-subtree) `A,B` has `Σ D(c) − D(v) = D(A)+D(B) − (D(A)+D(B)+2) < 0 → 0`: it integrates
nothing, so it gains nothing. A theorem whose dependencies genuinely share machinery scores high.
Degree-free by construction (a function of `v`'s out-structure, never its in-degree/usage).

## Gates (BOTH must pass or the run is VOID — no reporting the AUC as if it counted)

1. **Degree gate (identical to before):** `|rho(C_mdl, in-degree)| < 0.40` or `C_mdl` is disqualified.
2. **Anti-gaming gate (now a gate, not a caveat):** regenerate the SAME A∧B foil construction
   (distant A,B, both deep); `C_mdl` must place **< 10%** of foils in its top decile
   (vs the failing 32% for `C`). Foil `C_mdl` computed consistently: for a foil over A,B,
   `C_mdl_raw = D(A) + D(B) − D(A∪B∪{A,B})`, with `D(A∪B…)` from the merged A,B MinHash sketches.

## Test (identical anchor, identical protocol)

Same 185-positive anchor, same faithful graph. Report: AUC for `C_mdl`, depth, reuse (in-degree);
permutation p (1000 label-shuffles); and the decisive number — **`C_mdl`-beyond-depth AUC**
(`C_mdl` residualized on depth-rank, then AUC vs the anchor). Always report BOTH the partial
Spearman and the AUC (no hiding either).

## THREE outcomes (locked now — line pre-committed BEFORE seeing the number)

- **SURVIVES:** foil gate passes AND `C_mdl`-beyond-depth AUC **≥ 0.58** with perm p < 0.01.
  → compression-rank is real AND gaming-resistant → the judge (next session) is built on `C_mdl`.
- **REDUCES:** foil gate passes but `C_mdl`-beyond-depth AUC collapses toward 0.5 (< 0.58 or
  perm p ≥ 0.01). → the +0.616 surplus of raw `C` was gameable inflation. **Verdict: importance ≈
  foundational depth**; the judge is built on **depth** (simpler, non-gameable, AUC 0.81). A
  sharpening, not a failure — write it as such.
- **BROKE:** `C_mdl` loses to raw `C` on the anchor (AUC(C_mdl) materially < AUC(C)=0.827 AND
  beyond-depth < 0.5-ish). → the MDL reformulation discarded real signal → iterate the METRIC
  definition, not the claim; do NOT proceed to a judge.

## Two standing results to bank this session (independent of the outcome above)

1. **Reuse-kill, anchor-validated:** reuse (in-degree) AUC = 0.522, perm p = 0.14 ≈ chance against
   external truth. "Loops = reuse ≠ importance, proven exogenously." Does not ride on `C_mdl`.
2. **Imbalance methods lesson + PROOF:** the pre-registered partial-Spearman (−0.08) is mechanically
   inert at 0.056% prevalence. Prove it: build a PERFECT ranker of the anchor (AUC = 1.0), compute
   its partial-Spearman at this prevalence, confirm it is also ≈ 0. If so, record: "rank-correlation
   is the wrong statistic under extreme class imbalance; threshold-free AUC + permutation is correct."

## Discipline rails
- `C_mdl` degree-free and gaming-resistant BY CONSTRUCTION, gated before use — not rescued post-hoc.
- One anchor, unchanged. No swapping/re-tuning the join.
- If the foil gate fails, the run is VOID — say so; do not report the AUC as if it counted.
- The ≥0.58 beyond-depth line is committed here, before the number is seen.
- Do NOT re-test loops/reuse, add graph-derived importance proxies, or build any judge this session.
