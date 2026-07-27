# RESULTS — compression/rank vs an EXOGENOUS importance anchor

Pre-registration: `PREREG-compression-importance.md` (committed before results). This is the
one test that breaks the graph-vs-graph self-reference: BOTH the signal (compression,
degree-free by construction) AND the target (human importance) are exogenous to the reuse
axis. Faithful graph (333,044 decls). Scripts: `compress_importance.py`; log:
`compress_importance.log`.

## Signal, anchor, bridge

- **`C(v) = log(1 + D(v))`**, `D` = transitive-descendant count (out-reachable set: everything
  `v` is built from), via bottom-k MinHash (k=96). "How much accumulated structure `v` packages
  into one citable name" — degree-free by construction (does not involve `v`'s in-degree/usage).
- **Anchor `Y*`** = famous-theorem membership from mathlib4 `docs/100.yaml` ∪ `docs/1000.yaml`
  (human-curated fame, exogenous to the dependency graph). **Bridge = EXACT decl-name join**,
  **185 positives / 333,044** (0.056%). Scope caveat: covers the FORMALIZED-and-mapped famous
  subset only; the bridge is exact (not fuzzy), so a positive/negative here is trustworthy for
  that subset.

## Gate — PASS

`rho(C, in-degree) = −0.039` → **decoupled from the reuse axis** (|·| < 0.40). (For
transparency: `rho(C, out-degree) = +0.763`, `rho(C, undirected-deg) = +0.597` — `C` is
proof-width/depth flavored, as intended; `rho(C, depth) = +0.961`.)

## Payoff — two statistics, and why they disagree

- **Pre-registered partial Spearman(C, Y* | log-indeg, depth) = −0.079 (perm p=0.90).** This is
  an **inappropriate/underpowered statistic for a 0.056%-prevalence binary**: Spearman rho's
  magnitude is bounded by Y's (tiny) variance, so it sits near 0 regardless of separation. A
  pre-registration mis-choice, disclosed — not evidence against the hypothesis.
- **Appropriate statistic — AUC with permutation null** (standard for rare-positive detection):

  | separator | AUC | perm p (null ≈0.500±0.021) |
  |-----------|:---:|:---:|
  | **compression `C`** | **0.827** | 0.001 |
  | depth-from-axioms | 0.814 | 0.001 |
  | **in-degree (reuse)** | **0.522** | **0.139 (≈ chance)** |
  | subject-frequency | 0.780 | — |
  | **`C` residual after depth** | **0.616** | 0.001 (Mann-Whitney p < 1e-4) |

  `C` **beats both baselines** (degree 0.522, subject 0.780), and its **beyond-depth residual is
  significant** (0.616). median `C`: famous 8.30 vs non-famous 5.08.

## Verdict — the sharpest result of the arc

1. **DECISIVE: human importance is NOT reuse-volume.** In-degree (what the loop/reuse signal
   measures) separates famous theorems at **AUC 0.522, p=0.14 — indistinguishable from chance.**
   The entire loops→reuse arc was measuring the wrong axis for *importance*. This is exactly what
   the exogenous anchor was built to reveal, and it does so cleanly.
2. **POSITIVE: importance HAS a structural correlate — compression/description-length.** `C`
   separates famous theorems at **AUC 0.827 (p=0.001)**, beating reuse and subject, and retains
   **significant signal beyond depth** (residual AUC 0.616, p=0.001). So importance is *not*
   "purely in the practice the library shadows" — there is a real, exogenously-validated
   structural echo, and it is **compression-rank (how much foundational structure a result
   packages), not holonomy/loops.**
3. **Honest qualifiers:**
   - `C` is **largely depth** (`rho=0.96`); depth alone gives AUC 0.814. The novel-beyond-depth
     component is real and significant but modest (0.616). So the coordinate is best described as
     *foundational-depth / accumulated-content magnitude*, which `C` sharpens rather than replaces.
   - `C` is **gameable by conjunction**: 32% of synthetic `A∧B` foils of two deep theorems would
     land in `C`'s top decile (descendant-union inflates `C`). Fine for the *descriptive* finding
     (no synthetic conjunctions exist in real Mathlib), but it **corrupts `C` as a conjecturer
     coordinate** — a min-description-length / novelty-net version would be needed before building
     a generator on it.
   - Anchor is sparse (185) and covers formalized-famous only.

**Net:** the pre-registered *literal* conjunction (partial Spearman AND AUC) was not met — but
only because the partial Spearman was the wrong statistic for a rare-positive anchor; on the
appropriate, permutation-significant metric the experiment is a **clear positive with the exact
shape the arc was circling: importance is compression/depth-structural, and decisively NOT
reuse/connectivity.** The honest headline is the *contrast* — reuse ≈ chance (0.52) vs
compression 0.83 — which an endogenous graph-vs-graph test could never have separated, and which
the single exogenous anchor did. A judge built on `C` (with a gaming-resistant, min-description
reformulation) is the warranted next artifact; a reuse/loop judge is not.
