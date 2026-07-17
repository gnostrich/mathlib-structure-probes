# RESULTS — de-gamed (MDL) compression vs the exogenous importance anchor

Pre-registration: `PREREG-compression-mdl.md` (committed before results; the ≥0.58
beyond-depth line and the three outcomes were locked in advance). One narrow question: does a
**de-gamed** compression coordinate predict human importance **beyond plain depth**, or does
importance reduce to foundational depth? Faithful graph (333,044 decls). Script:
`compress_mdl.py`; log: `compress_mdl.log`.

## Metric

`C_mdl(v) = log(1 + max(0, Σ_{v→c} D(c) − D(v)))` — the descendant content **shared** by ≥2 of
`v`'s direct dependencies (charged once). A conjunction `A∧B` of distant `A,B` binds nothing, so
`Σ D(c) − D(v) < 0 → 0`. `D` via bottom-k MinHash (k=160).

## Both gates PASS — the run is VALID

- **Gate 1 (degree decoupling):** `rho(C_mdl, in-degree) = −0.056` → PASS. (`rho(C_mdl, depth) =
  0.902`, slightly less depth-bound than raw C's 0.961.)
- **Gate 2 (anti-gaming):** **0.0%** of the A∧B foils land in `C_mdl`'s top decile (raw `C` was
  32%) → PASS decisively. The MDL reformulation eliminates conjunction-gaming by construction.

## Anchor test (185 positives, exact bridge)

| separator | AUC | perm p |
|-----------|:---:|:---:|
| raw `C` (gameable) | 0.827 | 0.001 |
| depth | 0.814 | 0.001 |
| **`C_mdl`** (de-gamed) | **0.798** | 0.001 |
| reuse (in-degree) | 0.522 | 0.159 (≈ chance) |
| **`C_mdl` beyond depth** | **0.569** | 0.002 |

(both statistics reported: partial Spearman(C_mdl, Y | in-deg, depth) = −0.105 — inert, see
Standing Result 2.)

## VERDICT — **REDUCES** (importance ≈ foundational depth)

The foil gate passed, but the decisive number — **`C_mdl`-beyond-depth AUC = 0.569** — is
**below the pre-committed 0.58 line** (it is significantly above 0.5, p=0.002, but sub-threshold).
Compared to raw `C`'s beyond-depth AUC of 0.616: once the conjunction-inflatable
descendant-union component is removed, the beyond-depth surplus shrinks 0.616 → 0.569 and drops
under the bar. Per the locked outcomes:

> **REDUCES:** the +0.616 surplus of raw `C` was partly gameable inflation; the de-gamed,
> incorruptible compression signal beyond depth (0.569) does not clear 0.58. **Human importance
> reduces (essentially) to foundational depth** — the amount of accumulated structure a result
> sits atop. A judge should be built on **depth** (AUC 0.814), not a separate compression axis.

This is a **sharpening, not a failure**: the exogenous anchor localized the importance signal to
a single, simple structural quantity (depth), and showed the extra "compression" machinery adds
only a small, sub-threshold amount once de-gamed.

**Honest caveats (both directions):**
- The beyond-depth signal is *not zero* — 0.569 (p=0.002) is a real, significant near-miss. So a
  whisper of gaming-resistant compression beyond depth exists; it simply did not clear the
  pre-registered bar, and I hold the line I set before seeing the number.
- **Depth is itself conjunction-gameable** (`depth(A∧B) = 1 + max(depth A, depth B)` inherits a
  deep conjunct). So "build on depth" carries its own anti-gaming debt: the coordinate that IS
  gaming-resistant (`C_mdl`-beyond-depth) is sub-threshold, and the coordinate that carries the
  importance signal (depth) is gameable. The clean incorruptible-importance coordinate was not
  found; importance ≈ depth, with depth's gaming to be handled by a future judge separately.

## Standing results banked this session (independent of the above)

1. **Reuse-kill, anchor-validated:** reuse (in-degree) AUC(famous) = **0.522, p=0.16 ≈ chance**.
   Loops = reuse ≠ importance, proven against external human truth. This does not ride on `C_mdl`.
2. **Imbalance methods lesson + PROOF:** a **perfect** ranker of the anchor (AUC = 1.000) yields
   plain Spearman(Y) = **+0.041** and partial Spearman(Y | in-deg, depth) = **+0.003**. So even a
   perfect ranker is capped near 0 by the 0.056% prevalence — the earlier −0.08 partial-Spearman
   for `C` was within this mechanically-inert band, NOT evidence against the signal.
   **Transferable result: rank-correlation is the wrong statistic under extreme class imbalance;
   threshold-free AUC + permutation is correct.** Always report both.
