# Tier R5 status

The requested Objective A cannot hold as stated. This is not an incompleteness of the formalization: `RequestProject/R5.lean` contains machine-checked counterproofs identifying two independent obstructions.

1. `R5.PsiArch_not_convex` proves that `V5_1.PsiArch` is **not convex** even on `[0,0.4]`. The already audited enclosures give `PsiArch 0.2 > 0.0543` and `PsiArch 0.4 < 0.0413`, whereas convexity and `PsiArch 0 = 0` would force `PsiArch 0.2 ≤ PsiArch 0.4 / 2`.
2. `R5.coverage_prime_free` proves that no positive `δ, μ` satisfy the requested all-grid coverage claim. The prompt allows `0 ≤ t` and hence the singleton grid `{0}`. Its minimum-gap condition is vacuous, but its Gram matrix is zero because `V5_1.G 0 0 = 0`, so it is not positive definite. `R5.frontier_covers` records the corresponding impossibility of a `GramState` for this grid.

Verified positive portions delivered in `R5.lean`:

- `b = 0.69` and `0 < b < log 2`;
- continuity of `V5_1.L` on nonnegative compact intervals;
- continuity and normalization of `V5_1.PsiArch` on `[0,b]`;
- the exact R5-2 two-by-two determinant identity;
- a quantitative two-by-two diagonal-dominance Rayleigh-floor lemma;
- the existing audited `(0.2,0.4,0.6)` frontier construction, tied to `V5_1.G` and built by singleton/expand.

Objective B was not started because the delivery notes prioritize it only after Objective A is complete and building; Objective A's headline assertions are false under the stated hypotheses. A corrected follow-up should at minimum exclude the zero grid point (for example require `δ ≤ t 0`) and replace the false convexity premise with an analytically valid property. Even those changes do not by themselves establish arbitrary-size uniform coverage and would require a new statement and proof.
