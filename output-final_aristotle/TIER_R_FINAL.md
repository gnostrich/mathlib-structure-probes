# Tier R — final status

Tier R is closed at the strongest fully certified rung obtained in this repository.

## Certified general engine

`R5.gershgorin_margin` is proved for arbitrary finite real symmetric matrices. If every row has diagonal-dominance margin at least `μ`, it gives the quadratic-form floor

`μ * ∑ i, x i ^ 2 ≤ quadForm M x`.

The theorem is general in the matrix size and does not hide a sign assumption on `μ`.

## Full-band three-site coverage

`R5.coverage_band_k` and its alias `R5.coverage_band_final` certify the genuine kernel `V5_1.G` on the whole band `[1/5,3/5]` for three strictly increasing sites under the explicit total-pairwise mesh condition

`1/5 ≤ |t i - t j|` for `i ≠ j`.

They prove positive definiteness and the explicit Rayleigh floor

`1/200 ≤ lambdaMin (fun i j => V5_1.G (t i) (t j))`.

The mesh condition is load-bearing: `R5.band_three_grid` proves that it forces the unique coarse grid `(1/5,2/5,3/5)`. Thus this is a genuine three-site/full-band theorem, but not a continuum of movable three-site configurations. The positive floor is the audited `V5_5.true_kernel_grid_margin` certificate.

## Why the proposed positive Gershgorin route stops at three sites

`R5.three_grid_last_row_gershgorin_zero` proves an exact identity for the certified three-site grid: in its last row, the diagonal equals the sum of the two off-diagonal entries. Consequently the row's diagonal-dominance margin is exactly zero. The general Gershgorin engine therefore cannot produce a positive three-site floor on this grid, regardless of how sharply the individual entries are enclosed.

This is why the final three-site result uses the stronger direct quadratic-form certificate rather than claiming that the positive margin came from Gershgorin. A uniform analytic diagonal floor and a useful separation-dependent off-diagonal bound for freely moving grids were not established in this final rung.

## Frontier construction

`R5.frontier_covers_band_final` proves the matching frontier statement. Under the same explicit mesh condition, a `TierR.GramState` of dimension three represents the true `V5_1.G` matrix. It reuses the literal construction in `R_A6`: one `singleton` followed by two successful `expand` operations, with both Schur gates already discharged.

## Natural boundary

No fine-grid (`δ → 0`) result is claimed. Such grids accumulate many off-diagonal terms per row, while the requested diagonal-dominance mechanism requires their row sum to stay below a fixed diagonal. Coarse separated grids are therefore the natural scope of this certification method. The final certified rung is the explicit three-site coarse grid above.

## Executable interval engine

R-B2/R-B3 were not added. The priority Objective A was closed at the three-site partial-credit rung, and the existing exact rational checker `R_B1.checkPDq` remains available. The true `(0.2,0.4,0.6)` window continues to have the two existing certified proofs: the bespoke `V5_5` proof and the singleton/expander `R_A6` proof.
