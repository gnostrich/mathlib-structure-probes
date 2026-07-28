# RESULTS — Probe 18: harmonic-measure growth on a non-amenable graph

Pre-registration `PREREG.md` (+ its pre-run amendment) committed before any cluster was grown;
`solver.py` committed before the registered cells were run. Dielectric Breakdown Model
(Niemeyer–Pietronero–Wiesmann 1984) at η = 1 ≡ DLA, by **direct Laplace solve** — no walkers.
One round, terminal.

## VERDICT — **VOID.** Truncation convergence failed.

The ladder's first rung fires: *"VOID — harness exponents missed, or truncation convergence fails."*

| harness cell | requirement | measured | |
|---|---|---|---|
| Z² Eden `D` | ∈ [1.90, 2.10] | **2.0597** (2.046 / 2.137 / 1.996) | PASS on the mean |
| Z² DBM(η=1) `D` | ∈ [1.60, 1.85] | **1.6841** (1.832 / 1.576 / 1.644) | PASS on the mean |
| **truncation convergence** | \|D(R_max+10) − D(R_max+25)\| ≤ 0.05 | **0.1017** (1.6462 vs 1.7479) | **FAIL** |

Either harness failure *is* the published verdict. Bounds were not adjusted after seeing results.
No follow-up round under this method.

## Why it failed — the honest diagnosis

The convergence cell is a **single-seed** comparison, and at N = 2500 the seed-to-seed spread of
Z² DBM `D` at a *fixed* margin is **0.256** (1.576 – 1.832) — five times the 0.05 tolerance the
cell demands. So the 0.1017 gap between margins 10 and 25 is **not distinguishable from estimator
noise**: the test as specified cannot be met at this cluster size and seed count regardless of
whether the truncation is actually contaminating the field.

That is a defect of the pre-registered test, discovered by running it. It is recorded, not
repaired: re-running with more seeds or larger N to get inside the tolerance would be exactly the
outcome-dependent adjustment the pre-registration forbids. **The verdict stands as VOID.**

Note also the direction: D(m10) = 1.646 < D(m15) = 1.832 and D(m25) = 1.748 is not monotone in the
margin, which is itself consistent with noise dominating rather than a clean truncation bias.

## The test cell — reported, NON-ADJUDICATING

The harness failed, so these numbers decide nothing. They are published because nulls and walls are
first-class outputs, not because they carry a verdict.

| T₃ × Z arm | c (seed 0 / 1 / 2) | mean | achieved N | R_max |
|---|---|---|---|---|
| Eden | 0.3002 / 0.2584 / 0.3059 | **0.2882** | 500 / 500 / 500 | 14 / 16 / 14 |
| DBM(η=1), margin 5 | 0.2377 / 0.2859 / 0.2766 | **0.2667** | 146 / 185 / 167 | 13 / 13 / 13 |

`c(Eden) − c(DBM) = 0.0214`, far below the 0.15 PASS threshold; ambient rate is `log 2 = 0.693`.
Both arms are well below ambient. No DBM cluster was a single path (DEGENERATE does not apply).

**These two arms are not comparable and were never made comparable.** Every T₃ × Z DBM run hit the
pre-registered `MAX_DOMAIN` guard at N = 146–185, far short of the 500 target: continuing would have
required a ball of **1,572,823** nodes against the 1,200,000 cap. The Eden arm ran to 500. No
N-matched comparison was pre-registered and none is introduced now. So even had the harness passed,
this pair could not have been read off the ladder honestly.

T₃ × Z margin sensitivity (seed 0, reported, never VOID-bearing): `c` = 0.2203 (margin 3, N=214),
0.2377 (5, N=146), 0.3057 (7, N=104). The spread is confounded with achieved N, since a larger
margin exhausts the node cap sooner.

## Solver validity — clean

- **0 CG fallbacks** across all 16 cells (10 DBM cells, 8,000+ Dirichlet solves).
- Max deviation of warm-started CG against exact sparse-direct `spsolve`, over the first 20
  depositions of every run: **≤ 3.6e-8** (Z² ≤ 6.8e-9).
- No cell hit the 90-minute budget; the longest was 132 s.

The instrument did what it was built to do. **Unlike probe 17b, no deposition anywhere in this run
fell back to a different growth rule** — the fallback path here is an exact linear solve, and it was
never taken. The method change fixed the contamination it was designed to fix; it failed on a
different cell.

## What is NOT claimed

- **Not** that mathematics grows this way.
- **Not** anything about Mathlib, formal libraries, HM/FM, or any other probe in this repository.
- **Not** that harmonic-measure growth fails to filament on T₃ × Z. The harness voided the run, the
  test arms are not N-matched, and both stopped at a third of the target size. The `c` values above
  are measurements of what was actually grown, nothing more.
- **Not** that the truncation *is* contaminating the field. What is established is that the
  pre-registered convergence test cannot resolve the question at this scale — the estimator's own
  seed variance swamps its tolerance.
- **Not** a validated precondition for the resolvent-as-growth-driver argument. That precondition
  remains **unestablished**, neither supported nor refuted by this run.
- **No novelty claim.** DBM/DLA on Z² is [occupied] (Witten–Sander 1981; NPW 1984); DLA on trees and
  non-amenable graphs is [occupied] (Barlow–Pemantle–Perkins; Benjamini–Yadin). [proven-negative]
  for this method at this scale.

Even a PASS would only have shown that the mechanism distinction (local ⇒ compact, harmonic ⇒
filament) survives on an exponentially growing graph — **a precondition for the argument, not the
argument.**

## Named successor (not authorised here)

Per the directive: exact linear algebra on a smaller truncation. That would be a **fresh probe with
a fresh pre-registration**, and it should first fix the defect found above — a convergence tolerance
must be stated relative to the estimator's own seed variance, not as an absolute 0.05.

## Reproduce

```
python probes/18-harmonic-growth/solver.py --graph z2  --rule eden --n 2500 --seed 0 --margin 15 --out z2_eden_s0.json
python probes/18-harmonic-growth/solver.py --graph z2  --rule dbm  --n 2500 --seed 0 --margin 10 --out z2_dbm_s0_m10.json
python probes/18-harmonic-growth/solver.py --graph t3z --rule dbm  --n 500  --seed 0 --margin 5  --out t3z_dbm_s0_m5.json
```

All 16 cell records are in `cells/` (`all_cells.log` is the one-line-per-cell summary).
scipy 1.17.1, numpy 2.4.6; single-threaded BLAS; fixed seeds 0/1/2 via `numpy.random.default_rng`.
