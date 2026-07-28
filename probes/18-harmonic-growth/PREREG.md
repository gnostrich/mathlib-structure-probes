# PRE-REGISTRATION — Probe 18: harmonic-measure growth on a non-amenable graph

**Committed before any run.** One round, terminal. No follow-up rounds under this method.

## Question

Two candidate growth rules for adding to an existing structure:

- **LOCAL (Eden)** — pick uniformly among perimeter sites. Compact blob.
- **HARMONIC (DBM, η = 1 ≡ DLA)** — growth rate at a perimeter site ∝ the harmonic measure
  there. Tips are more exposed, so tips grow faster: an instability that produces branches.

Does the local/harmonic distinction still separate on a graph whose balls grow **exponentially**?
If branching genuinely requires the harmonic rule, the resolvent is a growth *driver*, not a
measurement instrument. This probe is a **precondition** for that argument, nothing more.

## Method — and why it is not the previous one

The prior attempt (probe 17b) sampled random walkers and deposited at first contact. On Z² that
worked; on T₃ × Z it did not — the walk is strongly transient, escape probability → 1, arrival
rate decays exponentially in launch radius, and **18–67% of depositions fell back to a
deterministic rule** instead of a walker hit. That arm was contaminated and was declared VOID,
terminal under the Monte Carlo method. **That method is not repeated here.**

The successor is the **Dielectric Breakdown Model** (Niemeyer–Pietronero–Wiesmann 1984), which at
η = 1 is equivalent to DLA. No walkers; solve for the harmonic measure directly.

Per deposition:

1. Truncate to the ball `B = {v : dist(v, origin) ≤ R_out}`.
2. Solve the discrete Laplace equation for `h`:
   - `h = 0` on every cluster node (Dirichlet),
   - `h = 1` on every node at distance `> R_out` (Dirichlet — the outside),
   - `h(v) = mean of h over the graph-neighbours of v` elsewhere.
3. Candidate growth sites = nodes adjacent to the cluster, not in it, inside `B`.
4. Choose the next site with probability ∝ `h(b)^η`, **η = 1**.
5. Add it; repeat.

On both substrates a single graph step changes `dist` by exactly ±1 (Z²: Euclidean distance
changes by at most 1 per step), so "neighbours outside `B` are Dirichlet 1" is a well-posed
truncation and every unknown's neighbours are either unknowns or Dirichlet.

### Solver — pinned now

- The Dirichlet Laplacian on the unknown set is symmetric positive definite. Solve with
  **`scipy.sparse.linalg.cg`, relative tolerance `rtol = 1e-9`, `maxiter = 20000`**, **warm-started**
  from the previous deposition's solution (the cluster changes by one node, so the field barely moves).
- **Solver validation, reported:** on the **first 20 depositions of every run**, the CG solution is
  compared against an exact sparse direct solve (`scipy.sparse.linalg.spsolve`); the maximum
  absolute deviation in `h` over all those solves is reported in RESULTS. This is a solver check,
  not an outcome.
- If CG fails to converge at any step, that step falls back to `spsolve` and the count of fallbacks
  is reported. (A fallback is exact, so it does not contaminate the arm — unlike 17b's fallback,
  which substituted a *different growth rule*.)

### Truncation radius

`R_out = R_max(cluster) + margin`, recomputed whenever `R_max` grows.

- **Z²**: margin **15**. Truncation-convergence harness cell re-runs the Z² DBM arm at margins
  **10** and **25**.
- **T₃ × Z**: margin **5**. A ball of radius `r` here holds ≈ `3·2^r` nodes, so a margin of 25 — or
  even 10 — is computationally impossible (millions of unknowns per deposition, one solve per
  deposition). Declared **deviation**: the fixed truncation-convergence *harness cell* is the Z²
  one specified in the directive; on T₃ × Z a convergence check at margins **3** and **7** is run on
  one seed and **reported**, but is not VOID-bearing. Transience cuts both ways: on a non-amenable
  graph the harmonic measure is expected to converge in `R_out` far faster than on Z², which is
  exactly why the Z² cell is the demanding one.

## Substrates

- **HARNESS — Z²**: nodes `(x,y)`, 4-neighbours, `dist` = Euclidean from origin.
- **TEST — T₃ × Z**: node = `(v, z)` with `v` a tuple of tree digits. Neighbours of `(v,z)`:
  `(v,z-1)`, `(v,z+1)`, `(v+(0,),z)`, `(v+(1,),z)`, and `(v[:-1],z)` when `v` is non-empty.
  `dist = len(v) + |z|`. Non-amenable; ambient ball growth rate `log 2 ≈ 0.693`. Unlike a bare
  tree it has sideways room, so filamenting is a genuine outcome rather than forced by unique paths.

## Observables

- **Z²**: fractal dimension `D` from radius-of-gyration scaling `R_g ~ N^(1/D)`; `D = 1/slope` of
  `log R_g` against `log N`; **the first 30% of the trajectory is discarded**.
- **T₃ × Z**: exponential growth rate `c` = slope of `ln N(r)` against `r`, `N(r)` = number of
  cluster nodes within distance `r`, fitted over `r ∈ [R_max/4, 3·R_max/4]`. Compare to `log 2`.

## HARNESS-VALIDITY CELL — must pass or the run is VOID

1. On Z²: **Eden `D ∈ [1.90, 2.10]`** AND **DBM(η=1) `D ∈ [1.60, 1.85]`**.
   (A prior Monte Carlo implementation reached 2.092 and 1.805 at N = 2500, so the bands are
   known reachable; this solver must match them independently.)
2. **Truncation convergence**: Z² DBM `D` at `R_out = R_max+10` and `R_max+25` must agree
   within **0.05**.

Either failure **is** the published verdict. Bounds are not adjusted after seeing results.

## INTERPRETATION LADDER — fixed before running, applied mechanically

- **VOID** — harness exponents missed, or truncation convergence fails.
- **PASS** — harness passes AND on T₃ × Z, `c(Eden) − c(DBM) ≥ 0.15` with `c(DBM) < c(Eden)`.
  Harmonic-measure growth filaments where local growth does not, on a non-amenable graph.
- **FAIL** — harness passes AND `c(DBM) ≥ c(Eden) − 0.05`. Harmonic measure does not filament
  here; the resolvent-as-driver motivation loses its support. Published as such.
- **DEGENERATE** — the DBM cluster is a single path (every cluster node has induced degree ≤ 2).
  Reported as DEGENERATE, **not** as PASS: it would mean the graph is too extreme to be a useful model.
- **Anything else** — "inconclusive at this scale with this method". Terminal, recorded as
  **CLOSED**, never as pending.

Ladder inputs are the **mean over seeds** of `c` per arm; per-seed values are reported alongside.

## Declared in advance

- **Prior expectation: the harness is again the risky cell.** The Laplace solve is O(unknowns) per
  deposition and the node count on T₃ × Z grows exponentially in `R_out`, so the achievable cluster
  size may be small. **If the test cell cannot reach a size where the growth-rate fit is
  meaningful, that is INCONCLUSIVE and terminal — not a reason to run it bigger.**
- Target sizes: **N ≥ 2000** on Z², **N ≥ 500** on T₃ × Z. Achieved sizes are stated.
  "Meaningful fit" is pre-defined as: the fit band `[R_max/4, 3R_max/4]` contains **≥ 4 distinct
  integer radii** and `R_max ≥ 6`. Below that → INCONCLUSIVE.
- **Seeds: 3 per arm**, reported per-seed and as a mean. Arms: Z²-Eden, Z²-DBM, T₃×Z-Eden,
  T₃×Z-DBM, plus the two Z²-DBM truncation cells and the two T₃×Z margin cells.
- **Wall-clock budget**: 90 minutes per arm. A run that hits the budget stops and reports its
  achieved N; it is not restarted with different parameters.
- Fixed seeds `0, 1, 2`; `numpy.random.default_rng(seed)` only.

## What a PASS does NOT establish

- **Not** that mathematics grows this way.
- **Not** anything about Mathlib, formal libraries, HM/FM, or any prior probe in this repository.
- Only that the mechanism distinction (local ⇒ compact, harmonic ⇒ filament) survives on an
  exponentially growing graph. **A precondition for the argument, not the argument.**

These statements must appear in the deliverable.

## Occupancy

DBM/DLA on Z² is [occupied] (Witten–Sander 1981; Niemeyer–Pietronero–Wiesmann 1984) and is used
here only as a harness. DLA on trees and non-amenable graphs is also [occupied] (Barlow–Pemantle–Perkins;
Eldan; Benjamini–Yadin on DLA on cylinder graphs). This probe makes **no novelty claim**; it is a
mechanism check on a specific substrate, run to decide whether a downstream argument has a
precondition.

## Deliverable

`probes/18-harmonic-growth/{PREREG.md, solver.py, RESULTS.md}` + one registry line in
`harness/STATUS.md`. PR. If the Laplace solver also fails, the named successor is exact linear
algebra on a smaller truncation — a **fresh probe with a fresh pre-registration**, not a
continuation of this one.

---

## PRE-RUN AMENDMENT (committed before any run; no results seen)

**Feasibility guard on the truncation ball.** The pre-registration above fixes
`R_out = R_max(cluster) + margin` and the directive fixes the domain as *all graph nodes within
`R_out` of the origin*. On T₃ × Z that ball holds ≈ `3·2^R_out` nodes, so a cluster that grows
*tall* — precisely what a filamenting DBM cluster would do — makes the domain explode
super-exponentially (a 500-node filament up the tree would demand a ball of ~2^505 nodes).

Therefore, fixed now:

- **`MAX_DOMAIN = 1_200_000` nodes.** When the required ball would exceed this, the run **stops**
  and reports its achieved `N`. It is **not** restarted with a smaller margin, a different
  substrate, or a re-centred domain.
- A stopped run is treated exactly like the wall-clock budget: **achieved N is reported**, and if
  it falls below the pre-defined meaningful-fit threshold (fit band ≥ 4 distinct integer radii and
  `R_max ≥ 6`), the verdict rung is **INCONCLUSIVE and terminal**, not a licence to re-run.
- The guard applies to both substrates and both arms; on Z² it is not expected to bind
  (`R_out ≈ 145` ⇒ ≈ 66,000 nodes).

This is a computational-feasibility bound, not an outcome-dependent choice: it is a fixed number,
fixed before any cluster was grown, and any run that hits it is reported as hitting it.
