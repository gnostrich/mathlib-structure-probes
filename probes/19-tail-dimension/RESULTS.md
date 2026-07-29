# RESULTS — Probe 19: tail dimension of Mathlib (Hankel rank of the prerequisite tape)

`PREREG.md` committed before the tape was built; `tape.py` and `spectra.py` committed before any
spectrum was computed. ONE ROUND, single batch, 36 cells. Prior art: **arXiv:2604.24797, "The
Network Structure of Mathlib"** — structural/network analysis of the same corpus, not
information-theoretic; *their* finding that centrality captures infrastructure rather than
mathematical relevance is cited here as theirs, not restated as new.

## VERDICT — **VOID. The harness-validity cell failed. CLOSED.**

The synthetic arm — a hand-built **3-state** HMM, ground truth known — was required to return
effective rank 2–4 at every (k, L). It returned **1, 2, 3, 3, 73, 104, 18, 36, 46, 2, 59, 35**,
failing **8 of 12** cells. Per the pre-registration the pipeline is broken, the run is VOID, that
failure is itself the published verdict, and **the real arm is not interpreted.**

## The 36-cell matrix (effective ranks — raw, uninterpreted)

Effective rank = number of singular values above the 95th percentile of the shuffle spectrum at the
same (k, L). Alphabets: k=0 → 3, k=1 → 95, k=2 → 2000 (hashed from 11,756), k=3 → 2000 (hashed from
143,823). R = 3 throughout; 20,000 declarations; seed 20260729.

| k | L | real | shuffle | **synthetic (must be 2–4)** | mean count / past (real / shuf / synth) |
|---|---|---|---|---|---|
| 0 | 1 | 2 | 1 | **1 ✗** | 81653 / 81653 / 81653 |
| 0 | 2 | 2 | 1 | 2 ✓ | 25109 / 25109 / 25109 |
| 0 | 3 | 12 | 2 | 3 ✓ | 7687 / 7687 / 7687 |
| 1 | 1 | 40 | 5 | 3 ✓ | 2916 / 2916 / 2692 |
| 1 | 2 | 52 | 15 | **73 ✗** | 369 / 65 / 58 |
| 1 | 3 | 7 | 15 | **104 ✗** | 144 / 6.1 / 5.6 |
| 2 | 1 | 79 | 15 | **18 ✗** | 168 / 168 / 139 |
| 2 | 2 | 22 | 15 | **36 ✗** | 30 / 3.6 / 3.3 |
| 2 | 3 | 12 | 15 | **46 ✗** | 19 / 1.2 / 1.2 |
| 3 | 1 | 3 | 15 | 2 ✓ | 123 / 123 / 122 |
| 3 | 2 | 165 | 15 | **59 ✗** | 16 / 1.7 / 1.5 |
| 3 | 3 | 155 | 15 | **35 ✗** | 13 / 1.0 / 1.0 |

Spectra plotted (real vs shuffle vs synthetic, log scale, with the p95 threshold marked):
`spectra.png`. Full per-cell spectra in `cells/cells.json`; run log in `cells/run.log`.

## Why it failed — three defects, all in the estimator, none in the corpus

1. **The threshold is a percentile artifact, not a noise floor.** Whenever the shuffle spectrum is
   computed to the 300-value truncation bound, exactly 5% of it — **15 values** — lies above its own
   95th percentile. That is why the shuffle column reads `15` in seven cells: it is arithmetic, not
   measurement. An effective rank defined against that number inherits the artifact.
2. **The arms are not dimension-matched, so the comparison is not like-for-like.** Shuffling
   destroys the very repetition that makes real contexts recur, so the shuffle and synthetic
   matrices are far larger and sparser than the real one — at k=1, L=3 the real arm has 1,441
   distinct pasts against the shuffle's 34,299. A percentile taken from a differently-shaped matrix
   is not a floor for the real one.
3. **The floor is itself data-starved in 7 of 12 cells** (mean count per past < 5 for shuffle and
   synthetic at k=1 L=3, k=2 L=2–3, k=3 L=2–3; down to **1.0**, i.e. every context seen once). A
   conditional matrix whose rows are one-hot has singular values pinned at 1 by construction; its
   spectrum encodes sample size, not process rank.

Together these break the estimator in **both** directions on known ground truth: it under-counts
where the spectrum is short (k=0, L=1: only 3 pasts exist, so the 95th percentile is essentially the
maximum and nothing can exceed it — rank 3 is **structurally unreachable** there), and over-counts
by an order of magnitude where the matrices are sparse (up to 104 against a true 3).

**Ceiling vs null, as required.** No cell reached the 300-value SVD truncation, so no cell is a
ceiling in that sense. The **starvation ceiling is the operative one**: the seven starved cells above
have no headroom for a rank estimate at all. None of the 36 cells is a genuine null — a genuine null
would require a working estimator, and this run does not have one.

## What is NOT claimed

- **This measures the FORMALIZED CORPUS under ONE DECLARED ALPHABET FILTRATION. It is not a
  statement about mathematics. Mathlib is a curated artifact with sociology in it.**
- **No claim about Mathlib's tail dimension, in either direction.** The real column above is
  published as a raw measurement and is **not interpreted**. Rules A, B and C were not reached: the
  harness gates them, and it failed.
- **Not** a claim that Mathlib has no past–future structure along the prerequisite axis, and **not**
  a claim that it has one.
- **Not** a claim that the Hankel-rank approach is wrong — only that *this* effective-rank estimator
  does not recover a rank-3 process from tapes of this sparsity, which is a fact about the estimator.
- **Not linked to the paraconsistent-metric line, which is CLOSED and stays closed.** Not a
  conjecturer probe.
- **No novelty claim** against arXiv:2604.24797 or the computational-mechanics literature
  (Crutchfield–Young causal states, Hankel-rank spectral learning); the machinery is [occupied].
  [proven-negative] for this estimator at this scale.

## Substrate limitations found while building (reported, not smoothed)

- **The k=0 alphabet is 3, not the declared 6.** The faithful dump records `kind ∈ {theorem, def,
  other}` only — `instance`, `structure` and `abbrev` were already folded away at extraction time in
  probe 17's `DumpDeps.lean`. The kind quotient is coarser than the directive specifies. It is not
  *degenerate* (rule D not triggered), but it is not what was asked for either.
- **The k=2 head type constructor is a source-text surrogate**, as pre-registered: the dump carries
  no type expressions. **NA share = 37.9%** of sampled declarations — Lean core constants, anonymous
  instances and auto-generated declarations have no parsed source. Over that 37.9%, k=2 collapses to
  k=1.
- **Hashing was extended beyond k=3.** The directive authorises 2000-bucket hashing at k=3; k=2 also
  exceeded 2000 (11,756 raw) and was hashed on the same rule. **Hashing breaks the nesting of the
  quotient chain** at k=2 and k=3 — the filtration is a chain of quotients only up to k=1.
- The intrinsic grading reproduces probe 17 exactly: 467,680 vertices, 10,463,268 edges, max depth
  **192**, mean 22.3. Mean chain length 15.2; 6,198 of 20,000 rows hit the 24-symbol cap.
- One implementation correction was made **before any spectrum was computed**: the k≥1 namespace root
  is the *module* root (Algebra, Topology, Order, CategoryTheory — 32 of them, as the directive
  enumerates), not the declaration name's first component (which gave 9,927 pseudo-roots).

## Reproduce

```
python probes/19-tail-dimension/tape.py       # -> tape.npz, tape_meta.json
python probes/19-tail-dimension/spectra.py    # -> cells.json, spectra.png
```

scipy 1.17.1, numpy 2.4.6, scikit-learn (randomized_svd, n_iter=7), matplotlib 3.11.1.
Mathlib `8f9d9cff6bd728b17a24e163c9402775d9e6a365` (v4.28.0). Seed **20260729** throughout.

**No follow-up round. No second substrate. No finer filtration.** Registry entry closed with this
verdict.
