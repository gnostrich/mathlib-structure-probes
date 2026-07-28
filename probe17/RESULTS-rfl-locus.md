# RESULTS — rfl-locus confirmation run (Checks A and B)

Pre-registration: `PREREG-rfl-locus.md`, committed before D or S was computed. Script:
`probe17_rfl_locus.py`; log `p17_run.log`. Mathlib `8f9d9cff6bd728b17a24e163c9402775d9e6a365`
(v4.28.0), toolchain `leanprover/lean4:v4.28.0`. **Route (a)**: real dependency extraction via
`DumpDeps.lean` (`Expr.getUsedConstants` over type **and** body — the analogue of `collectElems`),
two byte-identical extraction runs. One round, terminal.

## The two numbers

| quantity | value |
|---|---|
| **D = AUC(their declaration-level depth → substantive)** | **0.6508** |
| **S = fraction of module-level variance explained by subject** | **0.0770** |

S secondaries: 0.0427 (all 6,676 modules), 0.0733 (size-weighted). Primary population: 2,563
modules with ≥20 classified theorems, 26 subjects, unweighted — fixed in the pre-registration.

## Both classes, separately (directive §5 — never merged)

Over 170,326 classified declarations; join to graph 167,700/170,326 (98.5%).

| class | share | AUC(their depth → class) | S (subject variance explained) |
|---|---|---|---|
| strict `rfl` | 10.76% | **0.3103** | **0.0770** |
| `by simp` | 5.85% | **0.4517** | **0.0712** |
| substantive | 83.39% | **0.6508** (= D) | — |

AUC < 0.5 reads as *shallower than chance*: strict `rfl` sits low in the DAG (0.310, i.e. 0.690 in
the shallow direction), while `by simp` is essentially depth-indifferent (0.452 ≈ 0.548 shallow,
near coin-flip). So the whole of D's excess over 0.5 is carried by strict `rfl`; the automation
class contributes almost nothing. Check B holds for *both* classes independently — 7.7% and 7.1% —
i.e. neither definitional-ness nor `simp`-closability is a restatement of subject matter.

## Harness-validity cell — PASS

- `Mathlib.Logic`+`Mathlib.Init` strict definitional **0.1796** (n=1,604) vs `Mathlib.Analysis`
  **0.0659** (n=20,836) → **PASS**.
- Reconstructed **max depth = 192**; required within an order of magnitude of ~300 → **PASS**.
- Construction corroboration: **467,680 vertices** vs their reported 463,719 (0.85% apart).

## Verdict — **PARTIAL. TERMINAL, CLOSED.**

D = 0.651 is neither ≤ 0.60 (CONFIRMED) nor ≥ 0.75 (DEPTH-REDUCIBLE). S = 0.077 is far below 0.80,
so SUBJECT-REDUCIBLE is decisively excluded. Per the fixed ladder: report both numbers, claim
nothing beyond them. [proven-negative] for the confirmation attempt; the headline claim is **not**
confirmed and **not** refuted.

**What each check actually settled:**

- **Check B passes cleanly and is the informative half.** Subject matter explains **7.7%** of
  module-level variance in definitional fraction. The clustering is *not* a restatement of what a
  file is about; within-subject variation dominates. [proven]
- **Check A is where it fails to clear.** Moving from the coarse module-import proxy (prior
  AUC 0.556) to the paper's declaration-level depth **raised** the association to 0.651 — the
  coordinate is *more* entangled with their depth than the proxy suggested, which is exactly what
  this check existed to catch. It did not reach depth-reducibility, but it did not stay orthogonal.
  For scale: the prior probe's *statement character length* baseline was AUC 0.621, so 0.651 is
  barely above a trivial length proxy. [proven]

## Discrepancies (reported, not smoothed)

1. **Prior probe not reproduced.** My independent source-text classification at v4.28.0 gives
   strict `rfl` **10.76%** over **170,326** declarations; the prior run reported **7.34%** over
   **185,429**. Different commit and/or enumeration. The prior numbers should not be treated as
   replicated by this run.
2. **Max depth 192 vs their ~300.** Within the pre-registered order-of-magnitude band, but
   systematically shallower — expected, since Lean-core constants are depth-0 leaves here rather
   than internal nodes with their own descent to `Sort`.
3. **Zero non-trivial SCCs** found; they report ~60 mutually-dependent pairs (all unsafe recursion).
   Those declarations are absent from this Mathlib-scoped extraction. Immaterial to depth (their own
   collapse moved 463,719 → 463,661).
4. **Unwrapped soft check not reproduced.** Their named largest element,
   `AlgebraicGeometry.Scheme.exists_hom_hom_comp_eq_comp_of_locallyOfFiniteType`, is **present** but
   ranks **6,067 of 333,044** (top 1.8%) on our measure — consistent with pre-registered deviation 1
   (multiplicity-blind edge weights), and pre-declared **soft**, so not VOID-bearing. It is *not* a
   reproduction of their ranking.
5. **Elaborated-term cross-check is weak.** Source-classified strict-`rfl` theorems have median
   proof-side `value_deps` 12 vs 29 for substantive — the right direction, only ~2.4×. `rfl` at a
   typeclass-laden goal legitimately drags in instance machinery, so this neither confirms nor
   impugns the classification sharply.

## What is NOT claimed

- **Not claimed: that the rfl-locus is a native coordinate.** The verdict is PARTIAL. D = 0.651
  leaves a real association with their depth unaccounted for.
- **Not claimed: replication of the prior source-text probe.** Its headline fractions did not
  reproduce here (item 1).
- **Not claimed: elaborated-term classification.** Classification is **source text**, so `rfl`
  behind wrappers (`simp` closing a definitional goal, `decide`, unfolding tactics) is missed;
  10.76% is a **floor**, and the true definitional locus is larger by an unknown amount. Route (a)
  was used for the *graph*, not for proof classification.
- **Not claimed: replication of the paper's depth or unwrapped statistics.** Ours is shallower and
  multiplicity-blind by declared deviation.
- **Not claimed: any importance, quality or interestingness signal.** Definitional-vs-substantive is
  a statement about how a proof is discharged, not about what is worth proving.
- **Not claimed: a conjecturer, a generator, or any instrument validated for downstream use.** Even
  a CONFIRMED verdict would only have established a measurement.
- **No novelty claim against arXiv:2603.20396.** They measured wrapped/unwrapped length and depth and
  explicitly discarded the proof-automation signal as an artifact; this run treats it as an object
  but does not establish that it is a distinct coordinate. [occupied] for the depth machinery.

## Reproduce

```
python probe17/probe17_rfl_locus.py     # expects faithful/decl_deps.jsonl + mathlib4 @ 8f9d9cff
python probe17/probe17_perclass.py      # per-class AUCs and per-class S (log: p17_perclass.log)
```

Logs: `p17_run.log`, `p17_perclass.log`; machine-readable summary `p17_report.json`.
