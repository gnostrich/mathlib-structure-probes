# RESULTS — Probe 16: term-space failure anisotropy

Pre-registration: `PREREG-term-anisotropy.md`, committed before the run. Sweep: `SWEEP.md`.
Mathlib `8f9d9cff6bd728b17a24e163c9402775d9e6a365` (v4.28.0), toolchain `leanprover/lean4:v4.28.0`,
modules `Mathlib/Algebra/Group/Basic.lean` + `Mathlib/Order/Basic.lean`, budget 400 000 heartbeats.
275 generated files, 880 logs, one round. Script `probe16.py`, analysis `probe16_analyze.py`,
raw analysis log `p16_analysis.log`.

## Matrix (corpus, normalized survival R = S/cap_eff; R=0 means it broke at depth 1)

| direction | measurable cells | mean R | R=0 | R=1 | coverage of corpus |
|---|---:|---:|---:|---:|---:|
| D1 delete a hypothesis | 87 | 0.017 | 98% | 1% | 55% ✔ enters statistic |
| D2 weaken a typeclass | 107 | 0.075 | 93% | 7% | 67% ✔ enters statistic |
| D3 generalise a universe | 0 | — | — | — | **0%** |
| D4 generalise an instance | 9 | 0.000 | 100% | 0% | 6% |
| D5 generalise a bound var's type | 0 | — | — | — | **0%** |
| D6 drop finiteness | 2 | 0.500 | 50% | 50% | 1% |

Instrument checks: **canary failures 0/275**; unperturbed-baseline failures 4 (those theorems
excluded); **duplicate-shard fidelity 0 disagreements in 230 cells (0.00%)**.
BREAK error classes: 140 unclassified, 70 `lean.unknownIdentifier`, 36 `lean.synthInstanceFailed`.

**Harness-validity cell PASSES decisively:** decorative-structure trivialities mean R = **1.000**
(n=30) vs the 30 most hypothesis-laden corpus theorems mean R = **0.133**; Mann–Whitney
**p = 1.25 × 10⁻¹²** (required p < 0.01). The instrument is *not* blind — it separates decorative
from load-bearing structure perfectly.

**Anisotropy statistic:** V_T = 0.0430, V_D = 0.0008, **A_obs = 52.0**, **A_shuffled = 48.3**,
**ratio = 1.08×** (PASS required ≥ 3×).

## Verdict

**CEILING (not a null).** 94.6% of measurable cells fail at depth 1; 95.1% ever fail. Both
pre-registered ceiling triggers fire. Depths were **not** re-tuned to escape it, per the rules.

Independently, the anisotropy test would also not have passed: A_obs is large in absolute terms only
because V_D ≈ 0 — both live directions sit at almost the same near-zero mean survival — and the
permutation control exposes this, landing the ratio at 1.08× against a required 3×. So no PASS is
available by either route. Terminal, CLOSED. [proven-negative]

## What is NOT claimed

- **No anisotropy claim, in either direction.** The measurement had no headroom; this is *not*
  evidence that the failure field is isotropic, and *not* a NULL. [proven-negative] applies to
  "Probe 16 as specified could not measure anisotropy here", nothing more.
- **No claim about Mathlib mathematics.** These are artificially opened goals with kernel-checked
  ground truth, not statements about what is true.
- **No instrument was validated for downstream use**, and certainly no conjecturer. A PASS would
  only ever have yielded a rigidity-measuring instrument (directive §7); no PASS occurred.
- **No novelty is claimed for the machinery** — the sweep records mCoq, the typeclass/instance
  literature and Gandhi (ITP 2025) as owning the components; only the question was unclaimed, and
  the question went unanswered. [occupied] machinery, [candidate-original] question, unresolved.

## Honest reading (what the ceiling itself shows)

Two facts are worth recording because they were measured, not assumed:

1. **Mathlib's core algebraic and order theorems are maximally tight along the axes that exist.**
   98% of hypothesis deletions and 93% of single-step class weakenings break the proof immediately;
   only 11 of 159 theorems tolerate *any* perturbation at all. Combined with the harness cell —
   where deliberately decorative structure survives everything (R = 1.000) — the instrument
   demonstrably can see slack, and there is almost none to see. [proven]
2. **Four of the six directives' six directions barely exist on this substrate.** D3 and D5 yielded
   *zero* measurable cells and D4/D6 nine and two; Mathlib's core is already universe-polymorphic
   and carries almost no finiteness assumptions. The "6-tuple, multi-component by construction"
   is, here, a 2-tuple — and only 41 of 159 theorems had both live components. This is a property of
   the substrate, reported rather than repaired: choosing different modules to manufacture coverage
   would have been substrate-shopping. [proven]

The prior fifteen probes found the dependency graph admits essentially one invariant. Probe 16 does
not overturn that, and does not get the chance to: on this substrate the term-space deformation axes
are either absent or immediately fatal.

## Reproduce

```
python probe16/probe16.py <mathlib-v4.28.0> <outdir> p16_manifest.json   # generate variants
# elaborate each file: lake env lean -DmaxHeartbeats=400000 <file>
python probe16/probe16_analyze.py                                        # verdict
```
