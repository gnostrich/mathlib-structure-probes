# RESULTS — tension gate: cheap local Hodge tension vs forced-vs-open

Pre-registration: `PREREG-tension-gate.md` (committed before results; lines locked; stated prior =
DEGREE-collapse). Correlation measurement only — no sampler/EBM/prover. Script: `tension_gate.py`;
log: `tension_gate.log`. Sample: 40,000 theorems (r=0,1) / 10,000 (r=2, node-cap 5,000 — 0 hit the
cap) from the 165,905 labeled-theorem population, seed fixed.

## Metric, as pre-registered

`T_r(v) = b1/E` (harmonic-residue fraction) of the induced local complex grown from the
**statement's** `type_deps` by bounded out-expansion. T never sees `value_deps` — structurally
cannot read the proof it predicts. Neighborhoods stayed genuinely local (median N = 11 / 35 / 65
at r = 0/1/2).

## The joint table (radius × raw signal × degree-residual) — the deliverable

| r | AUC(T, simp) | rho(T, Y_a) raw | **resid(Y_a) after degree** | **resid(simp) after degree** |
|:-:|:---:|:---:|:---:|:---:|
| 0 | 0.552 | +0.291 | **−0.015** | +0.008 |
| 1 | 0.517 | +0.468 | **−0.039** | −0.020 |
| 2 | 0.503 | +0.489 | **−0.036** | −0.014 |

(Signal line: AUC ≥ 0.65 AND |rho| ≥ 0.15. Decisive line: residual ≥ 0.10 on both labels at r ≤ 1.)

## Verdict

**By the locked ladder: AMBIGUOUS (mixed) → do not build.** The mixed pattern is precisely:

1. **Y_a (proof complexity): the stated-prior DEGREE-collapse, textbook form.** Raw correlation is
   substantial and grows with radius (+0.29 → +0.47 → +0.49, the direction the idea predicted) —
   and the degree partial annihilates it at every radius (−0.015 / −0.039 / −0.036, even flipping
   sign). "Local tension" was neighborhood density in a hat. The raw signal never cleared the
   locked AUC arm, which is why the ladder routes to AMBIGUOUS rather than the formal DEGREE label,
   but the collapse pattern is exactly the pre-registered DEGREE failure mode.
2. **Y_b (@[simp], the confirmation label): FLAT.** AUC 0.552/0.517/0.503 ≈ chance at every radius.
   The confirmation label never showed signal even before controls.

Every component is a death; no label shows degree-independent signal at any radius; residuals are
≤ 0.04 everywhere against a 0.10 line. There is no radius-vs-degree trade to exploit — the joint
table is uniformly null after the partial.

**One-line call: do NOT build the tension-EBM sampler.**

## Caveats (both directions, per prereg)

- Labels are proxies: the FLAT on `@[simp]` and the overall null are provisional on label
  faithfulness. But the primary label's raw correlation was strong — the labels are not inert; the
  signal they carry is simply degree.
- No tuning was performed on T (single pre-registered definition, single run) — the hatch stayed shut.

## Place in the arc

This is the **sixth** independent confirmation of the arc's unifying finding: Mathlib's dependency
structure carries no cheap structural signal beyond the gradient/degree part — depth survived
(AUC 0.81); loops/reuse, order-holonomy, cell-5 atomicity self-selection, compression-beyond-depth,
and now local Hodge tension all collapse to degree or gradient. The tension-EBM thread closes at
measurement cost, before a sampler was built — which is what the gate was for.
