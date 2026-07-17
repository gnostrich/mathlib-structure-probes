# PRE-REGISTRATION — tension gate: does cheap local Hodge tension predict forced-vs-open beyond degree?

STATUS: pre-registered. Metric, radii, labels, controls, and locked lines fixed BELOW before
results. Correlation measurement ONLY — no sampler, no EBM, no generator, no Aristotle. The gate
decides whether the tension-EBM sampler is worth building. **Stated prior: DEGREE-collapse is the
likeliest outcome** ("local coboundary pull" is honestly close to "dense neighborhood," and
density-as-signal is already dead: reuse AUC 0.52). A clean DEATH is the expected, valuable outcome.

Ground truth confirmed: (a) faithful decl graph (333,044 / 7,523,067) available; (b) proof-term-size
proxy (#value_deps per decl) in the graph, `@[simp]` flags harvested (46,327/213,929 = 21.7%);
(c) no tension metric exists in the repo.

## The metric T_r(v) — cheap, local, statement-side only (fixed)

- **Seeds** `S(v)` = v's **type_deps** (the statement's referenced objects), v itself EXCLUDED.
  **T never sees value_deps (the proof).** This is the structural no-leakage / not-the-prover
  guarantee at the input level; the radius sweep tests it at the scale level.
- **Neighborhood** `N_0 = S(v)`; `N_{k+1} = N_k ∪ out-neighbors(N_k)` (dependency direction only —
  bounded by out-degree, avg ~29; no in-hub blowup). Induced dependency edges among members.
- **Tension** `T_r(v) = b1 / E = (E − N + C) / E` of the induced local complex (first-Betti /
  cycle-space fraction = the harmonic-residue share; `1 − T` = the spanning-forest/coboundary share).
  `E = 0 → T = 0` (reported). This is a rank computation on a bounded neighborhood — the "cheap" claim.
- **Radii**: r = 0, 1 (full sample; SMALL radius = r ≤ 1), r = 2 (subsample, sweep point).
- **Sample**: theorems (`kind=theorem`) with simp-label coverage; random **40,000** (seed 20260717)
  for r=0,1; random 10,000 of those for r=2. No other sampling.

## Labels (proxies — stated)

- **Y_a (primary, continuous)**: proof complexity = `log1p(#value_deps)` (proof-term-size proxy).
  High = open/hard; low = forced/chore.
- **Y_b (confirmation, binary)**: `@[simp]` flag = forced (simp lemmas are the mechanical
  consequences). Signal must appear on BOTH with **consistent signs** (T's correlation with Y_a must
  be opposite in sign to its association with simp) or it is not trusted.
- Caveat: both are proxies; FLAT is provisional on label faithfulness; ALIVE requires both.

## Controls (the load-bearing part)

Degree partial = partial Spearman of T vs Y after rank-regression on ALL of:
`log1p(indeg(v))`, `log1p(outdeg(v))`, `log1p(N_r)`, `log1p(E_r)` (v's own connectivity AND the
neighborhood size/density that T could smuggle in). Reported at EVERY radius — the deliverable is the
**joint table: radius × {raw signal, degree-residual}**, not two separate numbers.

## Locked reads (numbers fixed now)

- **Signal** (necessary, not sufficient): `max(AUC, 1−AUC)(T vs Y_b) ≥ 0.65` AND `|Spearman(T, Y_a)| ≥ 0.15`.
- **ALIVE**: signal present AND **degree-residual `|partial| ≥ 0.10` on BOTH Y_a and Y_b at r ≤ 1**,
  signs consistent → tension is real, cheap, not-degree, not-prover → build the EBM sampler next session.
- **DEGREE**: raw signal present but degree-residual `< 0.10` at every radius → reuse in a hat → DEAD.
- **PROVER**: passes signal+residual only at r = 2 (not at r ≤ 1) → prover in a hat → DEAD.
- **FLAT**: `max(AUC,1−AUC) < 0.55` and `|Spearman| < 0.05` on both labels at all radii → DEAD
  (provisional on labels).
- **Anything mixed** (e.g. one label passes, the other fails; or signs inconsistent) → AMBIGUOUS,
  report, do NOT build.

## Rails
- Measurement only; no sampler/EBM/generator/prover. One metric, no tuning T until it predicts (hatch).
- The degree partial is the decisive number; raw correlation is context.
- Boundedness is the "not the prover" claim: if T needs r=2 to predict, that is PROVER — no
  widen-and-declare-victory.
- A false ALIVE hides in trading radius against degree: ALIVE requires small-radius AND
  survives-degree **jointly**, read off the same row of the table.
