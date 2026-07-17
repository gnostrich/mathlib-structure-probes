# RESULTS — Phase 0: degree-normalized loop metric (judge robustness)

Pre-registration: `PREREG-conjecturer.md` (committed before this ran). Faithful graph
(333,044 decls / 7,523,067 edges). Script: `phase0_normloop.py`; log:
`phase0_normloop.log`. Thresholds fixed in the pre-reg; reporting whatever came out.

## Metric sweep (the honest table)

For each candidate loop coordinate: its correlation with degree (design goal: LOW, so it
is genuinely degree-normalized, not a degree proxy), H1 dissociation vs depth, and the
degree-controlled H2 payoff against the citation proxy Y2 (= log in-degree) and the
degree-independent label proxy Y1 (theorem=1/lemma=0).

| loop metric | `rho(·,degree)` | H1 `rho(·,depth)` | H2 vs Y2 (citation) \|depth+deg | H2 vs Y1 (label) \|depth+deg |
|-------------|:---:|:---:|:---:|:---:|
| raw triangles `T` | +0.949 | 0.528 | +0.372 | −0.31 |
| birth-simplex `B` (prior) | +0.805 | 0.715 | −0.585 | — |
| Lnorm = (T−E)/√(E+1) (z-score) | **−0.650** | −0.588 | +0.435 | −0.311 |
| clustering coeff | −0.603 | — | +0.352 | — |
| **ratio `T/E` (config-model)** | **−0.315** | **−0.341** | **+0.501** | −0.274 |

`E` = configuration-model expected triangles at the node (degree-preserving null).
**Metric chosen by an outcome-independent rule** (closest `rho(·,degree)` to 0, i.e. most
genuinely degree-normalized — NOT by H2), which is `ratio = T/E`. The pre-reg's primary
`Lnorm` z-score **over-corrected** (pushed to −0.65 — a known artifact of z-scoring
heavy-tailed counts); the ratio is the valid degree-normalized coordinate.

## What the winning (degree-normalized) metric shows — a real advance

With `ratio = T/E` (degree-decoupled, `rho(·,degree) = −0.315`, |·| < 0.40):

- **H1 dissociation CLEARS:** `rho(ratio, depth) = −0.341` (≤ 0.40), both off-diagonal
  terciles populated (50,850 / 63,153). This is the **first loop metric all session to
  clear H1** — raw triangles were borderline-fail (0.528) and birth-simplex worse (0.715).
  The degree-normalization fixes exactly the entanglement that made the faithful-graph
  verdict "AMBIGUOUS".
- **H2 payoff CLEARS and strengthens:** degree-controlled partial `rho(ratio, Y2 | depth,
  deg) = +0.501` (vs raw triangles' +0.372). And it is **robust across every real loop
  metric** (+0.35 … +0.50); the only metric that failed H2 was birth-simplex, precisely
  because `B ≈ degree` (so degree-controlling annihilates it) — that was a bad loop
  coordinate, not evidence against the signal.
- **H3(a) forward foil PASS:** 0/2000 distant `A∧B` conjunctions get any loop credit.

So the earlier worry ("the +0.372 is a raw-count / degree artifact, and it's metric-fragile
because birth-simplex killed it") is **resolved**: a principled degree-normalized metric
both **decouples from degree** and **clears H1 + H2** on the citation proxy. The judge's
signal is real and not an artifact of raw counts or degree.

## The honest caveat (the one thing that does NOT clear)

Against the **degree-independent** significance proxy Y1 (the theorem/lemma label), every
metric is **negative** (ratio: −0.274). So the loop-residue predicts **downstream reuse
(citation / in-degree)**, but it does **not** track the human theorem-vs-lemma naming — in
fact loop-heavy decls skew toward `lemma`. Whether "reuse-significance" is the significance
we care about is an interpretive question; the theorem/lemma label is a weak, stylistic
proxy, but it is the only degree-independent significance signal available in the graph, and
it comes back the wrong sign.

## Verdict against the pre-registration

- Pre-registered **PASS** wanted: degree-controlled H2 ≳ 0.3, correct sign, **and not
  dependent solely on a degree-linked Y** (some signal vs a degree-independent Y).
- Delivered: **H1 + H2 clear cleanly on the citation proxy with a degree-decoupled metric**
  (the strongest, cleanest judge result of the session) — but the **degree-independent Y arm
  fails** (Y1 = −0.27, wrong sign).

**Read (pre-Phase-0b):** the judge is validated as an **incorruptible predictor of
downstream reuse**, robust to metric choice and to degree control, and now clearing the
dissociation precondition it previously missed. It is **not** validated as a predictor of a
degree-independent notion of "importance." Phase 0b (below) settles that arm.

## Phase 0b — better degree-independent significance proxies (pre-registered in PREREG-conjecturer.md)

Two stronger degree-free proxies, fixed before computing (log: `phase0b.log`; scripts
`simp_flags.py`, `phase0b_analysis.py`):
- **Y3 = `@[simp]` flag** (parsed from mathlib4 v4.28.0 source). Genuinely degree-free:
  `rho(Y3, in-degree) = −0.084`.
- **Y4 = cross-subject downstream breadth** (# distinct subjects among dependents). Turned
  out **degree-LINKED**: `rho(Y4, in-degree) = +0.912` — it is essentially in-degree, so it
  is NOT a valid degree-independent proxy (a pre-registration mis-step, reported honestly).

Result — degree-controlled partial `rho(ratio, Y | depth, in-degree)` (each Y controlled for
its OWN degree confound, in-degree):

| proxy | degree-linkage `\|rho(Y,indeg)\|` | valid degree-indep? | partial `rho(ratio, Y)` |
|-------|:---:|:---:|:---:|
| Y3 `@[simp]` | 0.084 | yes | **−0.015** (null) |
| Y1 theorem/lemma label | 0.358 | yes | **−0.121** (negative) |
| Y4 cross-subject breadth | 0.912 | **no (≈in-degree)** | −0.091 (residual) |
| Y2 citation (reference) | — | no (IS in-degree) | +0.005 (near-circular floor) |

**Every genuinely degree-independent significance proxy is null or negative.** The apparent
"+0.411" for Y4 under an *undirected*-degree control is an artifact: Y4 is degree-linked, and
under its correct (in-degree) control it is −0.091. So the loop-residue predicts **reuse
volume / citation** (which is degree-flavored) but predicts **no degree-free notion of
significance** we can measure.

## FINAL verdict (Phase 0 + 0b) — qualified NEGATIVE for the significance claim

- **What holds (robustly):** with a principled degree-normalized metric (`ratio = T/E`,
  degree-decoupled at −0.315), the loop judge **clears H1** (dissociation −0.341, first
  metric this session to do so) and **H2 vs citation** (+0.501), and foils are not credited.
  The "loop-residue predicts downstream reuse beyond degree" claim is **real and not an
  artifact** of raw counts or degree.
- **What fails:** the judge does **not** predict any genuinely degree-independent
  significance (`@[simp]` −0.02, label −0.12, breadth-residual −0.09). The "significance" it
  captures is **reuse-volume ≈ connectivity**, not a degree-free notion of mathematical
  importance.

Per the pre-registered verdict grid, the degree-independent arm being ~0/negative on both
strengthened proxies is a **qualified NEGATIVE**: *the judge tracks reuse-volume only → do
NOT build the conjecturer as a "significance" conjecturer on this coordinate.* The reuse/H1
findings stand as a genuine, publishable result about the loop coordinate; the strong
"incorruptible significance judge" claim is not supported. (Caveat both ways: no strong
degree-free *importance* proxy exists in this data — `@[simp]`/label are utility/stylistic
markers — so this refutes the strong claim without positively measuring "importance".)
