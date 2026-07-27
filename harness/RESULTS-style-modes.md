# RESULTS — style-mode decomposition ("do dominant tastes exist in Mathlib, or is it a smear?")

Pre-registered experiment (spec fixed before running; no post-hoc tuning) run on the
FAITHFUL decl graph (`decl_deps.jsonl`, 333,044 decls / 7,523,067 edges, obtained via
Aristotle — see `RESULTS-faithful.md`). Scripts: `style_phase12.py` (metric + Steps A/B),
`style_phase3.py` (discreteness + Step C), `decl_lines.py` + `blame_authors.py`
(authorship). Full log: `style_modes.log`.

**Bottom line: SMEAR.** Mathlib's proof-style space has no dominant discrete "tastes" /
archetypes — it is a continuous cloud. The strong prior is confirmed; the "few
archetypes" shortcut is killed. Two secondary findings below (one of which walks back
part of the earlier faithful-graph H2 headline).

---

## Pre-registered metric (the one under-specified input, pinned before running)

**Birth-simplex loop metric `B(v)`:** introduce nodes into a union-find in increasing
`(depth-from-axioms, name)` order; `B(v) = (#edges to already-introduced neighbors) −
(#distinct components among them)` = the number of independent 1-cycles *born* at `v`
(the rise in first Betti number). `Σ B(v) = b₁ = 7,193,050`. Degree-controlled residue
`loop_residue = rank-residual of B on {rank log-udeg, rank depth}`.

## Phase 1 — the birth-simplex "H1 fix" BACKFIRES (secondary finding)

The birth-simplex swap was meant to be *less* depth-entangled than triangle-count and
rescue H1's clean-dissociation precondition. It does the opposite:

| metric | `rho(L,depth)` | `rho(L,degree)` | H2 degree-controlled |
|--------|:---:|:---:|:---:|
| triangle-count (RESULTS-faithful) | 0.528 | 0.429 | **+0.372 (clears)** |
| **birth-simplex `B`** | **0.715** | **0.805** | **−0.585 (fails)** |

A late high-degree lemma trivially closes many already-connected cycles, so `B ≈ degree`
(`rho=0.805`); degree-controlling it removes almost everything and the residue
*anti*-correlates with significance. **Consequence:** the earlier faithful-graph H2
positive (`+0.372`) is **specific to the triangle metric**, not a general "loop-residue"
property — an important robustness caveat on that headline. The triangle count was, it
turns out, the better-behaved loop coordinate; birth-simplex is worse on both axes.
(`RESULTS-faithful.md` cross-references this.)

## Step A — discrete modes vs smear → **SMEAR**

Node × 6 style features (loop_residue, proof_size, depth, in_deg, out_deg, classical),
standardized.

- **SVD spectrum:** singular values 928 / 688 / 562 / 465 / 302 / 198; variance
  0.43/0.24/0.16/0.11/0.05/0.02. Largest consecutive gap at k=4 but only **1.54×** —
  shallow. An SVD gap measures effective *dimensionality*, not *discreteness*, so this
  alone can't call "modes".
- **Discreteness test (the honest arbiter):** GMM BIC across k=1..10 **decreases
  monotonically to k=10 with no knee** (575k → 176k → 102k → 53k → 11k → −2k → … →
  −48k). That is the signature of a **continuous cloud** being tiled by ever-more
  Gaussians — no natural mode count. (silhouette at k=4 = 0.255 is borderline, but a
  moderate silhouette is expected for any k-means slice of a filled cloud; the no-knee
  BIC is decisive.)

**Step A verdict: SMEAR — taste is continuous, not a few archetypes.**

## Step B — are the (imposed) modes style or subject?

Forcing k=4 (the SVD-gap location) and clustering:

- `NMI(mode; subject) = 0.085` (LOW — the clusters are **not** subject areas ✓)
- `NMI(mode; style)`: out_degree 0.229, proof_size 0.216, depth 0.210, in_degree 0.157,
  **loop_residue 0.154** (the taste coordinate contributes *least*), classical 0.000.

So the weak structure that exists is **style-dominated over subject** — but the "style"
is essentially **proof size / complexity / degree**, and the loop/taste coordinate barely
participates. Since Step A says smear, these "modes" are arbitrary slices of a continuum.

## Step C — do the modes place people? (authorship via `git blame` on mathlib4 v4.28.0)

204,226 / 333,044 decls (61%) attributed to an author; analysed the top-20 prolific
authors (Yaël Dillies, Yury Kudryashov, Joël Riou, …) over 117,251 decls.

- **Author prediction accuracy:** majority 0.139, **subject-only 0.296**,
  **style-only 0.172**. Proof-style predicts *who wrote a lemma* far **worse** than
  *what area it is in*. Style is not a strong personal signature.
- **Mode-mixture stability/separability:** within-author (random split) JS = 0.016,
  between-author JS = 0.146 → **9.4× separable**. Authors *do* have stable, distinct
  mode-mixtures — **but** because style < subject for author prediction, that
  separability is **subject-confounded** (authors specialise in areas; areas have
  characteristic complexity profiles), not an independent personal taste.

**Step C verdict:** author "fingerprints" exist but are largely a proxy for the subjects
people work in; taste is **not** a strong personal signature beyond field.

---

## Pre-registered verdict grid → **SMEAR (taste is continuous)**

| step | pre-registered question | result |
|------|--------------------------|--------|
| A | discrete modes or smear? | **SMEAR** (GMM-BIC no knee to k=10; SVD gap shallow 1.54×) |
| B | modes = style or subject? | not subject (NMI 0.085), weakly style — but style = proof-complexity, loop coord weakest |
| C | tastes personal? | mixtures separable 9.4× **but** style<subject for author id → subject-confounded, not personal |

**Grand verdict:** there is **no map of dominant discrete mathematical tastes** in Mathlib's
proof structure — the style space is a **continuous smear**, the variation that exists is
**proof-complexity**, not a small set of "schools", and it is a **weaker author signal than
subject area**. This is the pre-registered strong-prior outcome (bet on smear), and it
**kills the "few archetypes" shortcut** to question 1. A clean gap (the surprising,
high-value outcome) did **not** appear.

Honest limitations: (1) the loop/taste coordinate was the birth-simplex residue, which
Phase 1 shows is degree-dominated and a weak coordinate — a better-behaved loop metric
(non-backtracking-cycle residue) might carry more taste signal, though Step A's smear is
driven by the whole feature set, not just the loop axis. (2) Step C used random-split
stability; the pre-reg's "later declarations" temporal split (needs commit dates) is a
stronger test left as an extension. (3) `classical` flag (Classical.* in deps) carried no
mode information (NMI 0.000) — too coarse a constructive/classical proxy.
