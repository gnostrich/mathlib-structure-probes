# mathlib-structure-probes

**Pre-registered measurement gates on Mathlib's proof-dependency structure — one robust positive,
a stack of clean negatives, and a reusable deterministic Lean-variant measurement harness.
No usable end product was built; that is a finding, not an apology.**

## What this repo is

A sequence of experiments on the faithful declaration-level dependency graph of Mathlib
(333,044 declarations / 7,523,067 kernel edges, extracted with the real elaborator) and on
Lean-checked theorem variants, run under a fixed discipline:

- **pre-registration committed before results** (metrics, controls, verdict lines locked in advance);
- **degree/confound controls as the decisive numbers**, never raw correlations;
- **deterministic fidelity**: independent double runs, must-fail canaries, budget-sensitivity checks;
- **negatives honored at full weight** — no post-hoc reinterpretation to keep ideas alive.

## What survived (the standing results)

1. **Human importance ≈ foundational depth.** Longest-prerequisite-chain depth separates the
   famous theorems (exact-matched 100/1000-theorem lists, an anchor *outside* the graph) at
   **AUC 0.81**; reuse/in-degree sits at **0.52 ≈ chance**. Importance is *not* popularity, and it
   has exactly one cheap structural correlate we could find. (`RESULTS-compression-importance.md`)
2. **De-gamed compression adds nothing beyond depth** (0.569 vs a locked 0.58 line) — and the
   gameable part of raw compression was identified and removed by construction. (`RESULTS-compression-mdl.md`)
3. **Methods:** rank-correlation is mechanically inert under extreme class imbalance (a *perfect*
   ranker scores ρ≈0.04 at 0.056% prevalence) — use AUC + permutation. Proven, transferable.
4. **A working instrument** (see below) for turning "loosen/perturb a theorem, see what still
   elaborates" into deterministic, canary-guarded, kernel-checked data.

## What was tested and killed (each at pre-committed lines)

| probe | verdict | doc |
|---|---|---|
| loop-residue as significance signal | = reuse volume; collapses under degree control on approx graphs; triangle-only positive on faithful graph, not metric-robust | `RESULTS-faithful.md`, `RESULTS-phase0-normloop.md` |
| discrete "style/taste" modes | continuous smear; author style < subject | `RESULTS-style-modes.md` |
| order-holonomy / circulation in accumulation order | ~92% pure gradient (curl ≤ 0.076) | `RESULTS-holonomy-gate.md` |
| real Schur-gate atomicity self-selection (cell 5) | selects an even purer gradient (curl 0.0009) | `RESULTS-cell5.md` |
| local Hodge tension → forced-vs-open | degree in a hat / flat | `RESULTS-tension-gate.md` |
| type-theoretic (infra) loosening axis | flat — 4 breaks in 216 cells; math axis richly structured | `RESULTS-loosening-lattice.md` |
| stuck-proof shape → missing constraint (compass) | BLIND — the removed premise is textually absent from the residue | `RESULTS-v3-walk.md` |

Aggregate reading: **Mathlib's proof structure is a near-pure hierarchy whose one legible
human-meaningful coordinate is depth.** Every antisymmetric / stylistic / guidance signal we
probed either reduced to degree/gradient or wasn't there.

## The reusable instrument

`harness/` contains a pipeline that (a) generates kernel-checkable variants of real Mathlib
theorems (hypothesis drops, class-ladder weakenings, instance perturbations) with sorry-twin
statement adjudication and must-fail canaries; (b) runs them through the **actual Lean elaborator**
at fixed heartbeat budgets using a remote built-Mathlib environment as a dumb deterministic
runner; (c) parses per-declaration outcomes with line-level attribution. Measured fidelity across
independent runs: **0 mismatches in ~900 cells; 0.000 budget flip-rate.** Also here: the faithful
kernel-edge graph extractor (`DumpDeps.lean` + retrieval scripts).

## Map

- `harness/` — all preregs (`PREREG-*.md`), results (`RESULTS-*.md`), scripts, logs, manifests.
- `output-final_aristotle/` — the certified-positivity Lean artifact (external prover output) used
  as the program-native substrate.
- `docs/` — the original loop-veto kit framing (including `README-original-kit.md`) and provenance.
- `archive/` — the unrelated earlier Structure-First Backpropagation project (pre-rename history).

Large artifacts (the 395 MB faithful graph, Mathlib clone, olean caches) are kept out of the repo;
every one is regenerable from committed scripts.
