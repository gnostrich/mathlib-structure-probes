# PRE-REGISTRATION — cell 5: intrinsic atomicity self-selection (real Schur gate on the graph)

STATUS: pre-registered. Observable, bridge, controls, locked line fixed BELOW before results.
This is a BUILD + one measurement, scoped minimal. If the graph→Gram bridge can't be built
faithfully at bounded cost, the honest output is "the object cannot currently be run on the graph"
— report and stop. No importance claims (worth stays exogenous/absent, per the scissors result).

Ground truth confirmed: (a) the REAL `expand`/`schur` Lean source is present and understood —
`schur A b d = d − bᵀ A⁻¹ b`, `expand` admits a site iff `schur > 0` (R_A1/R_A2/R_A3_A4.lean);
(b) faithful dependency graph (333,044 / 7,523,067) available; (c) no cell-5 site-selector exists
(C3Gibbs is the entropy/Gibbs equilibrium core; self-selection is unbuilt, candidate-original).

## Why the self-selected ORDER cannot be the observable (stated, then avoided)

A produced total order is a node-scalar potential → its curl is identically 0 (same tautology as
the deviation gate). So "curl of the self-selected order vs actual" is a forced zero and carries no
information. The operator-valued structure the scalar proxies (depth, mean-gen) provably discarded
lives in the object's **context-dependent Schur PREFERENCE FIELD**, which is genuinely non-integrable.

## The bridge (graph → Gram data the real gate consumes)

Incidence kernel: `φ(v) = {v} ∪ direct-dependencies(v)`; `K(u,v) = |φ(u) ∩ φ(v)|`. This is a genuine
PSD Gram matrix (`K = A Aᵀ` for the closed-out-adjacency incidence `A`), with `K(v,v) = outdeg(v)+1 > 0`
for every node. This is "the Gram/incidence data the expand gate consumes," built faithfully and at
bounded cost. FAITHFULNESS CAVEATS (reported prominently with the verdict): the SCHUR GATE is the
REAL formula (`d − bᵀA⁻¹b`, no reimplemented proxy); the KERNEL is a graph-incidence kernel (not the
object's analytic V5_1 kernel); the primary measurement uses the pairwise (1×1) Schur context. So the
verdict is more trustworthy than the mean-gen scalar proxy (real operator-valued gate on real PSD
Gram data), but a crude-bridge result stays provisional either way.

## Observable — curl of the real Schur preference field

For each dependency edge `u→v`, the object's pairwise atomicity preference (real Schur complement of
adding one node to the 1×1 state of the other):
```
schur_add(x | a) = K(x,x) − K(a,x)² / K(a,a)          (= d − bᵀA⁻¹b at 1×1 context, exact)
s(u→v) = schur_add(u | v) − schur_add(v | u)          (antisymmetric edge field)
       = [K(u,u) − K(v,v)]  +  K(u,v)²·(1/K(u,u) − 1/K(v,v))
```
The first bracket is a node potential (gradient, zero curl); the second term is edge-specific
(operator-valued, non-integrable). Hodge-decompose `s`: `curl_fraction(s) = ||s − grad φ*||² / ||s||²`
= the antisymmetric self-selection content after quotienting the forced gradient (topology). Compare
to the scalar-proxy baseline `curl_fraction = 0.076` (mean-generation order, prior result).

Confirmation run (faithfulness): also run the REAL `singleton → expand(argmax schur) → …` on a few
BOUNDED regions (N≈150) with this kernel, to demonstrate the real gate runs on the bridge and produce
a genuine self-selected order; report its full-context preference behaviour as a cross-check.

## Controls (both binding)
1. Topology quotient — the Hodge gradient part IS the forced order; `curl_fraction(s)` is the residual.
2. Module conditioning — recompute on intra-module edges only; the circulation must survive.
Plus: tautology check (pure-potential flow → curl ≈ 0) and reproducibility (edge-reorder).

## Pre-registered reads (LOCKED; prior is a headwind — substrate is ~92% gradient, DEAD expected)

- **ALIVE:** `curl_fraction(s) ≥ 0.20` AND survives module conditioning (intra ≥ 0.5× global) AND
  reproducible → the operator-valued gate self-selects structure the scalar order discarded; cell 5 is
  real; program reopens on solid ground. (Trustworthy given the real gate — modulo the kernel caveat.)
- **DEAD:** `curl_fraction(s) ≤ ~0.10` (proxy-level) → the atomicity gate self-selects a near-gradient
  order too; cell 5 closed on the real object — a clean, non-provisional kill (the epitaph stands),
  provided the bridge is assessed faithful.
- **AMBIGUOUS:** between 0.10 and 0.20 → report, do not advance.

## Rails
- Real Schur gate, not a reimplemented proxy. Report the faithfulness assessment prominently.
- Single build, single measurement, pre-committed line. No tuning the selector until it produces curl.
- The selector is the proposer, NOT a significance judge — no importance claims attach.
- Scope kill-switch: if the bridge can't be built faithfully at bounded cost, report that and stop
  rather than testing a crude bridge (an unfaithful bridge makes ALIVE and DEAD both meaningless).
