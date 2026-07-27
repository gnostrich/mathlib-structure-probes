# 03 — Pre-registration: the decisive decl-level test

STATUS: pre-registered. Fix all metrics + thresholds BEFORE running. Do not move
goalposts. (Note: in the chat session that produced this kit, the R^2 threshold
DIRECTION was first stated backwards and corrected; the corrected direction is
below and is definitional — R^2 = variance-of-loop-explained-by-slide, so HIGH
R^2 = collapse, LOW R^2 = orthogonal.)

## Substrate
The declaration-level dependency graph of Mathlib WITH proof-synthesized edges
(the edges Li–Peng–Severini–Shafto found dominant; ~92% indirect). Obtain via
DumpDeps.lean in a built env, or LeanDojo trace. The source-parse fallback
(decl_dep_extract.py) is APPROX (statement references only) and gives weaker
evidence — a null there is confounded by missing proof edges.

## Metrics (per declaration)
- slide S: {proof-term size, depth-from-axioms (longest chain), in-degree (times
  used by later decls)}. Combined via first PC or reported separately.
- loop L: birth-simplex indicator at introduction (Kedrick-style: does this decl's
  new edge(s) create a 1-cycle in the concept/decl complex) AND cycle-participation
  (count in a cycle basis / non-backtracking cycle membership) on the decl graph.
- significance Y (ground-truth proxies, report each):
  Y1 human label theorem(1)/lemma(0);
  Y2 in-library in-degree (times later Mathlib cites it) — log;
  Y3 optional external: named result / @[simp] / high downstream fan-out.

## Hypotheses
- H1 (precondition — dissociation): L is rank-independent of S; both off-diagonal
  terciles populated (high-S/low-L and low-S/high-L non-empty).
- H2 (PAYOFF — significance beyond novelty): L predicts Y controlling for S. I.e.
  partial Spearman rho(L, Y | S) is positive and non-trivial, AND in a logistic/
  Poisson fit Y ~ S + L, the L coefficient is significant with the sign that
  high-loop => higher significance. (This is the Kedrick claim, ported to Mathlib.)
- H3 (incorruptibility):
  (a) gaming foil — inject trivial cross-region conjunctions (A ∧ B for distant
      A,B). The loop meter must NOT credit them (Schur–MASA fake-success trap).
  (b) warm/cold floor — for a sample, recompute L after minimal independent
      reproof (cold) vs reusing the original lemma path (warm). Only the cold-
      surviving residue L_cold gets veto authority; L_warm − L_cold = path debt.

## Pre-registered reads (CORRECTED directions)
Let rho = Spearman(L, S) (primary), R2 = variance of L explained by S.
- WALL (kill on this substrate): |rho| >= 0.7 OR R2 >= 0.75  (L ≈ S)  OR  H2 fails
  (partial rho(L,Y|S) not significantly > 0).
- GO: |rho| <= 0.4 AND R2 <= 0.5 AND both cells populated (H1) AND H2 clears
  (L coeff significant, correct sign) AND H3(a) holds (foils not credited).
- AMBIGUOUS: otherwise → report, do not proceed to wiring.

## What a GO buys / does not buy
GO = the incorruptible loop-residue veto carries significance information beyond
slide on Mathlib's real proof-dependency structure, and is not trivially gamed.
It does NOT prove RH-anything and does NOT make the proposer autonomous — the
contribution is the curation veto, tagged [candidate-original — discipline].
