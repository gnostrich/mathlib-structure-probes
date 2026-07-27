# 02 — Closest-work sweep (occupancy ledger)

## Directly occupies the core idea
- **Kedrick, Yang, Gebhart, Wang, Funk — "Opening Knowledge Gaps Drives Scientific
  Progress"** (arXiv 2509.21899, Sep 2025). Persistent homology on a time-varying
  concept co-occurrence network, 34,363,623 MAG papers. Classifies each new edge:
  no-cycle / novel-pair-no-hole / **gap-opener** (birth simplex creating a 1-D
  class = closes a cycle among previously-unjoined regions = the loop residue).
  Findings: gap-openers ≈0.84% of papers; ~1.58× more likely top-1% cited; more
  disruptive; "sleeping beauties" (short-term citation penalty, large long-term
  gain). Novel pairings that DON'T open gaps show no advantage over baseline.
  => "cross-linking = significance, novelty ≠ significance" is PUBLISHED. [occupied]
  Uses ∂ boundary op, cycles=ker ∂, holes=ker ∂/im ∂, Z2 coeffs. Cite: also
  Zhou 2018 "cycle-based network centrality", Fan 2021 "cycle structure".

## Occupies the Mathlib-graph substrate (and is a NEGATIVE PRIOR)
- **Li, Peng, Severini, Shafto — "The Network Structure of Mathlib"** (arXiv
  2604.24797, Apr 2026). 308,129 declarations, 8.4M edges, 7,563 modules.
  Finding: network centrality captures **language infrastructure, not mathematical
  relevance**; human theorem-vs-lemma importance aligns with structural prominence
  only weakly (~1.47× in-degree). => scoring Mathlib by graph structure is taken;
  and dependency-graph *centrality* is infrastructure-dominated → warns that
  *homology* on the same graph may be too (funext-style plumbing closing masses of
  trivial cycles). This is the prior our test must beat.

## Occupies "interestingness-meter-guided autonomous conjecturer"
- **Fermat — "Learning Interestingness in Automated Mathematical Theory Formation"**
  (NeurIPS 2025 spotlight, arXiv 2511.14778). RL env + evolutionary synthesis of
  interestingness measures to guide exploration. NB: it *learns* the measure =
  precisely the corruptible/fakeable case our incorruptibility argument forbids.
- **Bengio et al. — "ML and information theory concepts towards an AI
  Mathematician"** (arXiv 2403.04571): conjecturing as goal-conditioned search vs
  interestingness reward R(t), GFlowNet proposer.
- **LeanConjecturer** (arXiv 2506.22005): generate + novelty-filter conjectures
  from Mathlib files. **STP** (Dong–Ma, ICML 2025): self-play conjecture+prove.
  **LEGO-Prover**: growing libraries.

## Occupies "autonomous expansion into Mathlib" (proposer side — use, don't rebuild)
- **Aristotle** (Harmonic, arXiv 2510.01346): gold-level IMO; made novel Mathlib
  contributions during training. This is the proposer slot (they have it).
- **MathlibLemma** (arXiv 2602.02561, ICML 2026): LLM generates folklore lemmas,
  proof-bypass screen, curated subset merged into Mathlib.

## Net
Idea occupied. Only the incorruptibility apparatus (non-learned + prospective veto
+ measured floor) is open, and only if the dissociation survives on the decl graph.
