# 05 — How the loop-veto connects to the certified generator

The generator (GramState/expand) is currently **semi-intrinsic**: intrinsic form +
intrinsic admissibility gate (PD via inertia meter), but externally-supplied
temperature and **expansion points**. The unswept piece is "cell 5":
self-selecting expansion points via an atomicity/significance criterion.

The loop-residue veto IS a candidate for cell 5. Mapping:
- expand(GramState, p): today `p` (the next expansion point / basis element) is
  handed in. The loop meter proposes *which* frontier cell to clamp next = which
  candidate theorem is worth admitting.
- inertia meter (isPDq_iff_nMinus_nZero) = the VALIDITY certifier (n- = 0). It is
  outside the objective and incorruptible — the design pattern the loop veto must
  copy. The loop veto is the SIGNIFICANCE certifier, likewise outside the objective.
- honest halt (haltWitness) = certified negative. The loop veto's analogue: a
  candidate with zero cold-floor loop residue is admitted for validity but denied
  structural authority (it's "the tape" — valid, inert, no anchor spawn). This is
  the I-8 no-self-ingestion rule made rigorous: only cold-surviving loop residue
  earns the right to expand world structure.

Wiring (only after H2 clears in doc 03):
1. proposer (Aristotle) emits proven candidate C with kernel certificate.
2. slide S(C) computed — diagnostic, logged, no authority.
3. loop L_cold(C) computed via the floored meter — if below pre-registered floor,
   admit-without-authority; else admit-as-anchor (may extend the frontier).
4. never feed L back into the proposer as a learned reward (keeps it incorruptible).

Single-authority discipline preserved: validity channel = inertia meter; the loop
veto is a SEPARATE, also-incorruptible authority over *structural authority*, not a
second channel inside the free-energy objective F. Both are meters outside F.
