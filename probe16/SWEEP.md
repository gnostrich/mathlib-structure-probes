# PROBE 16 — occupancy sweep (blocking; written before any experiment code)

Date of sweep: **2026-07-27**. Searcher: Claude Code (WebSearch + direct source fetches).
Sweep precedes the pre-registration and any code, per directive §2.

## Queries run

1. `mutation testing proof assistants mutation analysis formal proofs Coq Isabelle Lean`
2. `mCoq mutation proving Coq mutation score per-lemma results Celik Gligoric`
3. `proof repair proof brittleness fragility Lean Coq Isabelle measuring how proofs break under change`
4. `Lean 4 Mathlib typeclass diamond detection elaboration failure analysis instance graph empirical study`
5. `automatic theorem generalization tactic weakening hypotheses lemma generalization Lean Coq automated`

Direct fetches: mCoq paper PDF (Celik et al., ASE 2019) — PDF text not machine-extractable, so
claims below rest on the paper's abstract/summary as surfaced by search plus the tool paper
(Jain et al. 2020); Gandhi, *Automatically Generalizing Proofs and Statements* (ITP 2025) — abstract
retrieved verbatim from the Dagstuhl landing page.

## Area 1 — Mutation testing / mutation analysis for proof assistants  **[occupied]**

- **mCoq** (Celik, Palmskog, Parovic, Ramos, Gligoric — ASE 2019; tool paper Jain et al. 2020,
  `EngineeringSoftware/mcoq`). Applies mutation operators to **Coq definitions of functions and
  datatypes** (operators borrowed from functional-programming mutation testing), then re-checks the
  proofs of lemmas affected by each mutation, recording pass/fail. Purpose stated by the authors:
  a **mutation score as a project/specification quality metric**; their qualitative payoff is
  "finding many instances of incomplete specifications".
- The authors note the operators are portable to Lean and Isabelle/HOL but that this is future work.

**Relation to Probe 16.** Same *mechanism* (perturb, re-check, log pass/fail) — Probe 16 claims no
novelty in the mechanism, which is squarely occupied. Differences in *what is measured*: mCoq mutates
**definition bodies** (a semantic change to the mathematics) and aggregates to a **per-project
score**; Probe 16 perturbs the **statement's parameter space** (hypotheses, class binders, universe
levels, instances, finiteness) and keeps a **per-theorem multi-component tuple**, with a
**depth axis** (1–3) that mutation analysis does not use.

## Area 2 — Proof repair / brittleness  **[occupied, opposite sign]**

- Proof repair across type equivalences and across quotient type equivalences (Ringer et al.);
  empirical studies of Isabelle proof breakage across prover versions (Hou et al., FSE).
- Consensus framing: proofs "break after the slightest change"; brittleness is a **cost to be
  reduced** and breakage is the **adversary**. Tools aim to *repair* or *prevent* failure.

**Relation to Probe 16.** Probe 16 inverts the sign: failure is the *measurement channel*, not the
problem. No paper found treats the failure locus as an object with geometry.

## Area 3 — Typeclass diamonds / elaboration failure  **[occupied]**

- Tabled typeclass resolution (Selsam, Ullrich, de Moura) — diamonds cause exponential resolution;
  engineering fix.
- *Use and abuse of instance parameters in the Lean mathematical library* (Baanen 2022);
  *Scalar actions in mathlib*; *Growing Mathlib* (2508.21593) — instance-graph pathology, diamond
  detection, priorities, library-health maintenance.
- *The Network Structure of Mathlib* (2604.24797) — the dependency-graph object this repo's fifteen
  prior probes measured.

**Relation to Probe 16.** These study the **instance graph / library health in aggregate**. D2 and D4
of Probe 16 move along exactly the hierarchies this literature describes — Probe 16 borrows those
hierarchies rather than inventing a metric, which is the point — but no per-theorem
direction-resolved failure profile was found.

## Area 4 — Automatic generalization / hypothesis weakening  **[occupied, adjacent-and-thin]**

- **Gandhi, ITP 2025** (building on Pons): an algorithm in Lean to *automatically generalize
  mathematical proofs* — "robustly generalizing repeated and related constants, as well as
  abstracting out hypotheses implicitly concerning them", with discussion of generalization's role in
  conjecturing and "learning from failure".
- Also: automatic hypothesis generalization inside induction tactics (revert-all-then-recurse).

**This is the closest prior art and the thinnest margin.** Gandhi's system *performs* generalization —
it searches for a maximally general form, i.e. it computes (implicitly) how far one can move along
generalization axes. If that work reported, per theorem, a **comparison across distinct axes** and
analysed whether the profile is theorem-specific, Probe 16 would be occupied. The retrieved abstract
describes a **synthesis algorithm producing generalized statements**, not a measurement study of
direction-dependent failure, and reports no anisotropy statistic. On that basis Probe 16's *question*
survives; its *moves* do not, and D1/D5 in particular are essentially Gandhi's territory viewed from
the failure side.

## Verdict

**NOT OCCUPIED on the specific question; occupied on essentially every component.** [occupied] for
the perturb-and-recheck mechanism (mCoq), the hierarchies traversed (typeclass/instance literature),
and the generalization moves themselves (Gandhi/Pons). [candidate-original] only for the narrow
question **"is the elaboration-failure locus around a theorem anisotropic, and is the anisotropy a
property of the theorem rather than of the perturbation generator?"**, operationalised as a
per-theorem 6-tuple with a between-theorem vs between-direction variance ratio and a
label-shuffle control.

**Honest assessment of the margin.** Thin. Probe 16 is a re-aiming of established machinery at an
unasked question, not new machinery. Should a reader know of per-theorem direction-resolved
brittleness profiles in the mutation-analysis or generalization literature, this probe is occupied
and should be withdrawn. Recorded as such.

**Sweep limitation (stated):** two key PDFs (mCoq, ITP 2025) were not machine-extractable in this
environment; the reading of mCoq's purpose and Gandhi's scope rests on abstracts and search-surfaced
summaries, not full texts. A full-text check could still reveal a per-theorem axis comparison and
flip the verdict to occupied.

## Sources

- [Mutation Analysis for Coq (mCoq, ASE 2019)](https://users.ece.utexas.edu/~gligoric/papers/CelikETAL19mCoq.pdf)
- [mCoq tool paper (2020)](https://users.ece.utexas.edu/~gligoric/papers/JainETAL20mCoqTool.pdf)
- [mCoq repository](https://github.com/EngineeringSoftware/mcoq)
- [Proof Repair across Type Equivalences](https://arxiv.org/pdf/2010.00774)
- [Proof Repair across Quotient Type Equivalences](https://arxiv.org/html/2310.06959v6)
- [Why the Proof Fails in Different Versions of Theorem Provers (Isabelle)](https://zhehou.github.io/papers/Empirical_Study_of_Compatibility_Issues_in_Isabelle.pdf)
- [Tabled Typeclass Resolution](https://arxiv.org/pdf/2001.04301)
- [Use and abuse of instance parameters in the Lean mathematical library](https://arxiv.org/pdf/2202.01629)
- [Growing Mathlib](https://arxiv.org/pdf/2508.21593)
- [The Network Structure of Mathlib](https://arxiv.org/pdf/2604.24797)
- [Automatically Generalizing Proofs and Statements (ITP 2025)](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ITP.2025.12)
