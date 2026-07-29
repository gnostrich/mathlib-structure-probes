#!/usr/bin/env python3
"""Mirror the whole mathlib-structure-probes reasoning DAG into Paradigma Flywheel."""
import json, os, sys, time, uuid, urllib.request

API = "https://flywheel.paradigma.inc/api"
KEY = os.environ.get("FWK") or open(os.path.join(os.path.dirname(os.path.abspath(__file__)), ".fwk")).read().strip()
REPO = "https://github.com/gnostrich/mathlib-structure-probes"
BRANCH = os.environ.get("FW_BRANCH", "claude/mathlib-tail-dimension")
SHA = os.environ.get("FW_SHA", "")
XREF = "https://claude.ai/code/session_01BzKwSDmEf5XLe8BLvNXMBu"
STATE = os.path.dirname(os.path.abspath(__file__)) + "/fw_state.json"


def call(method, path, body=None):
    req = urllib.request.Request(API + path, method=method,
                                 data=json.dumps(body).encode() if body is not None else None)
    req.add_header("Authorization", "Bearer " + KEY)
    req.add_header("Content-Type", "application/json")
    req.add_header("Idempotency-Key", str(uuid.uuid4()))
    for attempt in range(5):
        try:
            with urllib.request.urlopen(req, timeout=90) as r:
                return json.loads(r.read())
        except Exception as e:
            if attempt == 4:
                raise
            time.sleep(2 ** attempt)


def commit(key, title, summary, content, parents):
    return call("POST", "/v1/nodes/commit-new", {
        "local_temp_node_id": f"msp-{key}",
        "parent_ids": parents,
        "staged_payload": {
            "title": title, "content": content, "summary": summary,
            "repo_context": {"repo_url": REPO, "branch_name": BRANCH,
                             "head_commit_sha": SHA or None, "origin_host": "github.com",
                             "updated_by": "claude-code", "external_transcript_ref": XREF}}})


N = []                     # (key, title, summary, [parent keys], content)


def node(key, title, summary, parents, content):
    N.append((key, title, summary, parents, content.strip()))


# ══════════════════════════════════════════════════════════ root + method
node("root", "Mathlib structure probes — programme root",
     "Does Mathlib's dependency structure carry any legible coordinate beyond depth? One robust positive, a long stack of clean negatives.",
     [], """
# Programme

**Question.** Formalised mathematics is a huge, fully-explicit artifact. Does its proof-dependency
structure carry any *legible, human-meaningful* coordinate — significance, taste, order, tension,
growth mechanism, memory — beyond the one obvious one (foundational depth)?

**Substrate.** Mathlib v4.28.0 @ `8f9d9cff6bd728b17a24e163c9402775d9e6a365`. Faithful
declaration-level dependency graph extracted with the real elaborator (`Expr.getUsedConstants`
over type **and** body): **333,044 declarations**, 7,523,067 kernel edges, 467,680 vertices
including core targets, **max depth 192**, mean 22.3, **0 non-trivial SCCs**.

**Aggregate finding after ~20 probes.** Mathlib's proof structure is a **near-pure hierarchy whose
one legible human-meaningful coordinate is depth**. Every antisymmetric, stylistic, order-dependent
or guidance signal probed either reduced to degree/gradient, or was not there.

**Honest status: no usable end product was built.** That is a finding, not an apology.
""")

node("method", "Discipline — the rules every probe ran under",
     "Pre-register before running, commit before running, one round, mechanical ladders, nulls first-class.",
     ["root"], """
# The standing policy

Every probe below ran under the same rules, and the rules did most of the work:

1. **Pre-register before running. Commit the pre-registration before computing the number.**
   Verdict lines, thresholds and controls are fixed in advance and applied mechanically.
2. **ONE ROUND.** No follow-up rounds authorised by default. No re-tuning after seeing results.
3. **"Inconclusive at this scale with this method" is a binding terminal verdict**, logged CLOSED,
   never pending.
4. **Harness-validity cell in every probe.** A known-answer control that must pass, or the run is
   VOID and *that failure is the published verdict*.
5. **Degree/confound controls are the decisive numbers**, never raw correlations.
6. **Walls and nulls are first-class outputs of equal standing to positives.**
7. **Claims are tagged**: [proven] / [conjectured] / [occupied] / [candidate-original] /
   [structural-rhyme] / [proven-negative]. Occupancy is swept *before* code is written.
8. **Fabrication is the worst failure mode.** Novelty inflation is prohibited.

This discipline killed several ideas that a looser process would have kept alive, and — twice —
killed the probe's own *instrument* rather than the hypothesis (probes 18, 19).
""")

node("methods-result", "[STANDING, transferable] Rank correlation is inert under extreme class imbalance",
     "At 0.056% prevalence a PERFECT ranker scores Spearman rho ~ 0.04. Use AUC + permutation.",
     ["method"], """
# A methods result worth keeping

Early probes tried to detect a signal with partial Spearman correlation against a rare label.

**Proved:** at a prevalence of **0.056%**, a *perfect* ranker — one that puts every positive above
every negative — scores **rho ≈ 0.041**. Rank correlation is mechanically inert in this regime;
a null result from it means nothing at all.

**Consequence, adopted for the rest of the programme:** AUC + permutation test, never
rank-correlation, whenever the positive class is rare. Several earlier "nulls" had to be re-read
because of this.

Tag: **[proven]**, transferable outside this project.
""")

node("instrument", "The reusable instrument — deterministic Lean-variant measurement",
     "Kernel-checked theorem perturbation with sorry-twin adjudication and must-fail canaries. 0 mismatches in ~900 cells.",
     ["root"], """
# What actually got built (and works)

A pipeline that turns "loosen or perturb a real theorem, see what still elaborates" into
deterministic data:

- generates kernel-checkable variants of real Mathlib theorems (hypothesis drops, class-ladder
  weakenings, instance perturbations, universe/finiteness perturbations) with **sorry-twin
  statement adjudication** (does the *statement* still typecheck, separately from the proof);
- runs them through the **actual Lean elaborator** at fixed heartbeat budgets, using a remote
  built-Mathlib environment (Aristotle) purely as a **dumb deterministic runner — never as a
  prover**;
- parses per-declaration outcomes with line-level attribution;
- **must-fail canaries** in every batch, and duplicate shards for fidelity.

**Measured fidelity: 0 mismatches in ~900 cells; 0.000 budget flip-rate; 0/275 canary failures;
0/230 duplicate-shard disagreements.**

Also here: the faithful kernel-edge extractor `DumpDeps.lean`, whose two independent runs were
**byte-identical** (provenance md5 `9f3a3c364cf975525e50049d10df194c`).

Tag: **[proven]** as an instrument. It is the one durable asset of the programme.
""")

node("egress", "Enabling move — the build was egress-blocked, so a remote env became the runtime",
     "GitHub releases 403 / blob cache 502 locally. Aristotle's built-Mathlib env used as a deterministic courier, never as a prover.",
     ["instrument"], """
# The unblock that made everything else possible

Building Mathlib locally was impossible in this environment: GitHub releases returned **403** and
the blob cache **502**. Rather than abandon the faithful graph, the remote built-Mathlib
environment (Aristotle) was used as a **deterministic runner**: upload a Lean file, run it, get
bytes back.

**Rail, held throughout:** the remote environment is a *courier*, never a prover. Nothing it
"proves" is ever credited. Two independent extraction jobs returned **byte-identical** output,
which is the evidence that the courier role is legitimate.

Refused hatches (recorded because refusing them cost real time):
- a static `value_deps` **simulation** of the elaborator — declined, it would have faked the data;
- Aristotle-**as-prover** for the loosening pilot — declined, that is exactly the thing being measured.
""")

# ══════════════════════════════════════════════════════════ Line A
node("lineA", "LINE A — is loop residue a significance signal?",
     "The original hypothesis: cycles/loops in the dependency structure mark important declarations. Killed.",
     ["root"], """
# Line A

**Hypothesis (the project's original one).** Declarations that sit in "loops" — dense
mutually-reinforcing regions of the dependency graph — are the significant ones, and a loop-residue
metric can veto or promote candidates.

**Outcome: killed.** The signal is reuse volume wearing a hat. It survives only in a form that
collapses under a degree control, or that is not metric-robust.
""")

node("A1", "A1 — H1/H2/H3 on the approximate graph",
     "H2 fails the degree control on the approximate decl graph (213,929 decls). Do not wire.",
     ["lineA"], """
# A1 — first pass, approximate graph

`loop_veto_test.py` on an approximate declaration graph (213,929 declarations, shallow parse).

- **H1** (loop metric predicts significance) — entangled with depth.
- **H2** (payoff) — **does NOT clear the degree confound control**.
- **H3** foils — implemented (see A2 for the bug that had to be fixed first).

**Verdict: do not wire.** Replicated on an independent v2 extraction.
""")

node("A1b", "A1b — the H3(b) redundancy bug (caught, fixed)",
     "Naive 2-hop stripping was degenerate: a directed triangle's closing edge is ALWAYS redundant. 7.8M -> 1317.",
     ["A1"], """
# A caught bug worth recording

The H3(b) foil stripped edges that had a 2-hop alternative path. This collapsed 7.8M triangles to
**1,317** — because a directed triangle's closing edge is *by construction* 2-hop redundant. The
foil was measuring its own definition.

**Fix:** require **≥ N distinct 2-hop intermediates** before calling an edge redundant.

Second bug in the same area: a **hardcoded verdict string** describing the approximate-graph
outcome, which would have been wrong for the faithful graph. Made data-driven.
""")

node("A2", "A2 — the faithful kernel graph (the decisive substrate)",
     "DumpDeps.lean via Aristotle: 333,044 decls, 7.5M kernel edges, two byte-identical runs.",
     ["lineA", "egress"], """
# A2 — get the real graph

The approximate graph was a shallow source parse. `DumpDeps.lean` uses `Expr.getUsedConstants`
over **type and value**, streaming through `IO.FS.Handle`, emitting
`{name, module, kind, type_deps, value_deps}` per declaration.

**333,044 declarations · 7,523,067 edges · two byte-identical runs.**

This graph is the substrate for every later probe in the programme, including probes 17 and 19.
""")

node("A3", "A3 — faithful re-run: the payoff FLIPS, but H1 stays ambiguous",
     "H2 clears on the faithful graph (0.539 -> 0.372); H1 = 0.528 vs a locked 0.40 bar -> AMBIGUOUS, DO NOT WIRE.",
     ["A2", "A1"], """
# A3 — the decisive re-run

On the faithful graph the result **flips relative to the approximate graph**:

- **H2 CLEARS the degree control**: 0.539 → **0.372**.
- **H1**: **0.528** against a pre-registered bar of **0.40** → **AMBIGUOUS**.

**Overall verdict: AMBIGUOUS → DO NOT WIRE.** Substantively positive (the payoff holds on the
faithful graph and is refuted on the approximate one — a real cross-substrate finding), but not a
clean GO, because loop and depth co-vary above the fixed line.

This is the single most annoying result in the programme: the honest reading is "the effect is
real but is not separable from depth at the pre-registered threshold", and the pre-registration
forbade moving the threshold.
""")

node("A4", "A4 — the birth-simplex loop metric, and its backfire",
     "A less depth-entangled loop metric was the named fix. It made things worse. Line A closed.",
     ["A3"], """
# A4 — the named successor, and its failure

A3's own stated next step: a **less depth-entangled loop metric** (birth-simplex /
non-backtracking residue), re-run, and wire only if H1 drops below 0.40 with H2 still up.

**It backfired.** The new metric did not separate loop from depth; it degraded the result.
Recorded in the `RESULTS-faithful.md` UPDATE section rather than quietly dropped.

**Line A is closed.** Loop residue = reuse volume; the triangle-only positive on the faithful
graph is not metric-robust.
""")

# ══════════════════════════════════════════════════════════ Line B
node("lineB", "LINE B — what does human importance actually correlate with?",
     "The one line that produced a standing positive. Anchor chosen OUTSIDE the graph, committed before results.",
     ["root"], """
# Line B

**Design rule that makes this line credible:** the importance anchor is **exogenous** — famous-theorem
lists (100/1000 theorems), exact-matched into Mathlib — and was **committed before any result was
seen**. Nothing about the anchor comes from the graph.
""")

node("B1", "[STANDING POSITIVE] B1 — importance ≈ foundational depth; reuse is chance",
     "AUC: compression 0.827, depth 0.814, reuse/in-degree 0.522 (p=0.14). Importance is NOT popularity.",
     ["lineB", "methods-result"], """
# B1 — the one robust positive of the programme

Against the exogenous famous-theorem anchor:

| predictor | AUC |
|---|---|
| compression rank `C` | **0.827** |
| **longest-prerequisite-chain depth** | **0.814** |
| reuse / in-degree | **0.522** (p = 0.14 ≈ chance) |

**Reading.** Human mathematical importance separates at **AUC ≈ 0.81** on *foundational depth*,
and **does not separate at all** on how often a result is reused. **Importance is not popularity.**
Depth is the one cheap structural correlate the programme could find.

Tag: **[proven]**. Doc: `RESULTS-compression-importance.md`.
""")

node("B2", "B2 — de-gamed MDL compression adds nothing beyond depth",
     "Beyond-depth AUC 0.569 against a pre-locked 0.58 line -> REDUCES.",
     ["B1"], """
# B2 — kill the more interesting half of B1

Raw compression (0.827) beat depth (0.814) — but raw compression is **gameable**: part of it is a
restatement of depth. So the gameable part was identified and removed by construction (an MDL
formulation), with three outcomes pre-committed: **SURVIVES / REDUCES / BROKE**.

**Result: beyond-depth AUC = 0.569 against a locked line of 0.58 → REDUCES.**

The prettier number did not survive de-gaming. Only depth stands. Doc: `RESULTS-compression-mdl.md`.
""")

# ══════════════════════════════════════════════════════════ Line C
node("lineC", "LINE C — is there an antisymmetric (order / holonomy) coordinate?",
     "If the order in which Mathlib was built carries information, it should show up as curl. It does not.",
     ["root"], """
# Line C

**Idea.** Mathlib was *built* in an order. If that order carries structure beyond a potential
function (i.e. beyond "everything flows downhill from foundations"), a Hodge decomposition of the
accumulation field should show a non-trivial **curl** component.

The whole line is an attempt to find a signal that is *antisymmetric* — one that a pure hierarchy
cannot fake.
""")

node("C1", "C1 — order-aware vs order-blind growth prediction",
     "Staged experiment; steered into the deviation gate and then the holonomy gate.",
     ["lineC"], """
# C1

Compare a growth predictor that sees accumulation order against one that does not. Run staged, and
deliberately steered into a sharper instrument (C2, then C3) rather than reported as a soft win.
The steering itself was pre-registered: *"its whole job is to point the re-run at the antisymmetric
observable with the double control, and to pre-commit that a null there is a real death."*
""")

node("C2", "C2 — deviation gate: back-guess vs back-actual",
     "Is the deviation between predicted and realised structure, or noise?",
     ["C1"], """
# C2 — the deviation gate

Run the same meter forward (predicted potential) and backward (realised residue) — pre-committed
as *"predicted-potential and realized-residue must be the same meter run forward vs backward"* —
and ask whether the deviation is structured or noise.

Outcome: not enough antisymmetric signal to justify anything downstream. Fed into C3.
""")

node("C3", "C3 — order-holonomy gate (Hodge curl) — DEAD",
     "curl_fraction = 0.076. ~92% pure gradient. A null here was pre-committed as a real death.",
     ["C2"], """
# C3 — the death of Line C

Hodge decomposition of the accumulation field, solved via `scipy.sparse.linalg.lsqr`:

```
curl_fraction = ||f - grad phi*||^2 / ||f||^2 = 0.076
```

**~92% of the field is a pure gradient.** The order in which Mathlib was built is, to that
accuracy, a potential function — no circulation, no holonomy.

**A null here was pre-committed as a real death, and is honored as one.**
Doc: `RESULTS-holonomy-gate.md`.
""")

node("C4", "C4 — cell 5: real Schur-gate self-selection — the epitaph",
     "Selecting the 'most atomic' declarations makes the field PURER gradient: curl 0.0009.",
     ["C3"], """
# C4 — the programme's epitaph

Last chance for Line C: restrict to declarations selected by a **real Schur-complement gate**
(`schur A b d = d − bᵀ A⁻¹ b`) — the structurally "atomic" ones, where any circulation should be
most visible.

```
curl(selected) = 0.0009
```

**Selecting for atomicity makes the field an even purer gradient**, by two orders of magnitude.
The signal does not concentrate; it evaporates.

This is the result that most clearly states the programme's aggregate finding.
Doc: `RESULTS-cell5.md`.
""")

node("C5", "C5 — tension EBM gate — degree in a hat",
     "Local Hodge tension vs forced-vs-open: collapses to degree on one axis, flat on the other. Do not build the EBM.",
     ["C3"], """
# C5 — do not build the energy-based model

Test whether a cheap **local Hodge tension** predicts whether a declaration was *forced* or *open*,
beyond degree.

**Result: degree-collapse on `Y_a`, flat on `Y_b`.** The tension is degree wearing a hat.

**Decision: do not build the EBM.** Doc: `RESULTS-tension-gate.md`.
""")

# ══════════════════════════════════════════════════════════ Line D
node("lineD", "LINE D — do discrete style / taste modes exist in Mathlib?",
     "Are there dominant tastes, or is it a smear? It is a smear, and subject beats author.",
     ["root"], """
# Line D — "do dominant tastes exist in Mathlib, or is it a smear?"

Three steps: (A) spectrum of a style embedding, (B) mutual information between style and author,
(C) per-author mode fingerprints.

**Result: a continuous smear.** No discrete modes. And **author style < subject matter** —
what a file is about predicts its style better than who wrote it.

Doc: `RESULTS-style-modes.md`. This result is quietly echoed later by probe 17's Check B, which
found the *opposite* direction for a different coordinate (subject explains only 7.7% of
definitional fraction) — the two together say style is subject-driven while proof-discharge mode
is not.
""")

# ══════════════════════════════════════════════════════════ Line E
node("lineE", "LINE E — term space: does the substrate render at all?",
     "Stop measuring the graph, start measuring the terms. Four probes; the substrate mostly refuses.",
     ["root", "instrument"], """
# Line E

Every probe up to here measured the **dependency graph**. Line E measures **terms**: perturb a real
theorem, run the real elaborator, see what survives.

Recurring finding across all four probes: **the substrate is far more brittle and far less varied
than the hypotheses assumed.** The instrument works; the terrain does not have the structure the
questions presuppose.
""")

node("E1", "E1 — loosening-lattice pilot: preamble gate FAILED",
     "No bounded prover available -> stop-report, frozen design, refused to fake it.",
     ["lineE"], """
# E1 — a stop-report instead of a result

The loosening-lattice pilot needed a **bounded prover** to decide whether a loosened statement is
still provable. The pre-registered preamble gate asked whether one existed within the rails.

**It did not.** A stop-report was written and the design frozen, rather than substituting
Aristotle-as-prover (which would have measured the prover, not the lattice).

The user then said *"just do it here"*, which unblocked E2 by changing the *runtime*, not the rails.
""")

node("E2", "E2 — loosening lattice: math axis STRUCTURED, infra axis FLAT",
     "4 breaks in 216 cells on the type-theoretic axis. Do not build the navigator.",
     ["E1"], """
# E2 — the first split between "math" and "infrastructure"

With the elaborator itself as the prover (Aristotle as runtime only):

- **mathematical axis** — richly structured; loosenings break in informative patterns;
- **type-theoretic / infrastructure axis** — **flat: 4 breaks in 216 cells**.

**Decision: do not build the navigator.** Doc: `RESULTS-loosening-lattice.md`.

This flatness is the first sighting of what probe 16 later confirms at scale: Mathlib's core is
already universe-polymorphic with almost no finiteness assumptions, so the "infrastructure"
degrees of freedom the hypotheses wanted to vary **barely exist**.
""")

node("E3", "E3 — V3 residue-advised walk: COMPASS BLIND",
     "The removed premise is textually ABSENT from the stuck-proof residue. Residue = readout only.",
     ["lineE"], """
# E3 — the compass does not point

**Question.** When a proof gets stuck because a premise was removed, does the *shape of the stuck
residue* point at the missing constraint?

Design: full state-table precompute (elaborate all 2^m repair subsets once), then replay an
**advised** walk and a **blind** walk locally. Three batches, staged in parallel; batch 3
pre-registered as **gated on batch 1 demonstrating the loop** (a correction the user made to my
naive parallel plan).

**Result: COMPASS BLIND (B2); DEGENERATE (B1, B3).** The removed premise is **textually absent**
from the residue. Residue is a **readout, not a guide**.

Doc: `RESULTS-v3-walk.md`.
""")

node("E4", "E4 / PROBE 16 — term-space failure anisotropy: CEILING (not a null)",
     "94.6% of cells fail at depth 1. Both ceiling triggers fire. The '6-tuple' of perturbation directions is really a 2-tuple.",
     ["lineE"], """
# Probe 16 — anisotropy of failure in term space

**Question.** Does failure under perturbation have *direction* — is the term space anisotropic?

245 corpus theorems from `Algebra/Group/Basic` + `Order/Basic`, perturbed along **six declared
type-theoretic directions D1–D6 at depths 1–3**, replaying each ORIGINAL proof under the perturbed
statement. 275 files, 880 logs.

**VERDICT: CEILING (not a null).** 94.6% of measurable cells fail at depth 1; 95.1% ever fail.
Both pre-registered ceiling triggers fire. **Depths were NOT re-tuned** — re-tuning to escape a
ceiling was explicitly forbidden and explicitly declined.

**The anisotropy test would not have passed either:** A_obs = 52.0 vs A_shuffled = 48.3 = **1.08×**
against a required **3×**. A is inflated only because V_D ≈ 0; the column-wise permutation control
exposes it.

**Instrument sound, not blind:** harness cell PASSES decisively — decorative-structure trivialities
R = 1.000 vs hypothesis-laden theorems 0.133, Mann–Whitney **p = 1.25e-12**. 0/275 canary failures,
0/230 duplicate-shard disagreements.

**Measured substrate facts:** 98% of hypothesis deletions and 93% of single-step class weakenings
break immediately; only **11/159** theorems tolerate ANY perturbation. **Four of the six directions
barely exist** (D3 and D5: zero measurable cells; D4: nine; D6: two). The "6-tuple" is a 2-tuple.
""")

node("E4bugs", "E4 — three parser bugs, all caught BEFORE the run",
     "varstack never popped; type variable chosen as first declared while class binders attach elsewhere; duplicate binders.",
     ["E4"], """
# Three bugs caught before running (the reason the probe is trustworthy)

1. **`varstack` never popped on `end`** → D2 emitted incoherent diamonds like
   `[Semigroup][CancelCommMonoid][DivInvMonoid]`.
2. **The type variable was chosen as the first declared** (`α` from `variable {α β G M : Type*}`)
   **while the class binders actually attach to `G`** → this silently *zeroed* D2 coverage. A
   probe that ran with this bug would have reported a clean null for a direction it never tested.
3. **Duplicate binders** `{a : PXV} … (a : PXV)`.

All three were found by inspecting generated variants before launching, not by the results looking
wrong. This is the strongest argument for the "read your own generated artifacts" habit.
""")

# ══════════════════════════════════════════════════════════ Line F
node("lineF", "LINE F — is the rfl-locus a native coordinate?",
     "Are definitionally-discharged theorems a real coordinate, or a restatement of depth / subject?",
     ["root"], """
# Line F

**Object.** The fraction of theorems discharged **definitionally** (`rfl` and friends) versus
substantively. A prior probe suggested this clusters, and that the clustering is not obviously
depth.

**Two checks, both against the paper's own machinery** (arXiv:2603.20396, which measured
wrapped/unwrapped length and depth and explicitly *discarded* the proof-automation signal as an
artifact).
""")

node("F1", "F1 / PROBE 17 — rfl-locus confirmation: PARTIAL",
     "D = AUC(their depth -> substantive) = 0.6508; S = subject variance = 0.0770. Check B passes, Check A does not clear.",
     ["lineF", "A2"], """
# Probe 17 — the two numbers

| quantity | value |
|---|---|
| **D** = AUC(their declaration-level depth → substantive) | **0.6508** |
| **S** = module-level variance in definitional fraction explained by subject | **0.0770** |

**Both classes reported separately, never merged:**

| class | share | AUC(depth → class) | S |
|---|---|---|---|
| strict `rfl` | 10.76% | 0.3103 | 0.0770 |
| `by simp` | 5.85% | 0.4517 | 0.0712 |
| substantive | 83.39% | 0.6508 (= D) | — |

AUC < 0.5 means *shallower than chance*. **All of D's excess over 0.5 is carried by strict `rfl`;
the `simp` class is depth-indifferent.**

**Harness PASS:** Logic+Init 0.1796 vs Analysis 0.0659; max depth 192; 467,680 vertices vs their
reported 463,719 (0.85% apart).

**VERDICT: PARTIAL. TERMINAL, CLOSED.** Not ≤ 0.60 (CONFIRMED), not ≥ 0.75 (DEPTH-REDUCIBLE),
S far below 0.80 so SUBJECT-REDUCIBLE is decisively excluded.

- **Check B passes cleanly and is the informative half** — subject matter explains **7.7%**. The
  clustering is *not* a restatement of what a file is about. **[proven]**
- **Check A is where it fails to clear** — the module-import proxy said 0.556; the paper's real
  depth says **0.651**, *more* entangled, and barely above the **0.621** statement-length baseline.
""")

node("F1disc", "F1 — five discrepancies, reported unsmoothed",
     "Including: the prior probe's own headline numbers did NOT reproduce.",
     ["F1"], """
# Discrepancies (reported, not smoothed)

1. **The prior probe did not reproduce.** 10.76% over 170,326 declarations here vs its reported
   7.34% over 185,429. Different commit and/or enumeration. **The prior numbers should not be
   treated as replicated.**
2. Max depth **192** vs their ~300 — inside the pre-registered band, systematically shallower
   (Lean-core constants are depth-0 leaves here rather than internal nodes).
3. **Zero non-trivial SCCs** vs their ~60 (unsafe recursion, absent from a Mathlib-scoped
   extraction; immaterial — their own collapse moved 463,719 → 463,661).
4. Their named largest unwrapped element is **present but ranks 6,067** — consistent with declared
   deviation 1 (multiplicity-blind weights), pre-declared **soft**, not VOID-bearing.
5. Elaborated-term cross-check is **weak**: median proof-side `value_deps` 12 vs 29, only ~2.4×.

**Classification is source text**, so `rfl` behind wrappers is missed: **10.76% is a floor.**
""")

# ══════════════════════════════════════════════════════════ Line G
node("lineG", "LINE G — growth mechanism: is the resolvent a driver or an instrument?",
     "Does branching require harmonic-measure growth? Two probes, two VOIDs, precondition unestablished.",
     ["root"], """
# Line G

**The claim this is a precondition for.** Known mathematics is a thin branching set inside an
exponentially large space of valid deductions. Two candidate growth rules:

- **LOCAL (Eden)** — uniform on the boundary → compact blob;
- **HARMONIC (DLA/DBM)** — growth ∝ harmonic measure → tips grow faster → **branches**.

If branching genuinely *requires* the harmonic rule, the resolvent is a growth **driver**, not a
measurement instrument.

**Substrates:** Z² as harness (known exponents), **T₃ × Z** as test (non-amenable, ambient growth
rate log 2 ≈ 0.693, with sideways room so filamenting is a genuine outcome rather than forced).

**Status after two probes: the precondition remains UNESTABLISHED — neither supported nor refuted.**
""")

node("G1", "G1 / probe 17b — Monte Carlo DLA: VOID (transient walk)",
     "On T3xZ walkers escape to infinity; 18-67% of depositions fell back to a DIFFERENT growth rule.",
     ["lineG"], """
# 17b — the walker method dies on a non-amenable graph

Classic DLA: launch a random walker far away, deposit at first contact. **Works on Z².** On
**T₃ × Z** it does not — the walk is strongly transient, escape probability → 1, and the arrival
rate decays exponentially in launch radius.

**Instrumented: 18–67% of depositions fell back to a deterministic rule instead of a walker hit.**
That is not noise; it is a *different growth rule* silently substituted into the arm.

**VOID, terminal under the Monte Carlo method.** Named successor: solve for the harmonic measure
directly.
""")

node("G2", "G2 / PROBE 18 — DBM Laplace solver: VOID (truncation convergence failed)",
     "Exponent cells PASS (Eden 2.0597, DBM 1.6841) but D(+10) vs D(+25) = 1.6462 vs 1.7479, |diff| 0.1017 > 0.05.",
     ["G1"], """
# Probe 18 — no walkers; solve the field

Dielectric Breakdown Model (Niemeyer–Pietronero–Wiesmann 1984), η = 1 ≡ DLA. One Dirichlet solve
per deposition: `h = 0` on the cluster, `h = 1` at `R_out`, harmonic elsewhere; grow at a perimeter
site with probability ∝ `h^η`.

| harness cell | requirement | measured | |
|---|---|---|---|
| Z² Eden `D` | [1.90, 2.10] | **2.0597** (2.046/2.137/1.996) | PASS on the mean |
| Z² DBM(η=1) `D` | [1.60, 1.85] | **1.6841** (1.832/1.576/1.644) | PASS on the mean |
| **truncation convergence** | \\|D(+10) − D(+25)\\| ≤ 0.05 | **0.1017** (1.6462 vs 1.7479) | **FAIL** |

**VERDICT: VOID.**

**The method change did work on its own terms:** 0 CG fallbacks across 8,000+ Dirichlet solves,
max deviation vs exact `spsolve` ≤ 3.6e-8, and — unlike 17b — **no deposition anywhere fell back to
a different growth rule**. 17b's contamination is genuinely fixed. The run died on a different cell.
""")

node("G2diag", "G2 — the honest diagnosis: the test cannot resolve its own question",
     "Seed-to-seed spread of D at FIXED margin is 0.256 — five times the 0.05 tolerance. Recorded, not repaired.",
     ["G2"], """
# Why probe 18 failed, and why it was not fixed

The convergence cell is a **single-seed** comparison. At N = 2500 the **seed-to-seed spread of Z²
DBM `D` at a fixed margin is 0.256** — five times the 0.05 tolerance the cell demands. The 0.1017
gap is **not distinguishable from estimator noise**, and the three margins are not even monotone
(1.646 / 1.832 / 1.748 at +10 / +15 / +25).

**That is a defect of the pre-registered test, discovered by running it. It was recorded, not
repaired.** Re-running with more seeds or larger N to land inside tolerance is exactly the
outcome-dependent adjustment the pre-registration forbids.

**Test cell, non-adjudicating:** T₃×Z `c(Eden) = 0.2882` (N = 500) vs `c(DBM) = 0.2667`
(N = 146–185). Every DBM run hit the pre-registered `MAX_DOMAIN` guard — continuing needed a ball
of **1,572,823** nodes against a 1,200,000 cap — so **the arms are not N-matched**, and no
N-matched comparison was pre-registered or introduced afterwards.
""")

node("G3", "G3 — named successor (NOT authorised)",
     "Exact linear algebra on a smaller truncation, as a fresh probe with a fresh prereg.",
     ["G2diag"], """
# What Line G would need next — not authorised, not started

Exact linear algebra on a **smaller** truncation. It would be a **fresh probe with a fresh
pre-registration**, and it must first fix the defect found above:

> a convergence tolerance must be stated **relative to the estimator's own seed variance**,
> not as an absolute 0.05.

Recorded here so the line is legible, **not** as pending work.
""")

# ══════════════════════════════════════════════════════════ Line H
node("lineH", "LINE H — tail dimension: does the corpus have memory along depth?",
     "Excess entropy / Hankel rank of the prerequisite tape. Rank measured DIRECTLY, never as L(M) - M*h.",
     ["root"], """
# Line H

**What is measured.** `E = I(shallow half ; deep half)` — the **tail dimension**: how many causal
states are needed to predict deep declarations from shallow ones.

**Method rail:** measure the **rank directly**. `E` is *not* estimated as `L(M) − M·h`; that is a
difference of two divergent quantities and is unstable. **The rank is the quantity.**

**Tape.** Row = a declaration; string = its depth-realizing prerequisite chain from a primitive to
itself, ascending depth. Position in the string **is** prerequisite depth (along a depth-realizing
path the grading falls by exactly 1 per step). Cap 24, truncated from the shallow end. 20,000
declarations, seed 20260729.
""")

node("H1", "H1 / PROBE 19 — Hankel rank: VOID (harness failed 8 of 12)",
     "The synthetic 3-state HMM returned 1,2,3,3,73,104,18,36,46,2,59,35. Real arm NOT interpreted.",
     ["lineH", "A2"], """
# Probe 19 — the 36-cell matrix

`k ∈ {0,1,2,3}` (alphabet filtration) × `L ∈ {1,2,3}` × `{real, shuffle, synthetic}`, `R = 3`.

**Harness:** the synthetic arm is a hand-built **3-state HMM** with known ground truth and had to
return effective rank **2–4** at every (k, L). It returned
**1, 2, 3, 3, 73, 104, 18, 36, 46, 2, 59, 35** — **8 of 12 cells fail**.

**VERDICT: VOID. The real arm is not interpreted.** (Real column, published raw and uninterpreted:
2, 2, 12 / 40, 52, 7 / 79, 22, 12 / 3, 165, 155.)

**Three estimator defects, none in the corpus:**
1. The shuffle column reads **15** by arithmetic — 5% of a 300-value truncated spectrum lies above
   its own 95th percentile. It is not a measurement.
2. **The arms are not dimension-matched.** Shuffling destroys the repetition that makes real
   contexts recur: at k=1, L=3 the real arm has **1,441** distinct pasts against the shuffle's
   **34,299**. A percentile from a differently-shaped matrix is not a floor.
3. **The floor is itself data-starved** in 7 of 12 cells, down to **1.0** observations per context,
   where rows are one-hot and singular values are pinned at 1 by construction.
""")

node("H2", "H2 — the estimability ceiling: 9 of 12 cells were never measurements",
     "r_max = min(algebraic, minimax parameter count at N=20,000, per-row SNR). Reported ranks exceed it by up to 165x.",
     ["H1"], """
# The estimability ceiling (added mid-run, computed before any cell was interpreted)

`r_max` = min of three bounds:
- **algebraic** — `r ≤ min(#pasts, #futures)`;
- **minimax / parameter count** — a rank-`r` conditional matrix on `m × f` has `r(m+f−r)` free
  parameters, so it is not distinguishable from a lower-rank one unless `N ≥ r(m+f−r)`, at
  **N = 20,000 independent declarations**;
- **per-row SNR (Fano-flavoured)** — `E‖p̂_u − p_u‖² ≤ 1/n_u` and `Σσ² = ‖H‖_F² ≤ m` force
  `r ≤ n̄`, the mean count per past.

**9 of 12 cells are CEILING on both the real and the synthetic arm.** Only the three k=0 cells are
measurements at all. Reported effective rank exceeds what is estimable by up to **two orders of
magnitude** (k=3, L=2: **165 against r_max = 1**). No growth law over L is fittable outside k=0.

**This explains the harness failure completely, and splits it in two:**
- the **seven k ≥ 1 failures are estimability artifacts**, exactly as the bound predicts;
- the **k=0, L=1 failure is structural**: with 3 distinct pasts, the 95th percentile of a 3-value
  spectrum is essentially its maximum, so **rank 3 is unreachable by construction**.

The synthetic arm **passes at the only two cells that are both estimable and able to express the
answer** (k=0, L=2 and L=3). **VOID still stands; the real arm is still not interpreted, k=0
included; Rule A is not read off the k=0 column.**
""")

node("H3", "H3 — substrate limitations found while building probe 19",
     "k=0 alphabet is 3 not 6; k=2 head constructor is a surrogate with 37.9% NA; hashing breaks nesting above k=1.",
     ["H1"], """
# What the substrate would not give

- **The k=0 alphabet is 3, not the declared 6.** The faithful dump records
  `kind ∈ {theorem, def, other}` only — `instance`, `structure`, `abbrev` were already folded away
  at extraction time inside `DumpDeps.lean`. Coarser than specified; not *degenerate*, so rule D
  was not triggered, but not what was asked for either.
- **The k=2 head type constructor is a source-text surrogate.** The dump carries no type
  expressions, and `type_deps` is in `getUsedConstants` traversal order so its first element is a
  *binder* constant, not the head. Parsed from source with a fixed notation table;
  **NA share = 37.9%** (core constants, anonymous instances, auto-generated declarations).
- **Hashing had to be extended from k=3 to k=2** (11,756 raw symbols). **Hashing breaks the nesting
  of the quotient chain** — the filtration is a chain of quotients only up to k=1.
- One implementation correction was made **before any spectrum was computed**: the namespace root
  is the **module** root (32 of them: Algebra, Topology, Order, CategoryTheory …), not the
  declaration name's first component (which gave 9,927 pseudo-roots).
""")

# ══════════════════════════════════════════════════════════ cross-cutting
node("occupancy", "Cross-cutting — occupancy sweeps and what is NOT claimed as novel",
     "Every component was swept for prior art before code was written. Nothing here claims novelty.",
     ["method"], """
# Occupancy — swept before code, in every probe

- **Probe 16**: NOT OCCUPIED on the exact question; **[occupied] on every component** — mCoq, the
  typeclass/instance literature, Gandhi ITP 2025. **Margin recorded as thin.**
- **Probes 17 / 19**: `arXiv:2603.20396` (depth machinery) and **`arXiv:2604.24797`, "The Network
  Structure of Mathlib"** — structural/network analysis of the same corpus, not
  information-theoretic. **Their** finding that centrality captures infrastructure rather than
  mathematical relevance is cited as theirs and is **not** restated as new here.
- **Probe 18**: DBM/DLA on Z² is [occupied] (Witten–Sander 1981; NPW 1984); DLA on trees and
  non-amenable graphs is [occupied] (Barlow–Pemantle–Perkins; Benjamini–Yadin).
- **Probe 19**: Crutchfield–Young causal states, Hankel-rank spectral learning — [occupied].

**No novelty claim is made anywhere in this programme.**
""")

node("notclaimed", "Cross-cutting — what is NOT claimed, everywhere",
     "Nothing here is a statement about mathematics. Mathlib is a curated artifact with sociology in it.",
     ["root"], """
# What is NOT claimed

- **Nothing here is a statement about mathematics.** Every measurement is of the **formalized
  corpus**, under **declared** encodings and filtrations. **Mathlib is a curated artifact with
  sociology in it.**
- **No importance, quality or interestingness signal** beyond the depth correlate in B1 — and B1 is
  a separation against an exogenous list, not a definition of importance.
- **No conjecturer, no generator, no navigator, no EBM was built.** Several were designed and then
  explicitly *not* built because the gate that would have justified them failed.
- **No claim about Mathlib's tail dimension** in either direction (probe 19 is VOID).
- **No claim that harmonic growth fails to filament** on a non-amenable graph (probe 18 is VOID and
  its arms are not N-matched). The resolvent-as-driver precondition is **unestablished**.
- **No claim that the rfl-locus is a native coordinate** (probe 17 is PARTIAL).
""")

node("standing", "SUMMARY — everything that actually stands",
     "One robust positive, one methods result, one instrument. Everything else is a clean negative.",
     ["B1", "B2", "methods-result", "instrument", "C4", "E4", "F1", "G2diag", "H2"], """
# The standing ledger

## Stands
1. **Human importance ≈ foundational depth** (AUC **0.814**; reuse **0.522 ≈ chance**), against an
   exogenous anchor committed before results. **Importance is not popularity.** [proven]
2. **De-gamed compression adds nothing beyond depth** (0.569 vs a locked 0.58). [proven-negative]
3. **Rank correlation is inert under extreme class imbalance**; use AUC + permutation. [proven]
4. **A working deterministic Lean-variant instrument** — 0 mismatches in ~900 cells,
   0.000 budget flip-rate, canaries clean. [proven]

## Killed at pre-committed lines
| probe | verdict |
|---|---|
| loop residue as significance | = reuse volume; not metric-robust |
| discrete style/taste modes | continuous smear; author style < subject |
| order-holonomy / circulation | ~92% pure gradient (curl 0.076) |
| Schur-gate atomicity self-selection | an even purer gradient (curl 0.0009) |
| local Hodge tension → forced/open | degree in a hat |
| type-theoretic loosening axis | flat — 4 breaks in 216 cells |
| stuck-proof shape → missing constraint | BLIND — premise textually absent from residue |
| term-space failure anisotropy | CEILING — 94.6% fail at depth 1; 1.08× vs a required 3× |

## Void / partial (instrument died, not the hypothesis)
| probe | verdict |
|---|---|
| rfl-locus as native coordinate | **PARTIAL** (D = 0.651, S = 0.077) |
| harmonic growth on T₃ × Z (walkers) | **VOID** — transient walk, 18–67% contaminated |
| harmonic growth on T₃ × Z (Laplace) | **VOID** — truncation test cannot resolve its own question |
| tail dimension / Hankel rank | **VOID** — 9 of 12 cells above the estimability ceiling |

## The aggregate
**Mathlib's proof structure is a near-pure hierarchy whose one legible human-meaningful coordinate
is depth.** Every antisymmetric, stylistic, order-dependent or guidance signal probed either
reduced to degree/gradient, or was not there.

**No usable end product was built. That is a finding, not an apology.**
""")

# ══════════════════════════════════════════════════════════ run
state = json.load(open(STATE)) if os.path.exists(STATE) else {}
for key, title, summary, parents, content in N:
    if key in state:
        print(f"  skip {key} (exists {state[key]})"); continue
    pids = [state[p] for p in parents if p in state]
    r = commit(key, title, summary, content, pids)
    state[key] = r["node"]["node_id"]
    json.dump(state, open(STATE, "w"), indent=1)
    print(f"  + {key:12s} {r['node']['slug_name']:24s} parents={len(pids)}  {title[:52]}")
print(f"\n{len(state)} nodes in graph -> https://flywheel.paradigma.inc")
