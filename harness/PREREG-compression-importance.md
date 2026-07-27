# PRE-REGISTRATION — compression/rank vs an EXOGENOUS importance anchor

STATUS: pre-registered. Metric, anchor, thresholds, reads fixed BELOW before any results.
Committed before the analysis. The point is to break the self-referential graph-vs-graph
loop: BOTH the signal (compression, degree-free by construction) AND the target (human
importance, exogenous to the Mathlib graph) are degree-independent, so a null is a real kill
and a positive is a real find. No post-hoc tuning; no swapping the anchor until one correlates.

Ground truth at pre-registration (confirmed from repo): (a) the degree-normalized loop metric
`ratio T/E` is committed and clears H1 (−0.341) / H2-reuse (+0.501); (b) every degree-free
IMPORTANCE proxy (@[simp] −0.02, thm/lemma label −0.12) came back null — loops = reuse-volume;
(c) no compression/rank measure and no exogenous importance anchor exist in the repo yet.

## Phase A — the compression/rank signal `C(v)`, degree-free by construction

**Definition (fixed):** `C(v) = log(1 + D(v))`, where `D(v)` = the number of DISTINCT
declarations in `v`'s transitive dependency closure (the out-reachable set following
type+value dependency edges — everything `v` is built from), estimated by bottom-k MinHash
(k = 96) propagated over the SCC condensation in reverse-topological order. Interpretation:
the amount of accumulated proof/statement content `v` packages into one citable name — the
dependency-DAG description length `v` compresses per reference. **Degree-free by construction:**
`D(v)` does not involve `v`'s in-degree (usage) at all — a once-used lemma that packages a
huge derivation scores high; a many-times-used triviality scores low.

**Gate (a metric must pass this BEFORE it is used — same bar the loop metric had):**
- PRIMARY: `|rho(C, in-degree)| < 0.40`. In-degree (reuse-volume) is the confound axis this
  whole arc proved dominates; `C` must be decoupled from it or it is disqualified — no rescuing.
- REPORTED transparently: `rho(C, undirected-degree)`, `rho(C, out-degree)`. If `C` is
  essentially out-degree (`rho(C,outdeg) > 0.9`) it is "proof-width in disguise" — flagged and
  interpreted cautiously, not silently used.

## Phase B — the exogenous anchor `Y*` (NOT derivable from the Mathlib graph)

**Anchor (fixed):** `Y*(v) = 1` iff `v` is the declaration a curated famous-theorem list maps
to, from mathlib4 `docs/100.yaml` (Freek Wiedijk's Formalizing 100 Theorems) ∪ `docs/1000.yaml`
(the 1000+ theorems project). Human-curated fame, exogenous to the dependency graph.
**Bridge = EXACT decl-name join** (the yaml supplies the Mathlib decl name — no fuzzy matching).
**Coverage (measured up front, honestly):** 185 famous-theorem decls match the 333,044-node
faithful graph (100.yaml 43/56 decl-entries, 1000.yaml 165/172). Positives are sparse (0.06%)
but the bridge is exact. **Scope caveat:** this covers the FORMALIZED-and-mapped famous subset;
unformalized-famous theorems are absent from the graph, so the claim is about formalized-famous
declarations only. Bridge quality is reported before any correlation is believed.

## Pre-registered reads (fixed now)

1. **Gate:** if `C` fails `|rho(C, in-degree)| < 0.40`, it is disqualified — report and stop
   (no rescuing, no redefining to pass).
2. **Payoff:** partial `Spearman(C, Y* | log-in-degree, depth) > 0`, non-trivial, with a
   permutation p-value; AND `C` must beat baselines at separating famous from non-famous —
   `AUC(C)` > `AUC(in-degree ranker)` and > `AUC(subject-only ranker)`.
3. **Anti-gaming:** inject synthetic trivial `A∧B` conjunctions of distant deep theorems; if a
   descendant-union metric credits them with high `C`, that is a documented corruptibility of
   `C` (report it — it does not invalidate the descriptive famous-vs-not finding, but it gates
   building a conjecturer on `C`).
4. **KILL (honor it):** if `C` vs `Y*` is ~0 or negative under the correct (in-degree, depth)
   control, or `C` does not beat the degree ranker, the verdict is: **"human importance is not a
   structural invariant of Mathlib's proof library — it lives in the practice the library only
   shadows."** Write it and stop; do NOT roll to a fourth endogenous metric.
5. **POSITIVE:** if `C` passes the gate AND clears the payoff AND beats the baselines, then
   compression-rank (not holonomy/loops) is the hidden coordinate the whole arc was circling —
   and THAT is what a judge/conjecturer should be built on.

Discipline rails held throughout: non-learned, degree-free BY CONSTRUCTION (not post-hoc
residualized); ONE exogenous anchor fixed before results; bridge coverage/noise reported up
front; a single sharp test with an honest kill on the table.
