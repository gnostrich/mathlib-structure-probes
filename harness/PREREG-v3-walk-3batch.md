# PRE-REGISTRATION — V3 residue-advised loosening walk, staged-parallel, 3 batches

STATUS: pre-registered; committed BEFORE any run. One protocol, three substrates. Single question:
**does the shape of a stuck proof point at the constraint responsible (COMPASS), better than blind
search?** Everything else is mechanics instrumentation for the EBR port. These are
artificially-opened goals with kernel-checked ground truth — NO claims about Mathlib mathematics
(interior settled per PR #12).

## Staging (respects the gates)

- **Stage A (now, parallel):** B1 = `Mathlib.FieldTheory.Finite.Basic` (primary, Weil-adjacent);
  B2 = `Mathlib.Algebra.Group.Basic` (friendly control/fallback). Independent verdicts.
- **Stage B (gated):** B3 = certified-positivity artifact (own lemmas; present in repo, 75 files)
  launches iff Stage A yields COMPASS WORKS or clean COMPASS BLIND on ≥1 batch (loop demonstrated
  somewhere). If both A batches DEGENERATE: stop, no B3, report substrate-construction failure.
  B3 elevated-DEGENERATE risk pre-acknowledged; if B3 degenerates after A succeeded, attribute to
  substrate automation-hostility, not the machine.

## Architecture (adaptivity removed from the runtime — full state-table precompute)

The walk is adaptive, but its state space is finite: per goal, repair menu ≤ 5 ⇒ ≤ 2⁵ = 32 subsets.
We elaborate **every** subset-state once (single runtime round, Aristotle env as deterministic
courier, two independent jobs), recording per state: **CLOSES** / **STUCK + the unsolved-goals text**
/ NA (sorry-twin failed). Advised and blind walks then replay **locally** over the same table —
deterministic, any number of seeds, zero runtime adaptivity. Prefix-verbatim per goal (original
theorem NOT in scope — no self-closure contamination).

## Per-goal construction (uniform rules; selection = first N parseable theorems with ≥1 removable
site; N: B1 = 20, B2 = 30, B3 = 20 — B1 reduced from ~30 for runtime cost, declared before any run).
Repair menu capped at 4 (removals' inverses + ≤2 decoys) ⇒ ≤16 states/goal — cost containment,
declared now.

- **Removals (ground truth, 1–2 per goal, deterministic by name-hash):** RemHyp = delete an inline
  explicit `(h : P)` binder; RemInst = weaken ambient class one step on the fixed ladder
  (lattice ladder + `Field→DivisionRing→Ring`, `CommRing→Ring`, `IsDomain→NoZeroDivisors`).
  DEVIATION declared: defeq→propositional and admit-non-canonical-instance are EXCLUDED from both
  removals and repairs (no clean text-level ground-truth inverse); reported as dropped recipes.
- **Repair menu (≤5, fixed):** inverses of the removals (AddHyp(exact removed P); StrengthenInst
  (restore original class)) + deterministic decoys from a fixed catalog (AddHyp(v ≠ 0) on the first
  value variable; AddHyp instance-binder `Nontrivial τ`; StrengthenInst on a non-removed ladder
  step; trivial AddHyp(v = v)). Deduped against ground truth. No mid-run additions.
- **Fixed prover (all batches, all states):** `by intros; first | assumption | rfl | simp_all |
  aesop | skip` at `-DmaxHeartbeats=200000`. The `skip` tail guarantees a readable unsolved-goals
  display at halt. Held constant everywhere (cross-batch comparability).
- **Cost table (committed):** AddHyp c=2 (weakens the claim more), StrengthenInst c=1.

## The walks (local replay over the table)

- **Advised (the compass, fixed scoring — the entire hypothesis):** at each state, read the stuck
  display G; score each unapplied repair r: AddHyp(P): +3 if normalized P (or its equality-negation
  form) occurs in G; +1 if P's head variable occurs in G. StrengthenInst(C→C₀): +3 if the state's
  error text mentions "failed to synthesize"/C₀, +2 if G contains an operation symbol from the fixed
  class→symbol table (⁻¹,/ → Field/DivisionRing/GroupWithZero; - → Ring; ^ → Monoid). Take
  argmax(score − c) iff score > c, else HALT. Ties → lower cost, then lexicographic. Cap 6 steps.
- **Blind baseline (mandatory):** uniform random permutation of the same menu, applied until close;
  200 seeds; mean steps-to-close (non-closing = cap).

## Locked lines (per batch)

- **Evaluable goal:** full-repair state CLOSES and empty-repair state does NOT close (genuinely
  stuck, genuinely repairable under the fixed suite).
- **DEGENERATE:** evaluable goals < 50% of constructed goals, OR < 10 evaluable goals.
- **COMPASS WORKS:** on evaluable goals, ≥70% have advised discovered-set ⊆ ground-truth set with
  close within (removed-size+1) steps, AND blind mean steps ≥ 1.5 × advised mean steps.
- **COMPASS BLIND:** evaluable ≥ threshold but the 1.5× margin fails or containment < 70% —
  pointing carries no information here; a finding at full weight, not a failure.
- Fidelity: two independent runtime jobs; per-file C2 (must-break) / C3 (must-NA) canaries;
  outcome-table identity ≥ 98% on common cells or VOID. Budget-sensitivity: B2 also at 50k
  heartbeats; state-outcome flip-rate > 10% ⇒ prover-leak flag.

## Report (the porting deliverable)

Per batch verdict vs locked lines; walk traces (settle→point→pay→stop); cost-paid vs
residue-dissolved curves overlaid across batches; k-group enumeration (blocking constraint-class)
for goals with irreducible remainder; budget flag; one honest closing paragraph of porting notes —
which V3 mechanics demonstrated cleanly, which showed friction, compass verdict across substrates.

## Rails

Fixed prover/budget everywhere; named move-set only, no mid-run additions; blind baseline
non-optional; no Mathlib-mathematics claims; no re-running closed gates; no scaling past the
corners; B3 strictly gated; a COMPASS BLIND anywhere is reported at full weight; the EBR port
proceeds either way with the verdict as its guidance-claim license.
