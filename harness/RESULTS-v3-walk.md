# RESULTS — V3 residue-advised loosening walk (staged-parallel, 3 batches)

Pre-registration: `PREREG-v3-walk-3batch.md` (committed before any run; B1-size and menu-cap
amendments declared pre-run). Question under test: **does the shape of a stuck proof point at the
constraint responsible (COMPASS), better than blind search?** Artificially-opened goals with
kernel-checked ground truth; fixed suite `intros; first | assumption | rfl | simp_all | aesop |
skip` @ 200k heartbeats everywhere; full state-table precompute (adaptivity removed from runtime);
advised + blind (200 seeds) replayed locally. Artifacts: `walk_generate.py`, `walk_analyze.py`,
manifests, `walk_stageA.log`, `walk_stageB.log`, `walk_report_stage{A,B}.json`.

## Fidelity (all batches)

Double-run identity **0/300 (stage A) and 0/40 (stage B) cell mismatches**; all C2/C3 canaries
correct in all 64 files; budget flip-rate **0.000** at both stages (200k vs 50k) — **no prover
leak**: outcomes are replay-determined, not search-budget-determined. The instrument is clean; the
verdicts below are about the substrates.

## Verdicts against the locked lines

| batch | substrate | goals | evaluable | verdict |
|---|---|---|---|---|
| B1 | `FieldTheory.Finite.Basic` (Weil-adjacent) | 20 | **0** | **DEGENERATE** |
| B2 | `Algebra.Group.Basic` (friendly) | 30 | **15** (threshold met) | **COMPASS BLIND** |
| B3 | certified-positivity artifact (gated, launched per B2) | 14 | **0** | **DEGENERATE** (pre-acknowledged risk) |

- **B1 DEGENERATE:** the fixed suite cannot reprove even the intact statements (k-group: 20×
  unsolved-goal). Automation-hostile terrain cannot host the test — measured, not assumed.
- **B2 COMPASS BLIND — the decisive result:** goals were genuinely stuck and genuinely repairable
  (blind mean steps-to-close **2.77**), but the advised walk **never fired a single step**
  (containment 0.00, advised mean 6.00 = all-halt, margin 0.46× — blind strictly better; advised
  cost-paid 0.00).
- **B3 DEGENERATE:** 0/14 evaluable (k-groups: 11 unsolved-goal, 3 stmt-NA). Attributed to
  substrate automation-hostility, not the machine — the attribution is clean only because the loop
  was already demonstrated on B2, which is exactly why B3 was gated.

## The diagnosis (why the compass never fired — structural, not a scoring bug)

Two representative traces (from `walk_stageA.log` diagnostics):

- `eq_one_iff_eq_one_of_mul_eq_one`, removed premise `a * b = 1` → stuck display:
  `⊢ b = 1` / `⊢ a = 1`. **No textual trace of the removed premise.**
- `pow_mul_pow_sub`, removed premise `m ≤ n` → stuck display: `⊢ a ^ m * a ^ (n - m) = a ^ n`.
  The needed side-condition is semantically implicated (truncated subtraction) but **textually
  absent**.

The removal *destroys* the pointing information: the residue shows **where** you are stuck, not
**which** premise would fix it. The only textual signal that survives — variable overlap (+1 in the
committed scoring) — cannot discriminate true repairs from decoys (the trivial decoy `v = v` shares
variables too), and the committed cost bar correctly refuses to fire on it. This is genuine
COMPASS BLIND at the textual-shape level, reported at full weight per the rails.

## Cross-batch read (the compass-vs-substrate separation)

The pattern is the pre-flagged worst case: **BLIND despite clean stuckness on the friendliest
terrain, DEGENERATE everywhere harder.** There is no dose-response to measure because the compass
never registered a dose anywhere. Cost-paid vs residue-dissolved curves: advised arm is flat at
zero cost (never pays); blind arm dissolves the residue in ~2.8 uniformly-random steps on B2 —
i.e., with menus this small, *unguided* repair is cheap and guidance adds nothing.

## Porting notes (the deliverable paragraph)

Demonstrated cleanly: stuck-variant construction with kernel ground truth; sorry-twin statement
adjudication; full state-table precompute (adaptivity removed from the runtime — advised, blind,
and any future policy replay over one deterministic table); per-cell determinism across independent
runs and budgets; the DEGENERATE line doing real work (2 of 3 substrates cannot host the test under
a fixed bounded suite). Friction: automation-hostility dominates substrate choice (only basic
algebra is evaluable); menu sizes compress on sparse-hypothesis corners, weakening step-margin
power. **Compass verdict across substrates: BLIND (B2), untestable (B1, B3).** For the EBR port:
build with the **residue as readout only** — the stuck-state's shape, at least as pretty-printed
text, does not carry repair-direction information even in the easiest case; a guidance claim would
need a semantically richer reader (e.g. unifier/type-error introspection rather than goal text) and
must independently earn it under a NEW pre-registration, not inherit it from this pilot.
