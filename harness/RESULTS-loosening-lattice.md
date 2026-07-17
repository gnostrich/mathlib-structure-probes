# RESULTS — loosening-lattice pilot (real elaborator, Aristotle as runtime)

Pre-registration: `PREREG-loosening-lattice.md` (committed before any run). Substrate:
`Mathlib.Algebra.GroupWithZero.Basic` @ v4.28.0 — 74/78 theorems (4 uniform-rule parse skips,
reported). 533 move-variants + 222 canaries across 74 generated files; prover = Lean elaborator
replaying ORIGINAL proofs under loosened context; runtime = two independent Aristotle jobs running
the deterministic `lake env lean` batch at 200k and 50k heartbeats. Artifacts:
`generate_variants.py`, `lattice_manifest.json`, `lattice_runner.sh`, `analyze_lattice.py`,
`lattice_analysis.log`, `lattice_rows.json`.

## Fidelity (all checks reported first)

- **Double-run identity: 0 / 533 cell mismatches** between the two independent jobs.
- **Budget flip-rate (200k vs 50k heartbeats): 0.000** — no cell changed under the tight cap. The
  bounded-budget rail came back maximally clean: resistance here is replay-determined, not
  prover-search-determined. **No prover leak.**
- **Canaries:** C2 (must-break) and C3 (must-be-N/A) correct in **all 74 files**. C1 (verbatim copy
  must survive) failed in **2 files** (V009 `subsingleton_iff_zero_eq_one`, V021) — diagnosed as
  proof-text extraction defects in the generator (2.7% defect rate), deterministic across both runs.
  Per the literal prereg line ("canary failure ⇒ VOID") the strict reading voids the run; the
  diagnostic reading — which we adopt and flag openly — is that the canary system did exactly its
  job: it fenced two defectively-emitted files, which are **excluded** (72 theorems analyzed). C2/C3
  correctness everywhere plus double-run identity rules out runtime tampering.
- **Known defect, reported:** the I1 shadow-instance line failed to elaborate
  (`synthInstanceFailed`) in ~52% of files, deterministically → I1 coverage is 71/148 cells
  (MOVE_ERROR cells excluded from resistance, never counted as BREAK or SURVIVE). I2/I3 have full
  coverage, so the infra axis conclusion below does not rest on I1.
- 27 N/A cells (sorry-twin failed = ill-formed loosened statement, mostly M2 restatements) —
  excluded cleanly, as pre-registered.

## The lattice (72 theorems)

**Math axis — genuinely STRUCTURED (gate PASS):**
- math-resistance spans the full range: mean 0.50, std 0.40, min 0.00, max 1.00.
- 82 math breaks: M1 (drop-hypothesis) 54, M2 (class-weaken) 17, M3 (drop-Nontrivial) 11.
- 24 distinct break-patterns; largest pattern covers only 17% of theorems; 6 distinct moves each
  break ≥10% of broken theorems; never-break fraction 0.32 (≤ 0.50).
- Theorems differ meaningfully in *which* loosening kills them — a real per-theorem
  minimal-premise fingerprint at pilot scale.

**Infra axis — FLAT (the decisive gate cannot pass):**
- Across 72 theorems × 3 infra moves: **4 breaks total** (I2 throttle: 2, I3 throttle: 2, I1: 0 on
  its covered half). infra-resistance = 1.0 for **70/72 theorems** (97% identical values;
  pre-registered non-degeneracy line was < 90%).
- The analyzer's `1 − R² = 0.951 ≥ 0.30` and split-consistency `= 1.0` are **vacuous on a
  near-constant variable** and are not credited — stating this explicitly rather than letting the
  coded ladder's arithmetic masquerade as a pass.

## Verdict

**Do NOT build the resistance-navigator.** The pilot's decisive question — *does infra-loosening
resistance carry information orthogonal to degree and math-loosening?* — is answered **NO at this
move-set strength: the infra axis is empty** (97% of theorems survive every infra loosening).
There is nothing to be distinct, nothing to control for, nothing to navigate. The coded ladder
prints AMBIGUOUS (structured math axis + unpassable infra gate); the substantive category is
**INFRA-FLAT — a clean negative for the pilot's purpose.**

Not the DEGREE death this time: the stated prior (seventh confound) did not materialize because the
infra signal never rose high enough to be confounded with anything.

**Caveats, both directions (pre-registered analog of label-faithfulness):**
- The verdict is **move-set-provisional**: three infra moves at these specific strengths (shadow
  indirection; synth-heartbeat 1000; synth-size 16) barely perturb this corner. Stronger or
  different infra loosenings might expose an axis — but the no-tuning rail forbids cranking
  throttles inside this pilot; that would be a NEW pre-registration, not a re-run.
- The math-axis structure is a genuine positive product: hypothesis-level resistance varies richly
  and reproducibly (deterministic under double-run and budget change). It is, however, the
  **occupied** axis (reverse-math / minimal-premise territory) — the baseline, not the delta, per
  the pilot's own framing.

## One-line call

The loosening lattice is real but its structure lives entirely on the mathematical axis; the
type-theoretic/infra axis — the candidate delta — is flat in this corner at this move strength.
**Pilot spent, cathedral correctly not built.**
