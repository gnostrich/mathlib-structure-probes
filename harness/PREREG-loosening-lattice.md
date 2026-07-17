# PRE-REGISTRATION — loosening-lattice pilot (executing session; adopts the frozen design)

STATUS: pre-registered; committed BEFORE any elaboration runs. Adopts
`REPORT-loosening-pilot-feasibility.md`'s frozen design with the deviations listed below (each
forced by substrate mechanics or environment, none by results — no results exist yet). Measurement
only: no EBM, no sampler, no conjecture generation, no agentic proving. Stated prior: **DEGREE**
(infra-resistance collapses to infrastructure-degree — the seventh confound) is the likeliest outcome.

## Environment resolution (why this can now run here)

The local toolchain is egress-blocked, but the user authorized the Aristotle environment as the
**runtime** (not the prover): Aristotle's built Mathlib v4.28.0 env executes a deterministic batch
script — `lake env lean` on each generated variant file at fixed heartbeat caps — and returns raw
logs. **The prover is the Lean elaborator replaying each theorem's ORIGINAL proof under the loosened
context, budget-capped: fixed, bounded, deterministic.** No ML/agentic proving anywhere in the
measurement. Precedent for runtime fidelity: the DumpDeps extraction (two independent jobs,
byte-identical output). Fidelity checks here: (i) two independent identical jobs, logs must agree
per-declaration; (ii) per-file canaries with known outcomes — C1 verbatim-copy must SURVIVE,
C2 type-error proof must BREAK, C3 bogus-name statement must be N/A. Canary failure ⇒ run VOID.

## Substrate

`Mathlib.Algebra.GroupWithZero.Basic` at v4.28.0 (78 theorem/lemma declarations; the generator's
parsed count is authoritative and reported). Variant file architecture = **prefix-verbatim**: file
text copied verbatim from line 1 up to theorem k (identical elaboration conditions, no import of the
original module ⇒ no self-contamination of simp calls), then the variant declarations, fresh-named,
**attributes stripped** on all variant copies (so a @[simp] variant cannot aid later variants).

## Move-list (named, finite; deviations from frozen draft marked)

Math axis:
- **M1** drop each inline explicit hypothesis binder `(h : P)`, one variant per hypothesis
  (theorem line edit; section context unchanged).
- **M2** ambient-class weaken one step on the fixed ladder `GroupWithZero→MonoidWithZero→
  MulZeroOneClass→MulZeroClass` (and `CancelMonoidWithZero→MonoidWithZero`), realized as a
  fresh-type-variable explicit-binder restatement (α-renamed) — DEVIATION: restatement is required
  because Lean auto-binds ambient section instances; expected-N/A cases tolerated and reported.
- **M3** drop `Nontrivial` where in scope (same restatement technique).

Infra axis (DEVIATION — concretized to context-scoped, prefix-safe moves):
- **I1** instance-indirection shadow: `instance (priority := 10000) : C M₀ := ‹C M₀›` inserted
  before the variant (statement unchanged; synthesis path perturbed, defeq-transparent).
- **I2** `set_option synthInstance.maxHeartbeats 1000 in` (synthesis time throttle).
- **I3** `set_option synthInstance.maxSize 16 in` (synthesis size throttle).
- I4 (coercion-path) DROPPED: no coercion axis in this corner — reported, not silently skipped.

Pairs (non-adaptive, pre-named): M1(first hypothesis)×I1 and M1(first hypothesis)×I2 for every
M1-eligible theorem.

## Adjudication (in-env, blind-proof-safe)

Each variant is emitted with a **sorry-twin** (same signature, `:= sorry`). Twin errors ⇒ **N/A**
(ill-formed statement — excluded, not noise). Twin ok + variant errors ⇒ **BREAK**. Both ok ⇒
**SURVIVE**. Error attribution by line ranges recorded at generation time.

## Budgets (DEVIATION: 200k/50k, not 200k/400k)

Two caps via `-DmaxHeartbeats=200000` (Lean default — original conditions) and `=50000` (tight).
Rationale: for replaying originally-passing proofs, the informative sensitivity direction is
tightening. Budget-sensitivity rail: report the fraction of (theorem, loosening) cells that flip
between caps; **> 10 % flips ⇒ prover-leak flag** on the whole lattice.

## Resistance (DEVIATION: fraction-survived, not minimal-depth — 3-move axes make depth degenerate)

- math-resistance(t) = fraction of applicable M-loosenings survived.
- infra-resistance(t) = fraction of I-loosenings survived.
- Break-pattern(t) = the bit-vector of which moves break t. Pairs reported as depth-2 context.

## Locked gates

- **STRUCTURED**: ≥ 3 distinct resistance patterns; no single pattern > 70 % of theorems; ≥ 3
  distinct moves each the breaker for ≥ 10 % of broken theorems. All-break-on-one ⇒ TRIVIAL;
  > 50 % of theorems break nowhere ⇒ DEGENERATE-FLAT.
- **INFRA-DISTINCT (decisive)**: `1 − R²(infra-resistance ~ log-indeg + log-outdeg +
  #instance-binders + math-resistance) ≥ 0.30`, infra-resistance non-degenerate (< 90 % identical
  values), and split-consistency (I1-derived vs {I2,I3}-derived residuals) ≥ 0.5.
  DEGREE = the R² is carried by the degree terms (stated prior). Mixed ⇒ AMBIGUOUS.
- Power caveat: n ≈ 78; SE(ρ) ≈ 0.11; borderline ⇒ AMBIGUOUS, never ALIVE.
- ALIVE = STRUCTURED ∧ INFRA-DISTINCT ⇒ recommend building the resistance-navigator next session.

## Rails
Runtime must not edit variants or fix errors (errors ARE the data); double-run + canaries or VOID;
one move-list, no tuning toward structure (recipes may be dropped for ill-formedness only, and every
drop is reported); degree-residual is the decisive number; measurement only.
